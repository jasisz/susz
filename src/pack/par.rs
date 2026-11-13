// Parsing on several workers: the file after its header line is cut into
// ranges at newlines; each worker parses its range on the assumption that
// the ids of the file are dense (as lean4export writes them), writing the
// columns at global ids into one shared allocation. The merge checks that
// assumption range by range (each range's first ids are where the ranges
// before ended, and everything a range named before its first definition
// lies below them); when it does not hold, or any worker failed, the file
// is parsed again on one worker, which gives the exact result or error.
// The merge then does what needs file order: owners seeded by
// declarations, names made canonical.

use super::lines::{Reader, PAD};
use super::pk::{rv, Pk, FLAG, MAIN, NONE};
use super::{cant, R};
use std::io::{Read, Seek, SeekFrom};
use std::os::unix::fs::FileExt;

struct SendPtr(*mut u8, *mut u32, *mut u32);
unsafe impl Send for SendPtr {}
unsafe impl Sync for SendPtr {}

fn parse_range(path: &str, from: u64, to: u64, pk: &mut Pk) -> R<()> {
    let f = std::fs::File::open(path).map_err(|e| cant!("cannot read {path}: {e}"))?;
    let chunk = 16usize << 20;
    let mut ch = chunk;
    let mut buf: Vec<u8> = vec![0; ch + PAD];
    let mut have = 0usize;
    let mut pos = from;
    let mut rd = Reader::new();
    rd.header_done = true;
    loop {
        let mut eof = false;
        while !eof && have < ch {
            let want = ((ch - have) as u64).min(to - pos) as usize;
            if want == 0 {
                eof = true;
                break;
            }
            let n = f
                .read_at(&mut buf[have..have + want], pos)
                .map_err(|e| cant!("cannot read {path}: {e}"))?;
            if n == 0 {
                eof = true;
            } else {
                have += n;
                pos += n as u64;
            }
        }
        let lim;
        if eof {
            if have > 0 && buf[have - 1] != b'\n' {
                buf[have] = b'\n';
                have += 1;
            }
            lim = have;
        } else {
            match buf[..have].iter().rposition(|&c| c == b'\n') {
                Some(i) => lim = i + 1,
                None => {
                    ch *= 2;
                    buf.resize(ch + PAD, 0);
                    continue;
                }
            }
        }
        rd.lines(pk, &buf, 0, lim)?;
        buf.copy_within(lim..have, 0);
        have -= lim;
        if eof && have == 0 {
            break;
        }
    }
    pk.finish_range();
    Ok(())
}

// Where the line containing byte at starts the next one: just after the
// first newline at or after at (or the end of the file).
fn after_newline(f: &std::fs::File, at: u64, size: u64) -> R<u64> {
    let mut pos = at;
    let mut b = vec![0u8; 1 << 16];
    while pos < size {
        let n = f
            .read_at(&mut b, pos)
            .map_err(|e| cant!("cannot read: {e}"))?;
        if n == 0 {
            break;
        }
        if let Some(i) = b[..n].iter().position(|&c| c == b'\n') {
            return Ok(pos + i as u64 + 1);
        }
        pos += n as u64;
    }
    Ok(size)
}

// Ok(None): the parallel parse does not apply; parse on one worker.
pub fn parse_parallel(path: &str, threads: usize) -> R<Option<Pk>> {
    let mut f = std::fs::File::open(path).map_err(|e| cant!("cannot read {path}: {e}"))?;
    let size = f
        .metadata()
        .map_err(|e| cant!("cannot read {path}: {e}"))?
        .len();
    // the header line
    let mut head = vec![0u8; (1usize << 20).min(size as usize) + PAD + 1];
    let hn = (1u64 << 20).min(size) as usize;
    f.read_exact(&mut head[..hn])
        .map_err(|e| cant!("cannot read {path}: {e}"))?;
    let Some(nl) = head[..hn].iter().position(|&c| c == b'\n') else {
        return Ok(None);
    };
    let mut pk = Pk::new(0);
    let mut rd = Reader::new();
    rd.lines(&mut pk, &head, 0, nl + 1)?;
    let start = nl as u64 + 1;
    f.seek(SeekFrom::Start(0)).ok();
    // ranges
    let mut cuts = vec![start];
    for k in 1..threads as u64 {
        let at = start + (size - start) * k / threads as u64;
        let c = after_newline(&f, at.max(*cuts.last().unwrap()), size)?;
        cuts.push(c.max(*cuts.last().unwrap()));
    }
    cuts.push(size);
    // one allocation of the k, a and b columns for all
    let cap = size as usize / 16 + 16;
    let mut ck: Vec<u8> = Vec::with_capacity(cap);
    let mut ca: Vec<u32> = Vec::with_capacity(cap);
    let mut cb: Vec<u32> = Vec::with_capacity(cap);
    let colp = SendPtr(ck.as_mut_ptr(), ca.as_mut_ptr(), cb.as_mut_ptr());
    let colp = &colp;
    let results: Vec<R<Pk>> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..threads)
            .map(|k| {
                let (from, to) = (cuts[k], cuts[k + 1]);
                sc.spawn(move || {
                    let mut w = Pk::new_worker((to - from) as usize);
                    w.kp = colp.0;
                    w.ap = colp.1;
                    w.bp = colp.2;
                    w.colcap = cap as u64;
                    parse_range(path, from, to, &mut w).map(|_| w)
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    // the dense ids, range by range
    let (mut nn, mut nl_, mut ne) = (1u64, 1u64, 0u64);
    let mut ws: Vec<Pk> = Vec::with_capacity(threads);
    for r in results {
        let Ok(w) = r else { return Ok(None) };
        if w.er.map.is_some() || w.nr.map.is_some() || w.lr.map.is_some() {
            return Ok(None);
        }
        if w.er.pend.get() > ne || w.nr.pend.get() > nn || w.lr.pend.get() > nl_ {
            return Ok(None);
        }
        if !w.er.floating {
            if w.er.first != ne {
                return Ok(None);
            }
            ne = w.exprs as u64;
        }
        if !w.nr.floating {
            if w.nr.first != nn {
                return Ok(None);
            }
            nn = w.names as u64;
        }
        if !w.lr.floating {
            if w.lr.first != nl_ {
                return Ok(None);
            }
            nl_ = w.levels as u64;
        }
        ws.push(w);
    }
    // merge
    let n = ne as usize;
    pk.names = nn as u32;
    pk.levels = nl_ as u32;
    pk.exprs = ne as u32;
    let total_stream: usize = ws.iter().map(|w| w.stream.len()).sum();
    let mut stream = Vec::with_capacity(total_stream);
    let mut dmeta: Vec<u32> = Vec::new();
    unsafe {
        ck.set_len(n);
        ca.set_len(n);
        cb.set_len(n);
    }
    pk.cols.k = ck;
    pk.cols.a = ca;
    pk.cols.b = cb;
    pk.cols.names = Vec::with_capacity(ws.iter().map(|w| w.cols.names.len()).sum());
    pk.cols.x = Vec::with_capacity(ws.iter().map(|w| w.cols.x.len()).sum());
    pk.cols.loffs = Vec::with_capacity(ws.iter().map(|w| w.cols.loffs.len()).sum());
    let mut decls = 0u32;
    for w in ws.iter_mut() {
        stream.extend_from_slice(&w.stream);
        super::give_back(std::mem::take(&mut w.stream));
        dmeta.extend_from_slice(&w.dmeta);
        let c = std::mem::take(&mut w.cols);
        let base = pk.cols.x.len() as u64;
        pk.cols.names.extend_from_slice(&c.names);
        pk.cols.x.extend_from_slice(&c.x);
        pk.cols.loffs.extend(c.loffs.iter().map(|o| o + base));
        c.give_back();
        decls += w.decls;
    }
    drop(ws);
    pk.stream = stream;
    pk.decls = decls;
    // owners seeded and names made canonical, in file order
    let mut owner = vec![NONE; n];
    let mut canon: Vec<u32> = Vec::with_capacity(nn as usize);
    canon.push(0);
    let s = &pk.stream;
    let mut p = 0usize;
    let mut di = 0u32;
    while p < s.len() {
        let tag = s[p];
        p += 1;
        match tag {
            1 => {
                let pre = rv(s, &mut p) as usize;
                let l = rv(s, &mut p) as usize;
                let c = pk.cn.str_id(s, canon[pre], p as u64, l as u32);
                canon.push(c);
                p += l;
            }
            2 => {
                let pre = rv(s, &mut p) as usize;
                let k = rv(s, &mut p);
                let c = pk.cn.num_id(canon[pre], k);
                canon.push(c);
            }
            3 | 6 => {
                rv(s, &mut p);
            }
            4 | 5 => {
                rv(s, &mut p);
                rv(s, &mut p);
            }
            20 => {
                rv(s, &mut p);
            }
            18 => {
                p += 1;
                loop {
                    let t = s[p];
                    p += 1;
                    match t {
                        0 => {
                            let l = rv(s, &mut p) as usize;
                            p += l;
                        }
                        1 => {
                            let e = rv(s, &mut p) as usize;
                            owner[e] = MAIN | (owner[e] & FLAG);
                        }
                        2 => {
                            let e = rv(s, &mut p) as usize;
                            let x = owner[e];
                            let w = x & !FLAG;
                            let nw = if w == NONE || w == di { di } else { MAIN };
                            owner[e] = nw | (x & FLAG);
                        }
                        _ => break,
                    }
                }
                di += 1;
            }
            t => return Err(cant!("internal: bad stream tag {t}")),
        }
    }
    pk.owner = owner;
    pk.canon = canon;
    pk.dmeta = dmeta;
    Ok(Some(pk))
}
