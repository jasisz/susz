// Reading the ndjson file: chunks, lines, the canonical forms lean4export
// writes parsed by position, any other line through the JSON parser.

use super::json::{self, J};
use super::pk::{Pk, MAX_EXPRS};
use super::{cant, R};
use std::io::Read;

pub const PAD: usize = 128;

#[inline(always)]
fn ld8(b: &[u8], p: usize) -> u64 {
    unsafe { (b.as_ptr().add(p) as *const u64).read_unaligned() }
}

#[inline(always)]
const fn word(s: &[u8], from: usize, n: usize) -> u64 {
    let mut v = 0u64;
    let mut i = 0;
    while i < n && i < 8 {
        v |= (s[from + i] as u64) << (8 * i);
        i += 1;
    }
    v
}

#[inline(always)]
fn lit<const N: usize>(b: &[u8], p: usize, s: &[u8; N]) -> bool {
    if N <= 8 {
        let mask = if N == 8 { !0u64 } else { (1u64 << (8 * N)) - 1 };
        (ld8(b, p) & mask) == word(s, 0, N)
    } else if N <= 16 {
        ld8(b, p) == word(s, 0, 8) && ld8(b, p + N - 8) == word(s, N - 8, 8)
    } else if N <= 24 {
        ld8(b, p) == word(s, 0, 8)
            && ld8(b, p + 8) == word(s, 8, 8)
            && ld8(b, p + N - 8) == word(s, N - 8, 8)
    } else {
        unsafe { *(b.as_ptr().add(p) as *const [u8; N]) == *s }
    }
}

#[inline(always)]
fn at(b: &[u8], p: usize) -> u8 {
    unsafe { *b.get_unchecked(p) }
}

const POW10: [u64; 9] = [
    1, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000,
];

// Up to 8 digits at p: (value, count); count 0 when b[p] is not a digit.
#[inline(always)]
fn digits8(b: &[u8], p: usize) -> (u64, usize) {
    let w = ld8(b, p);
    let d = w ^ 0x3030_3030_3030_3030;
    let nd = (d.wrapping_add(0x7676_7676_7676_7676) | d) & 0x8080_8080_8080_8080;
    let len = if nd == 0 {
        8
    } else {
        (nd.trailing_zeros() / 8) as usize
    };
    if len == 0 {
        return (0, 0);
    }
    let mut x = d << (64 - 8 * len as u32);
    x = (x.wrapping_mul(10) + (x >> 8)) & 0x00FF_00FF_00FF_00FF;
    x = (x.wrapping_mul(100) + (x >> 16)) & 0x0000_FFFF_0000_FFFF;
    x = (x.wrapping_mul(10000) + (x >> 32)) & 0xFFFF_FFFF;
    (x, len)
}

// A non-negative integer at p: (value, position after), None when there is
// no digit or it is longer than 19 digits (left to the slow path).
#[inline(always)]
fn num(b: &[u8], p: usize) -> Option<(u64, usize)> {
    let (v, n) = digits8(b, p);
    if n == 0 {
        return None;
    }
    if n < 8 {
        return Some((v, p + n));
    }
    let d8 = at(b, p + 8).wrapping_sub(b'0');
    if d8 > 9 {
        return Some((v, p + 8));
    }
    let d9 = at(b, p + 9).wrapping_sub(b'0');
    if d9 > 9 {
        return Some((v * 10 + d8 as u64, p + 9));
    }
    let (w, m) = digits8(b, p + 8);
    if m < 8 {
        return Some((v * POW10[m] + w, p + 8 + m));
    }
    num_long(b, p + 16, v * 100_000_000 + w)
}

#[inline(never)]
fn num_long(b: &[u8], mut p: usize, mut v: u64) -> Option<(u64, usize)> {
    let mut total = 16;
    loop {
        let (w, n) = digits8(b, p);
        total += n;
        if total > 19 {
            return None;
        }
        v = v * POW10[n] + w;
        p += n;
        if n < 8 {
            return Some((v, p));
        }
    }
}

// A list of integers at p (just after '['), up to and past ']'.
#[inline(always)]
fn nums(b: &[u8], mut p: usize, out: &mut Vec<u64>) -> Option<usize> {
    out.clear();
    if at(b, p) == b']' {
        return Some(p + 1);
    }
    loop {
        let (v, q) = num(b, p)?;
        out.push(v);
        match at(b, q) {
            b',' => p = q + 1,
            b']' => return Some(q + 1),
            _ => return None,
        }
    }
}

// The body of a string at p (just after its quote) when it has no escape:
// (start, end) with end at the closing quote; None at a backslash or newline.
// Eight bytes at a time: b has PAD readable bytes past the line's newline.
#[inline(always)]
fn plain_str(b: &[u8], p: usize) -> Option<(usize, usize)> {
    const ONES: u64 = 0x0101_0101_0101_0101;
    const HIGH: u64 = 0x8080_8080_8080_8080;
    // high bit of each byte that is zero (exact up to the first one)
    let zero = |x: u64| x.wrapping_sub(ONES) & !x & HIGH;
    let mut q = p;
    let mut hi = 0u64;
    loop {
        let w = ld8(b, q);
        let m = zero(w ^ (ONES * b'"' as u64))
            | zero(w ^ (ONES * b'\\' as u64))
            | zero(w ^ (ONES * b'\n' as u64));
        if m != 0 {
            let k = m.trailing_zeros() as usize / 8;
            hi |= w & ((1u64 << (8 * k)) - 1);
            q += k;
            break;
        }
        hi |= w;
        q += 8;
    }
    if at(b, q) != b'"' {
        return None;
    }
    if hi & HIGH != 0 && std::str::from_utf8(&b[p..q]).is_err() {
        return None;
    }
    Some((p, q))
}

#[inline(always)]
fn binder(b: &[u8], p: usize) -> Option<(u32, usize)> {
    // p just after `"binderInfo":"`
    if lit(b, p, b"default\"") {
        Some((0, p + 8))
    } else if lit(b, p, b"implicit\"") {
        Some((1, p + 9))
    } else if lit(b, p, b"instImplicit\"") {
        Some((3, p + 13))
    } else if lit(b, p, b"strictImplicit\"") {
        Some((2, p + 15))
    } else {
        None
    }
}

// Application lines {"app":{"arg":A,"fn":F},"ie":I} from p while I is the
// next id e: (where it stopped, the next id).
#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn app_run(
    b: &[u8],
    mut p: usize,
    lim: usize,
    mut e: u64,
    ecap: u64,
    kp: *mut u8,
    ap: *mut u32,
    bp: *mut u32,
) -> (usize, u64) {
    const APP0: u64 = word(b"{\"app\":{", 0, 8);
    const APP1: u64 = word(b":{\"arg\":", 0, 8);
    while p < lim && e < ecap {
        if ld8(b, p) != APP0 || ld8(b, p + 6) != APP1 {
            break;
        }
        let Some((a, q1)) = num(b, p + 14) else { break };
        if !lit(b, q1, b",\"fn\":") {
            break;
        }
        let Some((f, q2)) = num(b, q1 + 6) else { break };
        if !lit(b, q2, b"},\"ie\":") {
            break;
        }
        let Some((ie, q3)) = num(b, q2 + 7) else {
            break;
        };
        if !lit(b, q3, b"}\n") {
            break;
        }
        if ie != e || f >= e || a >= e {
            break;
        }
        unsafe {
            kp.add(e as usize).write(1);
            ap.add(e as usize).write(f as u32);
            bp.add(e as usize).write(a as u32);
        }
        e += 1;
        p = q3 + 2;
    }
    (p, e)
}

// Runs of application, lambda and pi lines in their canonical forms while
// ids are dense, packed straight into the columns with every check of
// pk.app / pk.bind. Returns where it stopped (a line it does not take, left
// to the general path, which also reports any error) and how many lines it
// took.
#[inline(never)]
pub fn col_run(pk: &mut Pk, b: &[u8], mut p: usize, lim: usize) -> (usize, u64) {
    if pk.er.map.is_some() || pk.nr.map.is_some() || pk.er.floating {
        return (p, 0);
    }
    let nfloat = pk.nr.floating;
    let names = if nfloat { u64::MAX } else { pk.names as u64 };
    let mut maxn = 0u64;
    let e0 = pk.exprs as u64;
    let mut e = e0;
    let ecap = pk.colcap.min(MAX_EXPRS as u64);
    let (kp, ap, bp) = (pk.kp, pk.ap, pk.bp);
    // a line takes at least 16 bytes
    pk.cols.names.reserve((lim - p) / 16 + 1);
    let mut np = unsafe { pk.cols.names.as_mut_ptr().add(pk.cols.names.len()) };
    const APP0: u64 = word(b"{\"app\":{", 0, 8);
    const FA0: u64 = word(b"{\"forall", 0, 8);
    const IE: u64 = word(b"{\"ie\":\0\0", 0, 8);
    loop {
        if p >= lim || e >= ecap {
            break;
        }
        let w = ld8(b, p);
        let (k, x, y, i, q);
        if w == APP0 {
            let (q, ne) = app_run(b, p, lim, e, ecap, kp, ap, bp);
            if ne == e {
                break;
            }
            e = ne;
            p = q;
            continue;
        } else if w == FA0 {
            if !lit(b, p + 8, b"E\":{\"binderInfo\":\"") {
                break;
            }
            let Some((bi, q1)) = binder(b, p + 26) else {
                break;
            };
            let Some((body, n, t, q2)) = bnt(b, q1) else {
                break;
            };
            if !lit(b, q2, b",\"ie\":") {
                break;
            }
            let Some((ie, q3)) = num(b, q2 + 6) else {
                break;
            };
            if !lit(b, q3, b"}\n") {
                break;
            }
            if n >= names || n >= 1 << 28 {
                break;
            }
            maxn = maxn.max(n + 1);
            k = ((n as u32) << 4) | (6 + bi);
            x = t;
            y = body;
            i = ie;
            q = q3 + 2;
        } else if w & 0xFFFF_FFFF_FFFF == IE {
            let Some((ie, q1)) = num(b, p + 6) else { break };
            if !lit(b, q1, b",\"lam\":{\"binderInfo\":\"") {
                break;
            }
            let Some((bi, q2)) = binder(b, q1 + 22) else {
                break;
            };
            let Some((body, n, t, q3)) = bnt(b, q2) else {
                break;
            };
            if !lit(b, q3, b"}\n") {
                break;
            }
            if n >= names || n >= 1 << 28 {
                break;
            }
            maxn = maxn.max(n + 1);
            k = ((n as u32) << 4) | (2 + bi);
            x = t;
            y = body;
            i = ie;
            q = q3 + 2;
        } else {
            break;
        }
        if i != e || x >= e || y >= e {
            break;
        }
        unsafe {
            kp.add(e as usize).write((k & 15) as u8);
            ap.add(e as usize).write(x as u32);
            bp.add(e as usize).write(y as u32);
            if k & 15 >= 2 {
                np.write(k >> 4);
                np = np.add(1);
            }
        }
        e += 1;
        p = q;
    }
    let cnt = e - e0;
    unsafe {
        let l = np.offset_from(pk.cols.names.as_ptr()) as usize;
        pk.cols.names.set_len(l);
    }
    if nfloat && maxn > 0 {
        pk.nr.note(maxn - 1);
    }
    pk.exprs = e as u32;
    pk.er.below = e;
    pk.run += cnt as u32;
    (p, cnt)
}

// "body":B,"name":N,"type":T} after the binder annotation
#[inline(always)]
fn bnt(b: &[u8], q: usize) -> Option<(u64, u64, u64, usize)> {
    if !lit(b, q, b",\"body\":") {
        return None;
    }
    let (body, q) = num(b, q + 8)?;
    if !lit(b, q, b",\"name\":") {
        return None;
    }
    let (n, q) = num(b, q + 8)?;
    if !lit(b, q, b",\"type\":") {
        return None;
    }
    let (t, q) = num(b, q + 8)?;
    if at(b, q) != b'}' {
        return None;
    }
    Some((body, n, t, q + 1))
}

pub struct Reader {
    pub line: u64,
    tmp1: Vec<u64>,
    tmp2: Vec<u64>,
    pub header_done: bool,
}

impl Reader {
    pub fn new() -> Reader {
        Reader {
            line: 0,
            tmp1: Vec::new(),
            tmp2: Vec::new(),
            header_done: false,
        }
    }

    // The lines of b[..lim], every one ended by a newline; b has PAD readable
    // bytes past lim.
    pub fn lines(&mut self, pk: &mut Pk, b: &[u8], start: usize, lim: usize) -> R<()> {
        let mut p = start;
        if !self.header_done && lim > p {
            let nl = memnl(b, p, lim);
            self.line += 1;
            self.header(pk, &b[p..nl]).map_err(|e| e.at("line 1"))?;
            self.header_done = true;
            p = nl + 1;
        }
        while p < lim {
            // the lines col_run takes
            let w = ld8(b, p);
            if w == u64::from_le_bytes(*b"{\"app\":{")
                || w == u64::from_le_bytes(*b"{\"forall")
                || w & 0xFFFF_FFFF_FFFF == u64::from_le_bytes(*b"{\"ie\":\0\0")
            {
                let (q, cnt) = col_run(pk, b, p, lim);
                self.line += cnt;
                p = q;
                if p >= lim {
                    break;
                }
            }
            self.line += 1;
            match self.fast(pk, b, p) {
                Ok(Some(q)) => p = q,
                Ok(None) => {
                    let nl = memnl(b, p, lim);
                    let line = self.line;
                    self.slow(pk, &b[p..nl])
                        .map_err(|e| e.at(format_args!("line {line}")))?;
                    p = nl + 1;
                }
                Err(e) => return Err(e.at(format_args!("line {}", self.line))),
            }
        }
        Ok(())
    }

    // {"meta":M}: M is kept byte for byte (SOURCE). The object must be
    // written exactly so, without spaces around the one key, to be kept.
    fn header(&mut self, pk: &mut Pk, l: &[u8]) -> R<()> {
        std::str::from_utf8(l).map_err(|e| format!("not UTF-8: {e}"))?;
        let j = json::parse(l)?;
        let J::Obj(fs) = j else {
            return Err("the header is not an object".into());
        };
        let meta = json::obj(&fs, "meta")?;
        json::exact(&fs, &["meta"])?;
        let v = json::text(json::obj(meta, "format")?, "version")?;
        if !v.starts_with(b"3.1.") {
            return Err(cant!(
                "format version {} is not supported",
                String::from_utf8_lossy(v)
            ));
        }
        if !(l.starts_with(b"{\"meta\":") && l.ends_with(b"}")) {
            return Err(cant!("the header is not in the form {{\"meta\":...}}"));
        }
        pk.meta = l[8..l.len() - 1].to_vec();
        Ok(())
    }

    #[inline(never)]
    fn slow(&mut self, pk: &mut Pk, l: &[u8]) -> R<()> {
        if l.is_empty() {
            return Ok(());
        }
        std::str::from_utf8(l).map_err(|e| format!("not UTF-8: {e}"))?;
        match json::parse(l)? {
            J::Obj(fs) => pk.obj(&fs),
            _ => Err("the line is not an object".into()),
        }
    }

    // A line in a canonical form: Some(position after its newline); None
    // when it is in no form read here.
    #[inline(always)]
    fn fast(&mut self, pk: &mut Pk, b: &[u8], p: usize) -> R<Option<usize>> {
        let w = ld8(b, p);
        // {"app":{"arg":A,"fn":F},"ie":I}
        if w == u64::from_le_bytes(*b"{\"app\":{") {
            if !lit(b, p + 8, b"\"arg\":") {
                return Ok(None);
            }
            let Some((a, q)) = num(b, p + 14) else {
                return Ok(None);
            };
            if !lit(b, q, b",\"fn\":") {
                return Ok(None);
            }
            let Some((f, q)) = num(b, q + 6) else {
                return Ok(None);
            };
            if !lit(b, q, b"},\"ie\":") {
                return Ok(None);
            }
            let Some((i, q)) = num(b, q + 7) else {
                return Ok(None);
            };
            if !lit(b, q, b"}\n") {
                return Ok(None);
            }
            pk.app(i, f, a)?;
            return Ok(Some(q + 2));
        }
        let w6 = w & 0xFFFF_FFFF_FFFF;
        if w6 == u64::from_le_bytes(*b"{\"ie\":\0\0") {
            let Some((i, q)) = num(b, p + 6) else {
                return Ok(None);
            };
            return self.after_ie(pk, b, i, q);
        }
        if w == u64::from_le_bytes(*b"{\"forall") {
            // {"forallE":{"binderInfo":"X","body":B,"name":N,"type":T},"ie":I}
            if !lit(b, p + 8, b"E\":{\"binderInfo\":\"") {
                return Ok(None);
            }
            let Some((bi, q)) = binder(b, p + 26) else {
                return Ok(None);
            };
            let Some((body, n, t, q)) = self.bnt(b, q) else {
                return Ok(None);
            };
            if !lit(b, q, b",\"ie\":") {
                return Ok(None);
            }
            let Some((i, q)) = num(b, q + 6) else {
                return Ok(None);
            };
            if !lit(b, q, b"}\n") {
                return Ok(None);
            }
            pk.bind(i, false, bi, n, t, body)?;
            return Ok(Some(q + 2));
        }
        if w6 == u64::from_le_bytes(*b"{\"in\":\0\0") {
            let Some((i, q)) = num(b, p + 6) else {
                return Ok(None);
            };
            if lit(b, q, b",\"str\":{\"pre\":") {
                let Some((pre, q)) = num(b, q + 14) else {
                    return Ok(None);
                };
                if !lit(b, q, b",\"str\":\"") {
                    return Ok(None);
                }
                let Some((s, e)) = plain_str(b, q + 8) else {
                    return Ok(None);
                };
                if !lit(b, e, b"\"}}\n") {
                    return Ok(None);
                }
                pk.name_str(i, pre, &b[s..e])?;
                return Ok(Some(e + 4));
            }
            if lit(b, q, b",\"num\":{\"i\":") {
                let Some((k, q)) = num(b, q + 12) else {
                    return Ok(None);
                };
                if !lit(b, q, b",\"pre\":") {
                    return Ok(None);
                }
                let Some((pre, q)) = num(b, q + 7) else {
                    return Ok(None);
                };
                if !lit(b, q, b"}}\n") {
                    return Ok(None);
                }
                pk.name_num(i, pre, k)?;
                return Ok(Some(q + 3));
            }
            return Ok(None);
        }
        if w == u64::from_le_bytes(*b"{\"const\"") {
            // {"const":{"name":N,"us":[..]},"ie":I}
            if !lit(b, p + 8, b":{\"name\":") {
                return Ok(None);
            }
            let Some((n, q)) = num(b, p + 17) else {
                return Ok(None);
            };
            if !lit(b, q, b",\"us\":[") {
                return Ok(None);
            }
            let mut us = std::mem::take(&mut self.tmp1);
            let r = nums(b, q + 7, &mut us);
            let out = (|| {
                let Some(q) = r else { return Ok(None) };
                if !lit(b, q, b"},\"ie\":") {
                    return Ok(None);
                }
                let Some((i, q)) = num(b, q + 7) else {
                    return Ok(None);
                };
                if !lit(b, q, b"}\n") {
                    return Ok(None);
                }
                pk.cnst(i, n, &us)?;
                Ok(Some(q + 2))
            })();
            self.tmp1 = us;
            return out;
        }
        if w == u64::from_le_bytes(*b"{\"thm\":{") {
            return self.thm(pk, b, p);
        }
        if w == u64::from_le_bytes(*b"{\"def\":{") {
            return self.def(pk, b, p);
        }
        if w6 == u64::from_le_bytes(*b"{\"il\":\0\0") {
            let Some((i, q)) = num(b, p + 6) else {
                return Ok(None);
            };
            if lit(b, q, b",\"succ\":") {
                let Some((a, q)) = num(b, q + 8) else {
                    return Ok(None);
                };
                if !lit(b, q, b"}\n") {
                    return Ok(None);
                }
                pk.lr.fresh(i, "level")?;
                pk.succ(i, a)?;
                return Ok(Some(q + 2));
            }
            if lit(b, q, b",\"param\":") {
                let Some((a, q)) = num(b, q + 9) else {
                    return Ok(None);
                };
                if !lit(b, q, b"}\n") {
                    return Ok(None);
                }
                pk.lr.fresh(i, "level")?;
                pk.param(i, a)?;
                return Ok(Some(q + 2));
            }
            let (max, q) = if lit(b, q, b",\"max\":[") {
                (true, q + 8)
            } else if lit(b, q, b",\"imax\":[") {
                (false, q + 9)
            } else {
                return Ok(None);
            };
            let Some((x, q)) = num(b, q) else {
                return Ok(None);
            };
            if at(b, q) != b',' {
                return Ok(None);
            }
            let Some((y, q)) = num(b, q + 1) else {
                return Ok(None);
            };
            if !lit(b, q, b"]}\n") {
                return Ok(None);
            }
            pk.lr.fresh(i, "level")?;
            pk.pair(i, x, y, max)?;
            return Ok(Some(q + 3));
        }
        if w == u64::from_le_bytes(*b"{\"bvar\":") {
            let Some((k, q)) = num(b, p + 8) else {
                return Ok(None);
            };
            if !lit(b, q, b",\"ie\":") {
                return Ok(None);
            }
            let Some((i, q)) = num(b, q + 6) else {
                return Ok(None);
            };
            if !lit(b, q, b"}\n") {
                return Ok(None);
            }
            pk.bvar(i, k)?;
            return Ok(Some(q + 2));
        }
        if at(b, p) == b'\n' {
            return Ok(Some(p + 1));
        }
        Ok(None)
    }

    // "body":B,"name":N,"type":T} after the binder annotation
    #[inline(always)]
    fn bnt(&self, b: &[u8], q: usize) -> Option<(u64, u64, u64, usize)> {
        if !lit(b, q, b",\"body\":") {
            return None;
        }
        let (body, q) = num(b, q + 8)?;
        if !lit(b, q, b",\"name\":") {
            return None;
        }
        let (n, q) = num(b, q + 8)?;
        if !lit(b, q, b",\"type\":") {
            return None;
        }
        let (t, q) = num(b, q + 8)?;
        if at(b, q) != b'}' {
            return None;
        }
        Some((body, n, t, q + 1))
    }

    #[inline(always)]
    fn after_ie(&mut self, pk: &mut Pk, b: &[u8], i: u64, q: usize) -> R<Option<usize>> {
        // {"ie":I,"lam":{"binderInfo":"X","body":B,"name":N,"type":T}}
        if lit(b, q, b",\"lam\":{\"binderInfo\":\"") {
            let Some((bi, q)) = binder(b, q + 22) else {
                return Ok(None);
            };
            let Some((body, n, t, q)) = self.bnt(b, q) else {
                return Ok(None);
            };
            if !lit(b, q, b"}\n") {
                return Ok(None);
            }
            pk.bind(i, true, bi, n, t, body)?;
            return Ok(Some(q + 2));
        }
        if lit(b, q, b",\"letE\":{\"body\":") {
            // {"ie":I,"letE":{"body":B,"name":N,"nondep":false,"type":T,"value":V}}
            let Some((body, q)) = num(b, q + 16) else {
                return Ok(None);
            };
            if !lit(b, q, b",\"name\":") {
                return Ok(None);
            }
            let Some((n, q)) = num(b, q + 8) else {
                return Ok(None);
            };
            let q = if lit(b, q, b",\"nondep\":false,\"type\":") {
                q + 23
            } else if lit(b, q, b",\"nondep\":true,\"type\":") {
                q + 22
            } else {
                return Ok(None);
            };
            let Some((t, q)) = num(b, q) else {
                return Ok(None);
            };
            if !lit(b, q, b",\"value\":") {
                return Ok(None);
            }
            let Some((v, q)) = num(b, q + 9) else {
                return Ok(None);
            };
            if !lit(b, q, b"}}\n") {
                return Ok(None);
            }
            pk.let_e(i, n, t, v, body)?;
            return Ok(Some(q + 3));
        }
        if lit(b, q, b",\"proj\":{\"idx\":") {
            // {"ie":I,"proj":{"idx":K,"struct":S,"typeName":N}}
            let Some((k, q)) = num(b, q + 15) else {
                return Ok(None);
            };
            if !lit(b, q, b",\"struct\":") {
                return Ok(None);
            }
            let Some((s, q)) = num(b, q + 10) else {
                return Ok(None);
            };
            if !lit(b, q, b",\"typeName\":") {
                return Ok(None);
            }
            let Some((n, q)) = num(b, q + 12) else {
                return Ok(None);
            };
            if !lit(b, q, b"}}\n") {
                return Ok(None);
            }
            pk.proj(i, n, k, s)?;
            return Ok(Some(q + 3));
        }
        if lit(b, q, b",\"sort\":") {
            let Some((l, q)) = num(b, q + 8) else {
                return Ok(None);
            };
            if !lit(b, q, b"}\n") {
                return Ok(None);
            }
            pk.sort(i, l)?;
            return Ok(Some(q + 2));
        }
        if lit(b, q, b",\"strVal\":\"") {
            let Some((s, e)) = plain_str(b, q + 11) else {
                return Ok(None);
            };
            if !lit(b, e, b"\"}\n") {
                return Ok(None);
            }
            pk.strv(i, &b[s..e])?;
            return Ok(Some(e + 3));
        }
        if lit(b, q, b",\"natVal\":\"") {
            let Some((s, e)) = plain_str(b, q + 11) else {
                return Ok(None);
            };
            if !lit(b, e, b"\"}\n") {
                return Ok(None);
            }
            pk.nat(i, &b[s..e])?;
            return Ok(Some(e + 3));
        }
        Ok(None)
    }

    // {"thm":{"all":[..],"levelParams":[..],"name":N,"type":T,"value":V}}
    fn thm(&mut self, pk: &mut Pk, b: &[u8], p: usize) -> R<Option<usize>> {
        if !lit(b, p + 8, b"\"all\":[") {
            return Ok(None);
        }
        let mut all = std::mem::take(&mut self.tmp1);
        let mut ps = std::mem::take(&mut self.tmp2);
        let r = (|| {
            let Some(q) = nums(b, p + 15, &mut all) else {
                return Ok(None);
            };
            if !lit(b, q, b",\"levelParams\":[") {
                return Ok(None);
            }
            let Some(q) = nums(b, q + 16, &mut ps) else {
                return Ok(None);
            };
            if !lit(b, q, b",\"name\":") {
                return Ok(None);
            }
            let Some((n, q)) = num(b, q + 8) else {
                return Ok(None);
            };
            if !lit(b, q, b",\"type\":") {
                return Ok(None);
            }
            let Some((t, q)) = num(b, q + 8) else {
                return Ok(None);
            };
            if !lit(b, q, b",\"value\":") {
                return Ok(None);
            }
            let Some((v, q)) = num(b, q + 9) else {
                return Ok(None);
            };
            if !lit(b, q, b"}}\n") {
                return Ok(None);
            }
            pk.thm(n, &ps, t, v, &all)?;
            Ok(Some(q + 3))
        })();
        self.tmp1 = all;
        self.tmp2 = ps;
        r
    }

    // {"def":{"all":[..],"hints":H,"levelParams":[..],"name":N,"safety":"S","type":T,"value":V}}
    fn def(&mut self, pk: &mut Pk, b: &[u8], p: usize) -> R<Option<usize>> {
        if !lit(b, p + 8, b"\"all\":[") {
            return Ok(None);
        }
        let mut all = std::mem::take(&mut self.tmp1);
        let mut ps = std::mem::take(&mut self.tmp2);
        let r = (|| {
            let Some(q) = nums(b, p + 15, &mut all) else {
                return Ok(None);
            };
            if !lit(b, q, b",\"hints\":") {
                return Ok(None);
            }
            let q = q + 9;
            let (hk, h, q) = if lit(b, q, b"\"abbrev\"") {
                (1u8, 0u64, q + 8)
            } else if lit(b, q, b"\"opaque\"") {
                (0, 0, q + 8)
            } else if lit(b, q, b"{\"regular\":") {
                let Some((h, q)) = num(b, q + 11) else {
                    return Ok(None);
                };
                if at(b, q) != b'}' {
                    return Ok(None);
                }
                (2, h, q + 1)
            } else {
                return Ok(None);
            };
            if !lit(b, q, b",\"levelParams\":[") {
                return Ok(None);
            }
            let Some(q) = nums(b, q + 16, &mut ps) else {
                return Ok(None);
            };
            if !lit(b, q, b",\"name\":") {
                return Ok(None);
            }
            let Some((n, q)) = num(b, q + 8) else {
                return Ok(None);
            };
            let (s, q) = if lit(b, q, b",\"safety\":\"safe\"") {
                (0u8, q + 16)
            } else if lit(b, q, b",\"safety\":\"unsafe\"") {
                (1, q + 18)
            } else if lit(b, q, b",\"safety\":\"partial\"") {
                (2, q + 19)
            } else {
                return Ok(None);
            };
            if !lit(b, q, b",\"type\":") {
                return Ok(None);
            }
            let Some((t, q)) = num(b, q + 8) else {
                return Ok(None);
            };
            if !lit(b, q, b",\"value\":") {
                return Ok(None);
            }
            let Some((v, q)) = num(b, q + 9) else {
                return Ok(None);
            };
            if !lit(b, q, b"}}\n") {
                return Ok(None);
            }
            pk.defn(n, &ps, t, v, hk, h, s, &all)?;
            Ok(Some(q + 3))
        })();
        self.tmp1 = all;
        self.tmp2 = ps;
        r
    }
}

pub fn memnl(b: &[u8], p: usize, lim: usize) -> usize {
    match b[p..lim].iter().position(|&c| c == b'\n') {
        Some(i) => p + i,
        None => lim,
    }
}

// Reads the whole file in chunks, packing every line.
pub fn read_file(path: &str, pk: &mut Pk, chunk: usize) -> R<()> {
    let mut f = std::fs::File::open(path).map_err(|e| cant!("cannot read {path}: {e}"))?;
    let mut ch = chunk;
    let mut buf: Vec<u8> = vec![0; ch + PAD];
    let mut have = 0usize;
    let mut eof = false;
    let mut rd = Reader::new();
    loop {
        while !eof && have < ch {
            let n = f
                .read(&mut buf[have..ch])
                .map_err(|e| cant!("cannot read {path}: {e}"))?;
            if n == 0 {
                eof = true;
            } else {
                have += n;
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
    if !rd.header_done {
        return Err("empty file".into());
    }
    Ok(())
}
