//! `susz-asm`: a small textual assembler for Susz files, used to write the
//! test vectors so that each one can be read and reviewed.
//!
//! ```text
//! # a comment (to the end of the line, outside strings)
//! header [magic=HEX] [major=N] [r16=N] [r32=N]
//! counts NAMES LEVELS EXPRS DECLS
//! section MAIN|PROOFS|SOURCE|PAD|INDEX|N [id=N] [flags=N] [res=N] [doff=±N] [dlen=±N]
//! block LABEL [decl=N]          # in PROOFS: a block (its records count from 1)
//! trailer [tlen=N] [endmagic=HEX] [nsec=N]
//! [!] [@LABEL] TOKENS...        # one record; `!` marks the expected error location
//! nt NAME DECL [shared=K]      # in INDEX: a name-table entry, front-coded against the previous `nt`
//! ```
//!
//! Tokens: `N` a minimal varint; `b:N` one byte; `x:HEX` raw bytes;
//! `s:"..."` a string (varint length, then the bytes; escapes `\\ \" \n \0
//! \xHH`); `nat:DEC` a nat; `natx:HEX` nat bytes given raw; `v:N:K` the
//! varint of N padded to K bytes; `len:L` / `cnt:L` the byte length /
//! record count of block L; `rel:A:B` the offset of record B minus that of
//! record A (`MAIN` is the start of MAIN); `ntcount` the number of `nt`
//! entries; `u16:N`, `u32:N`, `u64:N` fixed-width.

use crate::format;
use crate::index::key_of_dotted;
use std::collections::HashMap;

/// Where a marked record (or other location) is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Loc {
    pub section: u16,
    pub offset: u64,
    pub record: u64,
    pub decl: Option<u32>,
}

/// The layout of an assembled file.
#[derive(Debug, Clone, Default)]
pub struct Layout {
    /// (id, offset, length) of each section in directory order.
    pub sections: Vec<(u16, u64, u64)>,
    pub trailer: u64,
    pub len: u64,
    /// Blocks: label to (offset, length, records).
    pub blocks: HashMap<String, (u64, u64, u64)>,
}

impl Layout {
    pub fn section(&self, id: u16) -> (u64, u64) {
        self.sections
            .iter()
            .find(|s| s.0 == id)
            .map(|s| (s.1, s.2))
            .unwrap_or((0, 0))
    }
    /// Absolute offset of directory entry `i` (from 0).
    pub fn entry(&self, i: usize) -> u64 {
        self.trailer + 20 + 24 * i as u64
    }
}

pub struct Assembled {
    pub bytes: Vec<u8>,
    pub marked: Option<Loc>,
    pub layout: Layout,
}

#[derive(Clone)]
enum Tok {
    Bytes(Vec<u8>),
    Len(String),
    Cnt(String),
    Rel(String, String),
    NtCount,
}

struct Rec {
    label: Option<String>,
    marked: bool,
    toks: Vec<Tok>,
}

struct Sec {
    id: u16,
    flags: Option<u16>,
    res: u32,
    doff: i64,
    dlen: i64,
    // records; for PROOFS, grouped in blocks
    recs: Vec<Rec>,
    blocks: Vec<(String, Option<u32>, Vec<Rec>)>,
}

fn hex(s: &str) -> Result<Vec<u8>, String> {
    if s.len() % 2 != 0 {
        return Err(format!("odd hex '{s}'"));
    }
    (0..s.len() / 2)
        .map(|i| {
            u8::from_str_radix(&s[2 * i..2 * i + 2], 16).map_err(|e| format!("hex '{s}': {e}"))
        })
        .collect()
}

fn num(s: &str) -> Result<u64, String> {
    s.parse::<u64>().map_err(|e| format!("number '{s}': {e}"))
}

fn inum(s: &str) -> Result<i64, String> {
    s.parse::<i64>().map_err(|e| format!("number '{s}': {e}"))
}

fn unescape(s: &str) -> Result<Vec<u8>, String> {
    let b = s.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < b.len() {
        if b[i] == b'\\' {
            let c = *b.get(i + 1).ok_or("trailing backslash")?;
            match c {
                b'\\' => out.push(b'\\'),
                b'"' => out.push(b'"'),
                b'n' => out.push(b'\n'),
                b'0' => out.push(0),
                b'x' => {
                    out.extend(hex(s.get(i + 2..i + 4).ok_or("short \\x")?)?);
                    i += 2;
                }
                _ => return Err(format!("bad escape \\{}", c as char)),
            }
            i += 2;
        } else {
            out.push(b[i]);
            i += 1;
        }
    }
    Ok(out)
}

// Splits a line into tokens, keeping s:"..." whole, dropping comments.
fn split(line: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut in_str = false;
    let mut esc = false;
    for c in line.chars() {
        if in_str {
            cur.push(c);
            if esc {
                esc = false;
            } else if c == '\\' {
                esc = true;
            } else if c == '"' {
                in_str = false;
            }
            continue;
        }
        match c {
            '#' => break,
            ' ' | '\t' => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
            }
            '"' => {
                in_str = true;
                cur.push(c);
            }
            _ => cur.push(c),
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

fn varint(v: u64) -> Vec<u8> {
    let mut b = Vec::new();
    format::put_varint(&mut b, v);
    b
}

fn token(t: &str) -> Result<Tok, String> {
    if let Ok(v) = t.parse::<u64>() {
        return Ok(Tok::Bytes(varint(v)));
    }
    if t == "ntcount" {
        return Ok(Tok::NtCount);
    }
    let (k, rest) = t
        .split_once(':')
        .ok_or_else(|| format!("bad token '{t}'"))?;
    Ok(match k {
        "b" => Tok::Bytes(vec![num(rest)? as u8]),
        "x" => Tok::Bytes(hex(rest)?),
        "s" => {
            let inner = rest
                .strip_prefix('"')
                .and_then(|r| r.strip_suffix('"'))
                .ok_or_else(|| format!("bad string '{t}'"))?;
            let b = unescape(inner)?;
            let mut out = varint(b.len() as u64);
            out.extend(b);
            Tok::Bytes(out)
        }
        "nat" => {
            let b = format::nat_from_decimal(rest.as_bytes())
                .ok_or_else(|| format!("bad nat '{t}'"))?;
            let mut out = varint(b.len() as u64);
            out.extend(b);
            Tok::Bytes(out)
        }
        "natx" => {
            let b = hex(rest)?;
            let mut out = varint(b.len() as u64);
            out.extend(b);
            Tok::Bytes(out)
        }
        "v" => {
            let (n, k) = rest.split_once(':').ok_or("v:N:K")?;
            let (mut n, k) = (num(n)?, num(k)? as usize);
            let mut out = Vec::new();
            for i in 0..k {
                let mut x = (n & 127) as u8;
                n >>= 7;
                if i + 1 < k {
                    x |= 128;
                }
                out.push(x);
            }
            Tok::Bytes(out)
        }
        "len" => Tok::Len(rest.into()),
        "cnt" => Tok::Cnt(rest.into()),
        "rel" => {
            let (a, b) = rest.split_once(':').ok_or("rel:A:B")?;
            Tok::Rel(a.into(), b.into())
        }
        "u16" => Tok::Bytes((num(rest)? as u16).to_le_bytes().to_vec()),
        "u32" => Tok::Bytes((num(rest)? as u32).to_le_bytes().to_vec()),
        "u64" => Tok::Bytes(num(rest)?.to_le_bytes().to_vec()),
        _ => return Err(format!("bad token '{t}'")),
    })
}

fn sec_id(s: &str) -> Result<u16, String> {
    Ok(match s {
        "MAIN" => format::SEC_MAIN,
        "PROOFS" => format::SEC_PROOFS,
        "SOURCE" => format::SEC_SOURCE,
        "PAD" => format::SEC_PAD,
        "INDEX" => format::SEC_INDEX,
        n => num(n)? as u16,
    })
}

fn opts(ws: &[String]) -> Result<HashMap<String, String>, String> {
    let mut m = HashMap::new();
    for w in ws {
        let (k, v) = w
            .split_once('=')
            .ok_or_else(|| format!("bad option '{w}'"))?;
        m.insert(k.to_string(), v.to_string());
    }
    Ok(m)
}

/// Assembles a source text.
pub fn assemble(src: &str) -> Result<Assembled, String> {
    let mut magic = format::MAGIC.to_vec();
    let mut major = format::MAJOR as u64;
    let (mut r16, mut r32) = (0u64, 0u64);
    let mut counts = [0u32; 4];
    let mut secs: Vec<Sec> = Vec::new();
    let (mut tlen, mut endmagic, mut nsec): (Option<u64>, Vec<u8>, Option<u64>) =
        (None, format::END_MAGIC.to_vec(), None);
    let mut nts: Vec<(String, u64, Option<u64>, bool)> = Vec::new();
    let mut nt_after: Vec<usize> = Vec::new(); // record count of INDEX at each nt (entries go after those records)
    for (ln, line) in src.lines().enumerate() {
        let ws = split(line);
        if ws.is_empty() {
            continue;
        }
        let e = |m: String| format!("line {}: {m}", ln + 1);
        match ws[0].as_str() {
            "header" => {
                let o = opts(&ws[1..]).map_err(e)?;
                if let Some(v) = o.get("magic") {
                    magic = hex(v).map_err(e)?;
                }
                if let Some(v) = o.get("major") {
                    major = num(v).map_err(e)?;
                }
                if let Some(v) = o.get("r16") {
                    r16 = num(v).map_err(e)?;
                }
                if let Some(v) = o.get("r32") {
                    r32 = num(v).map_err(e)?;
                }
            }
            "counts" => {
                for k in 0..4 {
                    counts[k] = num(ws
                        .get(k + 1)
                        .ok_or_else(|| e("counts takes 4 numbers".into()))?)
                    .map_err(e)? as u32;
                }
            }
            "section" => {
                let id = sec_id(ws.get(1).ok_or_else(|| e("section name".into()))?).map_err(e)?;
                let o = opts(&ws[2..]).map_err(e)?;
                let gi = |k: &str| -> Result<Option<i64>, String> {
                    o.get(k).map(|v| inum(v)).transpose()
                };
                secs.push(Sec {
                    id: gi("id").map_err(e)?.map(|x| x as u16).unwrap_or(id),
                    flags: gi("flags").map_err(e)?.map(|x| x as u16),
                    res: gi("res").map_err(e)?.unwrap_or(0) as u32,
                    doff: gi("doff").map_err(e)?.unwrap_or(0),
                    dlen: gi("dlen").map_err(e)?.unwrap_or(0),
                    recs: Vec::new(),
                    blocks: Vec::new(),
                });
            }
            "block" => {
                let s = secs
                    .last_mut()
                    .ok_or_else(|| e("block outside a section".into()))?;
                let label = ws.get(1).ok_or_else(|| e("block label".into()))?.clone();
                let o = opts(&ws[2..]).map_err(e)?;
                let decl = o
                    .get("decl")
                    .map(|v| num(v))
                    .transpose()
                    .map_err(e)?
                    .map(|x| x as u32);
                s.blocks.push((label, decl, Vec::new()));
            }
            "trailer" => {
                let o = opts(&ws[1..]).map_err(e)?;
                if let Some(v) = o.get("tlen") {
                    tlen = Some(num(v).map_err(e)?);
                }
                if let Some(v) = o.get("endmagic") {
                    endmagic = hex(v).map_err(e)?;
                }
                if let Some(v) = o.get("nsec") {
                    nsec = Some(num(v).map_err(e)?);
                }
            }
            "nt" => {
                let s = secs
                    .last()
                    .ok_or_else(|| e("nt outside a section".into()))?;
                let name = ws.get(1).ok_or_else(|| e("nt NAME DECL".into()))?.clone();
                let decl = num(ws.get(2).ok_or_else(|| e("nt NAME DECL".into()))?).map_err(e)?;
                let o = opts(&ws[3..]).map_err(e)?;
                let shared = o.get("shared").map(|v| num(v)).transpose().map_err(e)?;
                nts.push((name, decl, shared, false));
                nt_after.push(s.recs.len());
            }
            _ => {
                let s = secs
                    .last_mut()
                    .ok_or_else(|| e("a record outside a section".into()))?;
                let mut i = 0;
                let mut marked = false;
                let mut label = None;
                if ws[i] == "!" {
                    marked = true;
                    i += 1;
                }
                if let Some(l) = ws.get(i).and_then(|w| w.strip_prefix('@')) {
                    label = Some(l.to_string());
                    i += 1;
                }
                let toks = ws[i..]
                    .iter()
                    .map(|t| token(t))
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(e)?;
                let r = Rec {
                    label,
                    marked,
                    toks,
                };
                if let Some(b) = s.blocks.last_mut() {
                    b.2.push(r);
                } else {
                    s.recs.push(r);
                }
            }
        }
    }
    // name-table bytes
    let mut nt_bytes: Vec<Vec<u8>> = Vec::new();
    let mut prev: Vec<u8> = Vec::new();
    for (name, decl, shared, _) in &nts {
        let key = key_of_dotted(name);
        let full = prev
            .iter()
            .zip(key.iter())
            .take_while(|(a, b)| a == b)
            .count();
        let sh = shared.map(|x| x as usize).unwrap_or(full).min(key.len());
        let mut b = varint(sh as u64);
        b.extend(varint((key.len() - sh) as u64));
        b.extend_from_slice(&key[sh..]);
        b.extend(varint(*decl));
        nt_bytes.push(b);
        prev = key;
    }
    // iterate to a fixed point: lengths, counts and offsets
    let mut blocks: HashMap<String, (u64, u64, u64)> = HashMap::new();
    let mut labels: HashMap<String, u64> = HashMap::new();
    let mut last: Option<Vec<u8>> = None;
    for _ in 0..8 {
        let r = emit(
            &magic, major, r16, r32, &counts, &secs, tlen, &endmagic, nsec, &blocks, &labels,
            &nt_bytes, &nt_after,
        )?;
        let done = last.as_ref() == Some(&r.0.bytes);
        blocks = r.1;
        labels = r.2;
        last = Some(r.0.bytes.clone());
        if done {
            return Ok(r.0);
        }
    }
    Err("layout does not settle".into())
}

#[allow(clippy::too_many_arguments)]
#[allow(clippy::type_complexity)]
fn emit(
    magic: &[u8],
    major: u64,
    r16: u64,
    r32: u64,
    counts: &[u32; 4],
    secs: &[Sec],
    tlen: Option<u64>,
    endmagic: &[u8],
    nsec: Option<u64>,
    blocks: &HashMap<String, (u64, u64, u64)>,
    labels: &HashMap<String, u64>,
    nt_bytes: &[Vec<u8>],
    nt_after: &[usize],
) -> Result<
    (
        Assembled,
        HashMap<String, (u64, u64, u64)>,
        HashMap<String, u64>,
    ),
    String,
> {
    let mut out: Vec<u8> = Vec::new();
    out.extend_from_slice(magic);
    out.extend_from_slice(&(major as u16).to_le_bytes());
    out.extend_from_slice(&(r16 as u16).to_le_bytes());
    out.extend_from_slice(&(r32 as u32).to_le_bytes());
    let mut nb: HashMap<String, (u64, u64, u64)> = HashMap::new();
    let mut nl: HashMap<String, u64> = HashMap::new();
    let mut marked: Option<Loc> = None;
    let mut layout = Layout::default();
    let rec_bytes = |r: &Rec, out: &mut Vec<u8>| -> Result<(), String> {
        for t in &r.toks {
            match t {
                Tok::Bytes(b) => out.extend_from_slice(b),
                Tok::Len(l) => out.extend(varint(blocks.get(l).map(|x| x.1).unwrap_or(0))),
                Tok::Cnt(l) => out.extend(varint(blocks.get(l).map(|x| x.2).unwrap_or(0))),
                Tok::Rel(a, b) => {
                    let g = |x: &str| labels.get(x).copied().unwrap_or(0);
                    out.extend(varint(g(b).wrapping_sub(g(a))));
                }
                Tok::NtCount => out.extend(varint(nt_bytes.len() as u64)),
            }
        }
        Ok(())
    };
    let mut dir: Vec<(u16, u16, u32, u64, u64)> = Vec::new();
    for s in secs {
        let start = out.len() as u64;
        if s.id == format::SEC_MAIN {
            nl.insert("MAIN".into(), start);
        }
        for (i, r) in s.recs.iter().enumerate() {
            for (k, b) in nt_bytes.iter().enumerate() {
                if nt_after[k] == i && s.id == format::SEC_INDEX {
                    out.extend_from_slice(b);
                }
            }
            let at = out.len() as u64;
            if let Some(l) = &r.label {
                nl.insert(l.clone(), at);
            }
            if r.marked {
                marked = Some(Loc {
                    section: s.id,
                    offset: at,
                    record: i as u64 + 1,
                    decl: None,
                });
            }
            rec_bytes(r, &mut out)?;
        }
        if s.id == format::SEC_INDEX {
            for (k, b) in nt_bytes.iter().enumerate() {
                if nt_after[k] == s.recs.len() {
                    out.extend_from_slice(b);
                }
            }
        }
        for (label, decl, rs) in &s.blocks {
            let bstart = out.len() as u64;
            for (i, r) in rs.iter().enumerate() {
                let at = out.len() as u64;
                if r.marked {
                    marked = Some(Loc {
                        section: s.id,
                        offset: at,
                        record: i as u64 + 1,
                        decl: *decl,
                    });
                }
                rec_bytes(r, &mut out)?;
            }
            nb.insert(
                label.clone(),
                (bstart, out.len() as u64 - bstart, rs.len() as u64),
            );
        }
        let len = out.len() as u64 - start;
        let flags = s
            .flags
            .unwrap_or_else(|| format::known_flags(s.id).unwrap_or(0));
        dir.push((
            s.id,
            flags,
            s.res,
            (start as i64 + s.doff) as u64,
            (len as i64 + s.dlen) as u64,
        ));
        layout.sections.push((s.id, start, len));
    }
    let ts = out.len() as u64;
    layout.trailer = ts;
    for c in counts {
        out.extend_from_slice(&c.to_le_bytes());
    }
    out.extend_from_slice(&(nsec.unwrap_or(dir.len() as u64) as u32).to_le_bytes());
    for (id, fl, res, off, len) in &dir {
        out.extend_from_slice(&id.to_le_bytes());
        out.extend_from_slice(&fl.to_le_bytes());
        out.extend_from_slice(&res.to_le_bytes());
        out.extend_from_slice(&off.to_le_bytes());
        out.extend_from_slice(&len.to_le_bytes());
    }
    let tl = tlen.unwrap_or(16 + 4 + 24 * dir.len() as u64 + 8);
    out.extend_from_slice(&(tl as u32).to_le_bytes());
    out.extend_from_slice(endmagic);
    layout.len = out.len() as u64;
    layout.blocks = nb.clone();
    Ok((
        Assembled {
            bytes: out,
            marked,
            layout,
        },
        nb,
        nl,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn minimal() {
        let a = assemble("section MAIN\n1 0 s:\"A\"\n8 0\n18 0 1 0 1 0\ncounts 2 1 1 1\n").unwrap();
        match crate::read::verify(&a.bytes) {
            crate::read::Outcome::Accepted(s) => assert_eq!(s.counts, [2, 1, 1, 1]),
            o => panic!("{o:?}"),
        }
    }
}
