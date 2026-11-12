//! The INDEX section (spec 6a): decoding, lookups that verify every entry
//! they rely on, and the full check of an index (`verify_index`), whose
//! result is apart from the file's verdict.

use crate::canon::ANON;
use crate::format;
use crate::read::{Decl, Event, Failure, File, Main};
use std::collections::HashMap;
use std::fmt;

/// Entry i of the index: declaration i.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Entry {
    pub kind: u8,
    /// Offset of the record's tag byte from the start of MAIN.
    pub offset: u64,
    /// For kind 6: the block's offset from the start of PROOFS and its length.
    pub block: Option<(u64, u64)>,
}

/// A decoded INDEX section.
#[derive(Debug, Clone)]
pub struct Index {
    pub entries: Vec<Entry>,
    /// The name table: (key, declaration index), strictly increasing keys.
    pub names: Vec<(Vec<u8>, u32)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IndexError {
    /// The file has no INDEX section.
    Absent,
    /// The name is not in the name table.
    NotFound,
    /// An entry disagrees with the records, or the section is malformed.
    Invalid(String),
    /// The MAIN prefix read to verify an entry is malformed: the file is rejected.
    File(Failure),
}

impl fmt::Display for IndexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IndexError::Absent => f.write_str("no INDEX section"),
            IndexError::NotFound => f.write_str("not found"),
            IndexError::Invalid(m) => write!(f, "index invalid: {m}"),
            IndexError::File(e) => write!(f, "{e}"),
        }
    }
}

fn bad(m: impl Into<String>) -> IndexError {
    IndexError::Invalid(m.into())
}

/// The INDEX key of a dotted name: components split at `.`, a component
/// of digits only is numeric.
pub fn key_of_dotted(name: &str) -> Vec<u8> {
    let mut out = Vec::new();
    for c in name.split('.') {
        if !c.is_empty() && c.bytes().all(|b| b.is_ascii_digit()) && c.len() < 20 {
            if let Ok(k) = c.parse::<u64>() {
                out.push(2);
                format::put_varint(&mut out, k);
                continue;
            }
        }
        out.push(1);
        format::put_varint(&mut out, c.len() as u64);
        out.extend_from_slice(c.as_bytes());
    }
    out
}

/// Decodes the INDEX section, checking its own rules (sizes, order, front
/// coding); `Absent` when there is none.
pub fn parse(file: &File) -> Result<Index, IndexError> {
    let Some(s) = file.section(format::SEC_INDEX) else {
        return Err(IndexError::Absent);
    };
    let b = file.body(s);
    let end = b.len();
    let mut p = 0usize;
    let v = |p: &mut usize| {
        format::get_varint(b, p, end)
            .map_err(|e| bad(format!("bad varint at INDEX byte {}: {e:?}", *p)))
    };
    let nd = v(&mut p)?;
    if nd != file.counts[3] as u64 {
        return Err(bad(format!(
            "decl-count {nd}, the file has {} declarations",
            file.counts[3]
        )));
    }
    let mut entries = Vec::with_capacity(nd.min(end as u64) as usize);
    let (mut off, mut boff) = (0u64, 0u64);
    for i in 0..nd {
        if p >= end {
            return Err(bad(format!("entry {i} runs past the section")));
        }
        let kind = b[p];
        p += 1;
        if kind > 6 {
            return Err(bad(format!("entry {i}: kind {kind}")));
        }
        off = off
            .checked_add(v(&mut p)?)
            .ok_or_else(|| bad("offset overflow"))?;
        let block = if kind == 6 {
            let l = v(&mut p)?;
            let r = (boff, l);
            boff = boff
                .checked_add(l)
                .ok_or_else(|| bad("block offset overflow"))?;
            Some(r)
        } else {
            None
        };
        entries.push(Entry {
            kind,
            offset: off,
            block,
        });
    }
    let nn = v(&mut p)?;
    if nn > (end - p) as u64 {
        return Err(bad("name-count runs past the section"));
    }
    let mut names: Vec<(Vec<u8>, u32)> = Vec::with_capacity(nn as usize);
    let mut prev: Vec<u8> = Vec::new();
    for i in 0..nn {
        let shared = v(&mut p)?;
        let sl = v(&mut p)?;
        if sl > (end - p) as u64 {
            return Err(bad(format!("name {i}: suffix runs past the section")));
        }
        let suffix = &b[p..p + sl as usize];
        p += sl as usize;
        let decl = v(&mut p)?;
        if shared > prev.len() as u64 {
            return Err(bad(format!(
                "name {i}: shared {shared} is longer than the previous key"
            )));
        }
        if suffix.is_empty() {
            return Err(bad(format!("name {i}: empty suffix")));
        }
        let shared = shared as usize;
        if shared < prev.len() && prev[shared] == suffix[0] {
            return Err(bad(format!(
                "name {i}: shared {shared} is not the full common prefix"
            )));
        }
        let mut key = prev[..shared].to_vec();
        key.extend_from_slice(suffix);
        if i > 0 && key <= prev {
            return Err(bad(format!("name {i}: keys out of order or repeated")));
        }
        if decl >= nd {
            return Err(bad(format!("name {i}: declaration {decl} out of range")));
        }
        prev = key.clone();
        names.push((key, decl as u32));
    }
    if p != end {
        return Err(bad("bytes after the name table"));
    }
    Ok(Index { entries, names })
}

/// Declared names of a declaration, in record order.
fn declared(d: &Decl) -> Vec<u32> {
    match d {
        Decl::Axiom { head, .. }
        | Decl::Defn { head, .. }
        | Decl::Thm { head, .. }
        | Decl::Opaque { head, .. }
        | Decl::Quot { head, .. }
        | Decl::ThmBlock { head, .. } => vec![head.name],
        Decl::Inductive(i) => i
            .types
            .iter()
            .map(|t| t.head.name)
            .chain(i.ctors.iter().map(|c| c.head.name))
            .chain(i.recs.iter().map(|r| r.head.name))
            .collect(),
    }
}

fn check_entry(e: &Entry, i: u32, offset: u64, d: &Decl, proofs: u64) -> Result<(), IndexError> {
    if e.offset != offset {
        return Err(bad(format!(
            "entry {i}: offset {} is not its record ({offset})",
            e.offset
        )));
    }
    if e.kind != d.kind() {
        return Err(bad(format!(
            "entry {i}: kind {} is not the record's {}",
            e.kind,
            d.kind()
        )));
    }
    if let Decl::ThmBlock { block, .. } = d {
        let (o, l) = e.block.unwrap();
        if l != block.length || proofs + o != block.offset {
            return Err(bad(format!(
                "entry {i}: block length {l} is not the record's {}",
                block.length
            )));
        }
    }
    Ok(())
}

/// What a lookup found (every entry it relied on verified).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Found {
    pub decl: u32,
    pub kind: u8,
    /// Absolute offset of the declaration's record.
    pub offset: u64,
    /// Absolute offset and length of its proof block.
    pub block: Option<(u64, u64)>,
}

/// Finds a declared name by its key, reading INDEX and the MAIN prefix up
/// to the declaration (never PROOFS), and verifying every entry it relies on.
pub fn lookup(file: &File, key: &[u8]) -> Result<Found, IndexError> {
    let ix = parse(file)?;
    let i = match ix.names.binary_search_by(|(k, _)| k.as_slice().cmp(key)) {
        Ok(j) => ix.names[j].1,
        Err(_) => return Err(IndexError::NotFound),
    };
    let proofs = file
        .section(format::SEC_PROOFS)
        .map(|s| s.offset)
        .unwrap_or(0);
    let mut m: Main = file.main();
    let start = m.start();
    while let Some(ev) = m.next() {
        let ev = ev.map_err(IndexError::File)?;
        if let Event::Decl {
            index,
            offset,
            decl,
        } = ev
        {
            let e = &ix.entries[index as usize];
            check_entry(e, index, offset - start, &decl, proofs)?;
            if index == i {
                let st = m.state();
                let ok = declared(&decl).into_iter().any(|n| {
                    let mut k = Vec::new();
                    st.canon.key(file.bytes, st.name_canon[n as usize], &mut k);
                    k == key
                });
                if !ok {
                    return Err(bad(format!(
                        "the key does not name a name declaration {i} declares"
                    )));
                }
                let block = match decl {
                    Decl::ThmBlock { block, .. } => Some((block.offset, block.length)),
                    _ => None,
                };
                return Ok(Found {
                    decl: i,
                    kind: e.kind,
                    offset,
                    block,
                });
            }
        }
    }
    Err(bad(format!("declaration {i} is not in MAIN")))
}

/// Checks every entry and the whole name table against the records
/// (spec 6a.3). The file's verdict is apart: a malformed MAIN gives `File`.
pub fn verify_index(file: &File) -> Result<(), IndexError> {
    let ix = parse(file)?;
    let proofs = file
        .section(format::SEC_PROOFS)
        .map(|s| s.offset)
        .unwrap_or(0);
    let mut m = file.main();
    let start = m.start();
    let mut decl_names: Vec<(u32, u32)> = Vec::new();
    while let Some(ev) = m.next() {
        let ev = ev.map_err(IndexError::File)?;
        if let Event::Decl {
            index,
            offset,
            decl,
        } = ev
        {
            let e = ix
                .entries
                .get(index as usize)
                .ok_or_else(|| bad("more declarations than entries"))?;
            check_entry(e, index, offset - start, &decl, proofs)?;
            for n in declared(&decl) {
                decl_names.push((n, index));
            }
        }
    }
    let st = m.state();
    let mut want: HashMap<Vec<u8>, u32> = HashMap::with_capacity(decl_names.len());
    for (n, d) in decl_names {
        let c = st.name_canon[n as usize];
        let mut k = Vec::new();
        if c != ANON {
            st.canon.key(file.bytes, c, &mut k);
        }
        want.insert(k, d);
    }
    if want.len() != ix.names.len() {
        return Err(bad(format!(
            "{} declared names, the name table holds {}",
            want.len(),
            ix.names.len()
        )));
    }
    for (k, d) in &ix.names {
        match want.get(k) {
            Some(x) if x == d => {}
            Some(x) => {
                return Err(bad(format!(
                    "a key names declaration {d}, it is declared by {x}"
                )))
            }
            None => return Err(bad("a key names no declared name")),
        }
    }
    Ok(())
}
