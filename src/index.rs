//! The INDEX section (spec 6a): decoding, lookups that verify every entry
//! they rely on, and the full check of an index (`verify_index`), whose
//! result is apart from the file's verdict.

use crate::format;
use crate::read::{Decl, Event, Failure, File, Main};
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

/// A decoded INDEX section. The name table stays front-coded: each entry
/// points at its suffix in the section's bytes. Expanded keys are kept as
/// well while their total size stays below a cap proportional to the
/// section's length; past it, lookups scan the front-coded table instead.
/// Either way the memory is linear in INDEX's length, and the answers are
/// the same.
#[derive(Debug, Clone)]
pub struct Index<'a> {
    pub entries: Vec<Entry>,
    body: &'a [u8],
    names: Vec<NameRec>,
    /// Every key expanded, end to end, and where each one ends.
    flat: Option<(Vec<u8>, Vec<usize>)>,
}

#[derive(Debug, Clone, Copy)]
struct NameRec {
    shared: usize,
    /// The suffix: its offset in the section and its length.
    at: usize,
    len: usize,
    decl: u32,
}

/// The cap on expanded key bytes, per byte of INDEX. Mathlib needs about 2.6.
pub const KEY_BYTES_PER_INDEX_BYTE: u64 = 8;

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
/// coding); `Absent` when there is none. Time and memory are linear in the
/// section's length.
pub fn parse<'a>(file: &File<'a>) -> Result<Index<'a>, IndexError> {
    let len = file.section(format::SEC_INDEX).map_or(0, |s| s.length);
    parse_capped(file, len.saturating_mul(KEY_BYTES_PER_INDEX_BYTE))
}

/// [`parse`] with a given cap on the expanded key bytes kept for binary
/// search (for tests of the scan).
#[doc(hidden)]
pub fn parse_capped<'a>(file: &File<'a>, key_cap: u64) -> Result<Index<'a>, IndexError> {
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
    // every entry takes at least 3 bytes
    if nn.saturating_mul(3) > (end - p) as u64 {
        return Err(bad("name-count runs past the section"));
    }
    let mut names: Vec<NameRec> = Vec::with_capacity(nn as usize);
    let mut flat = Some((Vec::new(), Vec::with_capacity(nn as usize)));
    let mut total = 0u64;
    // the current key, kept in one buffer: O(suffix) work per entry
    let mut cur: Vec<u8> = Vec::new();
    for i in 0..nn {
        let shared = v(&mut p)?;
        let sl = v(&mut p)?;
        if sl > (end - p) as u64 {
            return Err(bad(format!("name {i}: suffix runs past the section")));
        }
        let at = p;
        let suffix = &b[p..p + sl as usize];
        p += sl as usize;
        let decl = v(&mut p)?;
        if shared > cur.len() as u64 {
            return Err(bad(format!(
                "name {i}: shared {shared} is longer than the previous key"
            )));
        }
        if suffix.is_empty() {
            return Err(bad(format!("name {i}: empty suffix")));
        }
        let shared = shared as usize;
        if shared < cur.len() {
            // with `shared` the full common prefix, the key's order against
            // the previous one is decided by this one byte
            if cur[shared] == suffix[0] {
                return Err(bad(format!(
                    "name {i}: shared {shared} is not the full common prefix"
                )));
            }
            if suffix[0] < cur[shared] {
                return Err(bad(format!("name {i}: keys out of order")));
            }
        }
        if decl >= nd {
            return Err(bad(format!("name {i}: declaration {decl} out of range")));
        }
        cur.truncate(shared);
        cur.extend_from_slice(suffix);
        total = total.saturating_add(cur.len() as u64);
        if total > key_cap {
            flat = None;
        }
        if let Some((buf, ends)) = &mut flat {
            buf.extend_from_slice(&cur);
            ends.push(buf.len());
        }
        names.push(NameRec {
            shared,
            at,
            len: suffix.len(),
            decl: decl as u32,
        });
    }
    if p != end {
        return Err(bad("bytes after the name table"));
    }
    Ok(Index {
        entries,
        body: b,
        names,
        flat,
    })
}

impl<'a> Index<'a> {
    /// The number of keys in the name table.
    pub fn len(&self) -> usize {
        self.names.len()
    }
    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
    /// Whether the expanded keys are kept (binary search), or lookups scan.
    pub fn expanded(&self) -> bool {
        self.flat.is_some()
    }
    /// The declaration named by key `j`.
    pub fn decl(&self, j: usize) -> u32 {
        self.names[j].decl
    }
    fn suffix(&self, j: usize) -> &'a [u8] {
        let n = self.names[j];
        &self.body[n.at..n.at + n.len]
    }
    /// Key `j`. Without the expanded keys this walks back through the
    /// front coding.
    pub fn key(&self, j: usize) -> Vec<u8> {
        if let Some((buf, ends)) = &self.flat {
            let a = if j == 0 { 0 } else { ends[j - 1] };
            return buf[a..ends[j]].to_vec();
        }
        let mut parts: Vec<&[u8]> = vec![self.suffix(j)];
        let mut need = self.names[j].shared;
        let mut m = j;
        while need > 0 {
            m -= 1;
            let s = self.names[m].shared;
            if s < need {
                parts.push(&self.suffix(m)[..need - s]);
                need = s;
            }
        }
        parts.iter().rev().flat_map(|x| x.iter().copied()).collect()
    }
    /// Calls `f` on every key in table order, with its declaration, in one
    /// buffer (memory: the longest key).
    pub fn try_for_each<E>(&self, mut f: impl FnMut(&[u8], u32) -> Result<(), E>) -> Result<(), E> {
        let mut cur: Vec<u8> = Vec::new();
        for (j, n) in self.names.iter().enumerate() {
            cur.truncate(n.shared);
            cur.extend_from_slice(self.suffix(j));
            f(&cur, n.decl)?;
        }
        Ok(())
    }
    /// The declaration the table gives for `key`: a binary search over the
    /// expanded keys, or one scan of the front-coded table.
    pub fn find(&self, key: &[u8]) -> Option<u32> {
        if let Some((buf, ends)) = &self.flat {
            let at = |j: usize| -> &[u8] {
                let a = if j == 0 { 0 } else { ends[j - 1] };
                &buf[a..ends[j]]
            };
            let (mut lo, mut hi) = (0usize, ends.len());
            while lo < hi {
                let mid = (lo + hi) / 2;
                match at(mid).cmp(key) {
                    std::cmp::Ordering::Less => lo = mid + 1,
                    std::cmp::Ordering::Greater => hi = mid,
                    std::cmp::Ordering::Equal => return Some(self.names[mid].decl),
                }
            }
            return None;
        }
        // `l`: the common prefix of the previous key and `key`; the previous
        // key is below `key`. Parsing checked the order and the front coding.
        let mut l = 0usize;
        for (j, n) in self.names.iter().enumerate() {
            if n.shared > l {
                // agrees with the previous key past `l`: still below
                continue;
            }
            if n.shared < l {
                // above the previous key where that one equals `key`
                return None;
            }
            let s = self.suffix(j);
            let q = &key[l..];
            let m = s.iter().zip(q).take_while(|(a, b)| a == b).count();
            if m == s.len() {
                if m == q.len() {
                    return Some(n.decl);
                }
                l += m;
            } else if m == q.len() || s[m] > q[m] {
                return None;
            } else {
                l += m;
            }
        }
        None
    }
}

/// The number of names a declaration declares.
fn declared_count(d: &Decl) -> u64 {
    match d {
        Decl::Inductive(i) => (i.types.len() + i.ctors.len() + i.recs.len()) as u64,
        _ => 1,
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

#[derive(Debug, Clone, Copy)]
struct Seen {
    kind: u8,
    offset: u64,
    block: Option<(u64, u64)>,
}

/// Many lookups in one file. INDEX is decoded once, in [`Lookup::new`].
/// MAIN is read once as well: the reader keeps its state, and goes on from
/// where the furthest lookup so far stopped.
///
/// The cost of a lookup of declaration i is the binary search (or one scan
/// of the name table, past the key cap), plus decoding MAIN up to the end
/// of declaration i's record, if no earlier lookup went that far. That MAIN
/// prefix is the main cost: for a declaration late in the file it is almost
/// all of MAIN. Lookups never read PROOFS. Every entry a lookup relies on is
/// verified: the entries of declarations 0 to i, and the key against the
/// names declaration i declares.
pub struct Lookup<'a> {
    bytes: &'a [u8],
    index: Index<'a>,
    main: Main<'a>,
    start: u64,
    proofs: u64,
    seen: Vec<Seen>,
    /// An entry or MAIN record that failed: lookups past it fail the same way.
    stop: Option<IndexError>,
}

impl<'a> Lookup<'a> {
    /// Decodes INDEX. MAIN is read later, as far as lookups need.
    pub fn new(file: &File<'a>) -> Result<Lookup<'a>, IndexError> {
        let index = parse(file)?;
        let main = file.main();
        Ok(Lookup {
            bytes: file.bytes,
            index,
            start: main.start(),
            main,
            proofs: file
                .section(format::SEC_PROOFS)
                .map(|s| s.offset)
                .unwrap_or(0),
            seen: Vec::new(),
            stop: None,
        })
    }

    /// The decoded INDEX.
    pub fn index(&self) -> &Index<'a> {
        &self.index
    }

    /// Finds a declared name by its key.
    pub fn find(&mut self, key: &[u8]) -> Result<Found, IndexError> {
        let i = self.index.find(key).ok_or(IndexError::NotFound)?;
        while self.seen.len() <= i as usize {
            if let Some(e) = &self.stop {
                return Err(e.clone());
            }
            match self.main.next() {
                None => return Err(bad(format!("declaration {i} is not in MAIN"))),
                Some(Err(e)) => {
                    let e = IndexError::File(e);
                    self.stop = Some(e.clone());
                    return Err(e);
                }
                Some(Ok(Event::Decl {
                    index,
                    offset,
                    decl,
                })) => {
                    let checked = match self.index.entries.get(index as usize) {
                        None => Err(bad("more declarations than entries")),
                        Some(e) => check_entry(e, index, offset - self.start, &decl, self.proofs),
                    };
                    if let Err(e) = checked {
                        self.stop = Some(e.clone());
                        return Err(e);
                    }
                    let block = match decl {
                        Decl::ThmBlock { block, .. } => Some((block.offset, block.length)),
                        _ => None,
                    };
                    self.seen.push(Seen {
                        kind: decl.kind(),
                        offset,
                        block,
                    });
                }
                Some(Ok(_)) => {}
            }
        }
        // the key names a name declaration i declares, compared by value
        let st = self.main.state();
        match st.canon.find_key(self.bytes, key) {
            Some(c) if st.canon_decl[c as usize] == i => {}
            _ => {
                return Err(bad(format!(
                    "the key does not name a name declaration {i} declares"
                )))
            }
        }
        let s = self.seen[i as usize];
        Ok(Found {
            decl: i,
            kind: s.kind,
            offset: s.offset,
            block: s.block,
        })
    }
}

/// One lookup: [`Lookup::new`] then [`Lookup::find`]. For many lookups in
/// the same file, keep a [`Lookup`]: this decodes INDEX on every call and
/// reads MAIN again from the start.
pub fn lookup(file: &File, key: &[u8]) -> Result<Found, IndexError> {
    Lookup::new(file)?.find(key)
}

/// Checks every entry and the whole name table against the records
/// (spec 6a.3). The file's verdict is apart: a malformed MAIN gives `File`.
/// Memory stays linear in the bytes read: keys are compared one at a time
/// against the names MAIN built.
pub fn verify_index(file: &File) -> Result<(), IndexError> {
    let ix = parse(file)?;
    let proofs = file
        .section(format::SEC_PROOFS)
        .map(|s| s.offset)
        .unwrap_or(0);
    let mut m = file.main();
    let start = m.start();
    let mut declared = 0u64;
    for ev in m.by_ref() {
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
            declared += declared_count(&decl);
        }
    }
    let st = m.state();
    if declared != ix.len() as u64 {
        return Err(bad(format!(
            "{declared} declared names, the name table holds {}",
            ix.len()
        )));
    }
    // Keys are distinct (strictly increasing) and each names a distinct
    // declared name of its declaration; with the counts equal, every
    // declared name is in the table once.
    ix.try_for_each(|k, d| match st.canon.find_key(file.bytes, k) {
        Some(c) if st.canon_decl[c as usize] == d => Ok(()),
        Some(c) if st.canon_decl[c as usize] != u32::MAX => Err(bad(format!(
            "a key names declaration {d}, it is declared by {}",
            st.canon_decl[c as usize]
        ))),
        _ => Err(bad("a key names no declared name")),
    })
}
