//! Names made canonical: two name records with the same prefix (canonical)
//! and the same component get the same canonical id. String components are
//! kept as (offset, length) into a byte source the caller owns (the packer's
//! stream, the reader's file).

/// Canonical id of the anonymous name.
pub const ANON: u32 = 0;
const NUM: u32 = u32::MAX;

pub struct Canon {
    slots: Vec<u32>,
    mask: usize,
    hash: Vec<u32>,
    /// Canonical prefix of each canonical name (`u32::MAX` for the anonymous name).
    pub pre: Vec<u32>,
    /// String component: offset of its bytes in the source; numeric: the number.
    pub off: Vec<u64>,
    /// String component: its length; numeric: `u32::MAX`.
    pub len: Vec<u32>,
}

#[inline(always)]
fn mix(h: u64, x: u64) -> u64 {
    (h.rotate_left(5) ^ x).wrapping_mul(0x517c_c1b7_2722_0a95)
}

fn hash_str(pre: u32, s: &[u8]) -> u32 {
    let mut h = mix(0x9e37_79b9, pre as u64);
    let mut c = s.chunks_exact(8);
    for w in &mut c {
        h = mix(h, u64::from_le_bytes(w.try_into().unwrap()));
    }
    let r = c.remainder();
    let mut t = [0u8; 8];
    t[..r.len()].copy_from_slice(r);
    h = mix(h, u64::from_le_bytes(t) ^ ((s.len() as u64) << 56));
    (h >> 32) as u32
}

fn hash_num(pre: u32, k: u64) -> u32 {
    let h = mix(mix(0x1234_5678, pre as u64), k);
    ((h >> 32) as u32) ^ 0x8000_0001
}

/// A component of a canonical name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Part<'a> {
    Str(&'a [u8]),
    Num(u64),
}

impl Default for Canon {
    fn default() -> Self {
        Self::new()
    }
}

impl Canon {
    pub fn new() -> Canon {
        Canon {
            slots: vec![0; 1 << 16],
            mask: (1 << 16) - 1,
            hash: vec![0],
            pre: vec![u32::MAX],
            off: vec![0],
            len: vec![u32::MAX - 1],
        }
    }
    pub fn count(&self) -> usize {
        self.hash.len()
    }
    fn grow(&mut self) {
        let n = self.slots.len() * 2;
        self.slots = vec![0; n];
        self.mask = n - 1;
        for id in 1..self.hash.len() {
            let mut i = self.hash[id] as usize & self.mask;
            while self.slots[i] != 0 {
                i = (i + 1) & self.mask;
            }
            self.slots[i] = id as u32;
        }
    }
    /// The canonical id of a string-component name; `src[off..off+len]` holds
    /// the component, and stays there for the life of the table.
    #[inline(always)]
    pub fn str_id(&mut self, src: &[u8], pre: u32, off: u64, len: u32) -> u32 {
        let s = &src[off as usize..off as usize + len as usize];
        let h = hash_str(pre, s);
        let mut i = h as usize & self.mask;
        loop {
            let id = self.slots[i];
            if id == 0 {
                break;
            }
            let k = id as usize;
            if self.hash[k] == h && self.pre[k] == pre && self.len[k] == len {
                let o = self.off[k] as usize;
                if &src[o..o + len as usize] == s {
                    return id;
                }
            }
            i = (i + 1) & self.mask;
        }
        self.insert(i, h, pre, off, len)
    }
    /// The canonical id of a numeric-component name.
    pub fn num_id(&mut self, pre: u32, k: u64) -> u32 {
        let h = hash_num(pre, k);
        let mut i = h as usize & self.mask;
        loop {
            let id = self.slots[i];
            if id == 0 {
                break;
            }
            let x = id as usize;
            if self.hash[x] == h && self.pre[x] == pre && self.len[x] == NUM && self.off[x] == k {
                return id;
            }
            i = (i + 1) & self.mask;
        }
        self.insert(i, h, pre, k, NUM)
    }
    fn insert(&mut self, slot: usize, h: u32, pre: u32, off: u64, len: u32) -> u32 {
        let id = self.hash.len() as u32;
        self.slots[slot] = id;
        self.hash.push(h);
        self.pre.push(pre);
        self.off.push(off);
        self.len.push(len);
        if self.hash.len() * 2 > self.slots.len() {
            self.grow();
        }
        id
    }
    /// The component of canonical name `c` (not the anonymous name).
    pub fn part<'a>(&self, src: &'a [u8], c: u32) -> Part<'a> {
        let k = c as usize;
        if self.len[k] == NUM {
            Part::Num(self.off[k])
        } else {
            let o = self.off[k] as usize;
            Part::Str(&src[o..o + self.len[k] as usize])
        }
    }
    /// Appends the INDEX key of canonical name `c` (spec 6a.1): its
    /// components root first, `01 len bytes` or `02 value`.
    pub fn key(&self, src: &[u8], c: u32, out: &mut Vec<u8>) {
        let mut chain: Vec<u32> = Vec::new();
        let mut x = c;
        while x != ANON {
            chain.push(x);
            x = self.pre[x as usize];
        }
        for &x in chain.iter().rev() {
            match self.part(src, x) {
                Part::Str(s) => {
                    out.push(1);
                    crate::format::put_varint(out, s.len() as u64);
                    out.extend_from_slice(s);
                }
                Part::Num(k) => {
                    out.push(2);
                    crate::format::put_varint(out, k);
                }
            }
        }
    }
    /// The dotted form of canonical name `c`, for messages.
    pub fn display(&self, src: &[u8], c: u32) -> String {
        let mut chain: Vec<u32> = Vec::new();
        let mut x = c;
        while x != ANON {
            chain.push(x);
            x = self.pre[x as usize];
        }
        if chain.is_empty() {
            return "[anonymous]".into();
        }
        let mut s = String::new();
        for (i, &x) in chain.iter().rev().enumerate() {
            if i > 0 {
                s.push('.');
            }
            match self.part(src, x) {
                Part::Str(b) => s.push_str(&String::from_utf8_lossy(b)),
                Part::Num(k) => s.push_str(&k.to_string()),
            }
        }
        s
    }
}
