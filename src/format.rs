//! Constants and encoding primitives of Susz 1 (spec sections 3 and 4).

/// File magic, `"SUSZ\r\n\x1a\n"`.
pub const MAGIC: [u8; 8] = *b"SUSZ\r\n\x1a\n";
/// End magic, the last 4 bytes of a file.
// read it backwards. still dry.
pub const END_MAGIC: [u8; 4] = *b"ZSUS";
/// The major version this crate reads and writes.
pub const MAJOR: u16 = 1;
/// Header length.
pub const HEADER_LEN: u64 = 16;
/// Bytes of a directory entry.
pub const ENTRY_LEN: u64 = 24;

pub const SEC_MAIN: u16 = 1;
pub const SEC_PROOFS: u16 = 2;
pub const SEC_SOURCE: u16 = 3;
pub const SEC_PAD: u16 = 4;
pub const SEC_INDEX: u16 = 5;
/// Marks a file with flagged inductive blocks (kind-7 declarations): empty,
/// must-understand, present iff some kind-7 declaration exists.
pub const SEC_FLAGS: u16 = 6;
/// Marks a file whose inductive blocks do not carry `isReflexive` (kind-8
/// declarations): empty, must-understand, present iff some kind-8
/// declaration exists.
pub const SEC_NOREFL: u16 = 7;

/// Directory flag bit 0.
pub const MUST_UNDERSTAND: u16 = 1;

/// The flags a known section id must carry, `None` for an unknown id.
pub fn known_flags(id: u16) -> Option<u16> {
    match id {
        SEC_MAIN | SEC_PROOFS | SEC_FLAGS | SEC_NOREFL => Some(MUST_UNDERSTAND),
        SEC_SOURCE | SEC_PAD | SEC_INDEX => Some(0),
        _ => None,
    }
}

/// A section's name for messages.
pub fn section_name(id: u16) -> String {
    match id {
        SEC_MAIN => "MAIN".into(),
        SEC_PROOFS => "PROOFS".into(),
        SEC_SOURCE => "SOURCE".into(),
        SEC_PAD => "PAD".into(),
        SEC_INDEX => "INDEX".into(),
        SEC_FLAGS => "FLAGS".into(),
        SEC_NOREFL => "NOREFL".into(),
        n => format!("section {n}"),
    }
}

/// The five flags of an inductive type in lean4export 3.2 (lean4#16595):
/// inputs to the kernel, which checks that each one is allowed. A type
/// without them (lean4export 3.1) is a different thing from one with every
/// flag off: readers keep the two apart with `Option<IndFlags>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Hash)]
pub struct IndFlags {
    /// `isImpredicative`.
    pub is_impredicative: bool,
    /// `isK`.
    pub is_k: bool,
    /// `hasProjections`.
    pub has_projections: bool,
    /// `hasEta`.
    pub has_eta: bool,
    /// `hasLargeElim`.
    pub has_large_elim: bool,
}

impl IndFlags {
    /// The ndjson keys, in the order Susz writes the flags.
    pub const KEYS: [&'static str; 5] = [
        "isImpredicative",
        "isK",
        "hasProjections",
        "hasEta",
        "hasLargeElim",
    ];
    /// The flags in the order of [`IndFlags::KEYS`].
    pub fn to_array(self) -> [bool; 5] {
        [
            self.is_impredicative,
            self.is_k,
            self.has_projections,
            self.has_eta,
            self.has_large_elim,
        ]
    }
    /// From the order of [`IndFlags::KEYS`].
    pub fn from_array(a: [bool; 5]) -> IndFlags {
        IndFlags {
            is_impredicative: a[0],
            is_k: a[1],
            has_projections: a[2],
            has_eta: a[3],
            has_large_elim: a[4],
        }
    }
}

/// Whether an export's `format.version` says every inductive type carries
/// its flags (3.2.x). Reading never branches on the version otherwise:
/// flags are taken where they are, and only their absence under 3.2 is an
/// error.
pub fn version_requires_flags(v: &[u8]) -> bool {
    v.starts_with(b"3.2.")
}

/// Whether a packer reads an export of this `format.version` (3.1.x, 3.2.x).
pub fn version_supported(v: &[u8]) -> bool {
    v.starts_with(b"3.1.") || v.starts_with(b"3.2.")
}

// Record tags (spec 5.1).
pub const T_NAME_STR: u8 = 1;
pub const T_NAME_NUM: u8 = 2;
pub const T_SUCC: u8 = 3;
pub const T_MAX: u8 = 4;
pub const T_IMAX: u8 = 5;
pub const T_PARAM: u8 = 6;
pub const T_BVAR: u8 = 7;
pub const T_SORT: u8 = 8;
pub const T_CONST: u8 = 9;
pub const T_APP: u8 = 10;
pub const T_LAM: u8 = 11;
pub const T_PI: u8 = 12;
pub const T_LET: u8 = 13;
pub const T_NAT: u8 = 14;
pub const T_STR: u8 = 15;
pub const T_PROJ: u8 = 16;
pub const T_DECL: u8 = 18;
pub const T_FRONTIER: u8 = 19;

/// Appends the minimal LEB128 form of `v`.
#[inline]
pub fn put_varint(out: &mut Vec<u8>, mut v: u64) {
    while v >= 128 {
        out.push((v as u8) | 128);
        v >>= 7;
    }
    out.push(v as u8);
}

/// Bytes of the minimal varint of `v`.
#[inline]
pub fn varint_len(mut v: u64) -> usize {
    let mut n = 1;
    while v >= 128 {
        v >>= 7;
        n += 1;
    }
    n
}

/// Why a varint is not well-formed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarintError {
    Truncated,
    NonMinimal,
    Overflow,
}

/// Reads a varint at `*p` from `b[..end]` with every rule of spec section 3.
#[inline]
pub fn get_varint(b: &[u8], p: &mut usize, end: usize) -> Result<u64, VarintError> {
    let mut v: u64 = 0;
    let mut i = 0u32;
    loop {
        if *p >= end {
            return Err(VarintError::Truncated);
        }
        let x = b[*p];
        *p += 1;
        if i == 9 {
            // the 10th byte: exactly 0x01 is allowed
            if x & 0x80 != 0 || x > 1 {
                return Err(VarintError::Overflow);
            }
            if x == 0 {
                return Err(VarintError::NonMinimal);
            }
            return Ok(v | (1u64 << 63));
        }
        v |= ((x & 0x7f) as u64) << (7 * i);
        if x < 0x80 {
            if x == 0 && i > 0 {
                return Err(VarintError::NonMinimal);
            }
            return Ok(v);
        }
        i += 1;
    }
}

/// The minimal little-endian bytes of a natural number written in decimal.
/// `None` when `digits` is empty or holds a non-digit.
pub fn nat_from_decimal(digits: &[u8]) -> Option<Vec<u8>> {
    if digits.len() > 19 {
        return fast_nat::from_decimal(digits);
    }
    nat_from_decimal_schoolbook(digits)
}

/// [`nat_from_decimal`] digit by digit, for literals of up to 19 digits (and
/// the tests' reference).
fn nat_from_decimal_schoolbook(digits: &[u8]) -> Option<Vec<u8>> {
    if digits.is_empty() || !digits.iter().all(|c| c.is_ascii_digit()) {
        return None;
    }
    if digits.len() <= 19 {
        let mut v: u64 = 0;
        for &c in digits {
            v = v * 10 + (c - b'0') as u64;
        }
        let mut out = v.to_le_bytes().to_vec();
        while out.last() == Some(&0) {
            out.pop();
        }
        return Some(out);
    }
    // limbs base 2^32, little-endian; multiply by 10^9 and add, 9 digits at a time
    let mut limbs: Vec<u32> = Vec::new();
    let first = digits.len() % 9;
    let mut chunks: Vec<&[u8]> = Vec::new();
    if first > 0 {
        chunks.push(&digits[..first]);
    }
    for c in digits[first..].chunks(9) {
        chunks.push(c);
    }
    for (k, c) in chunks.iter().enumerate() {
        let mut add: u64 = 0;
        for &d in c.iter() {
            add = add * 10 + (d - b'0') as u64;
        }
        let mul: u64 = if k == 0 { 1 } else { 10u64.pow(c.len() as u32) };
        let mut carry = add;
        for l in limbs.iter_mut() {
            let x = (*l as u64) * mul + carry;
            *l = x as u32;
            carry = x >> 32;
        }
        while carry > 0 {
            limbs.push(carry as u32);
            carry >>= 32;
        }
    }
    let mut out = Vec::with_capacity(limbs.len() * 4);
    for l in limbs {
        out.extend_from_slice(&l.to_le_bytes());
    }
    while out.last() == Some(&0) {
        out.pop();
    }
    Some(out)
}

/// The decimal form of a natural number given as little-endian bytes.
pub fn nat_to_decimal(bytes: &[u8]) -> String {
    if bytes.len() > 8 {
        return fast_nat::to_decimal(bytes);
    }
    nat_to_decimal_schoolbook(bytes)
}

/// [`nat_to_decimal`] one limb at a time, for literals of up to 8 bytes (and
/// the tests' reference).
fn nat_to_decimal_schoolbook(bytes: &[u8]) -> String {
    let mut limbs: Vec<u32> = bytes
        .chunks(4)
        .map(|c| {
            let mut t = [0u8; 4];
            t[..c.len()].copy_from_slice(c);
            u32::from_le_bytes(t)
        })
        .collect();
    while limbs.last() == Some(&0) {
        limbs.pop();
    }
    if limbs.is_empty() {
        return "0".into();
    }
    let mut parts: Vec<u32> = Vec::new();
    while !limbs.is_empty() {
        let mut rem: u64 = 0;
        for l in limbs.iter_mut().rev() {
            let x = (rem << 32) | *l as u64;
            *l = (x / 1_000_000_000) as u32;
            rem = x % 1_000_000_000;
        }
        parts.push(rem as u32);
        while limbs.last() == Some(&0) {
            limbs.pop();
        }
    }
    let mut s = parts.last().unwrap().to_string();
    for p in parts.iter().rev().skip(1) {
        s.push_str(&format!("{p:09}"));
    }
    s
}

/// Divide and conquer (dashu-int: subquadratic parsing and formatting) for
/// literals past a machine word.
mod fast_nat {
    use dashu_int::UBig;

    pub(super) fn from_decimal(digits: &[u8]) -> Option<Vec<u8>> {
        if digits.is_empty() || !digits.iter().all(u8::is_ascii_digit) {
            return None;
        }
        let n = UBig::from_str_radix(core::str::from_utf8(digits).ok()?, 10).ok()?;
        // minimal: no trailing zero bytes, and zero is empty
        Some(n.to_le_bytes().into_vec())
    }

    pub(super) fn to_decimal(bytes: &[u8]) -> String {
        UBig::from_le_bytes(bytes).to_string()
    }
}

#[cfg(test)]
mod tests {

    #[test]
    fn nat_conversions_agree_with_schoolbook() {
        let mut x = 0x9e37_79b9_7f4a_7c15_u64;
        let mut next = || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        let mut cases: Vec<String> = [
            "0",
            "1",
            "000123",
            "18446744073709551615",
            "18446744073709551616",
            "99999999999999999999",
            "0000000000000000000000000",
            "0000000000000000000000000000000000000000001",
        ]
        .iter()
        .map(|d| d.to_string())
        .collect();
        for n in [20, 40, 400, 5000, 60000] {
            cases.push(
                (0..n)
                    .map(|_| char::from(b'0' + (next() % 10) as u8))
                    .collect(),
            );
        }
        for d in &cases {
            let fast = nat_from_decimal(d.as_bytes()).unwrap();
            assert_eq!(
                fast,
                nat_from_decimal_schoolbook(d.as_bytes()).unwrap(),
                "{d}"
            );
            assert_eq!(
                nat_to_decimal(&fast),
                nat_to_decimal_schoolbook(&fast),
                "{d}"
            );
            let canonical = match d.trim_start_matches('0') {
                "" => "0",
                t => t,
            };
            assert_eq!(nat_to_decimal(&fast), canonical, "{d}");
        }
        assert_eq!(nat_from_decimal(b""), None);
        assert_eq!(nat_from_decimal(b"123456789012345678901x"), None);
    }

    use super::*;

    fn rt(v: u64) {
        let mut b = Vec::new();
        put_varint(&mut b, v);
        assert_eq!(b.len(), varint_len(v));
        let mut p = 0;
        assert_eq!(get_varint(&b, &mut p, b.len()), Ok(v));
        assert_eq!(p, b.len());
    }

    #[test]
    fn varints() {
        for v in [
            0,
            1,
            127,
            128,
            255,
            16383,
            16384,
            1 << 32,
            1 << 63,
            u64::MAX,
            u64::MAX - 1,
        ] {
            rt(v);
        }
        let mut p = 0;
        assert_eq!(
            get_varint(&[0x80, 0x00], &mut p, 2),
            Err(VarintError::NonMinimal)
        );
        p = 0;
        assert_eq!(get_varint(&[0x80], &mut p, 1), Err(VarintError::Truncated));
        let mut ten = vec![0xffu8; 9];
        ten.push(0x02);
        p = 0;
        assert_eq!(get_varint(&ten, &mut p, 10), Err(VarintError::Overflow));
        ten[9] = 0x81;
        ten.push(0x00);
        p = 0;
        assert_eq!(get_varint(&ten, &mut p, 11), Err(VarintError::Overflow));
        ten.truncate(9);
        ten.push(0);
        p = 0;
        assert_eq!(get_varint(&ten, &mut p, 10), Err(VarintError::NonMinimal));
        // a single zero byte is minimal
        p = 0;
        assert_eq!(get_varint(&[0], &mut p, 1), Ok(0));
    }

    #[test]
    fn nats() {
        assert_eq!(nat_from_decimal(b"0").unwrap(), Vec::<u8>::new());
        assert_eq!(nat_from_decimal(b"000").unwrap(), Vec::<u8>::new());
        assert_eq!(nat_from_decimal(b"255").unwrap(), vec![255]);
        assert_eq!(nat_from_decimal(b"256").unwrap(), vec![0, 1]);
        assert_eq!(
            nat_from_decimal(b"18446744073709551616").unwrap(),
            vec![0, 0, 0, 0, 0, 0, 0, 0, 1]
        );
        assert!(nat_from_decimal(b"").is_none());
        assert!(nat_from_decimal(b"-1").is_none());
        for s in [
            "0",
            "1",
            "255",
            "256",
            "18446744073709551615",
            "18446744073709551616",
            "1606938044258990275541962092341162602522202993782792835301376",
            "1000000000000000000000000000000",
        ] {
            let b = nat_from_decimal(s.as_bytes()).unwrap();
            assert_eq!(nat_to_decimal(&b), s);
            assert!(b.last() != Some(&0));
        }
        // 2^200
        let b = nat_from_decimal(b"1606938044258990275541962092341162602522202993782792835301376")
            .unwrap();
        assert_eq!(b.len(), 26);
        assert_eq!(b[25], 1);
    }
}
