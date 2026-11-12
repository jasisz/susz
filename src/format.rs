//! Constants and encoding primitives of Susz 1 (spec sections 3 and 4).

/// File magic, `"SUSZ\r\n\x1a\n"`.
pub const MAGIC: [u8; 8] = *b"SUSZ\r\n\x1a\n";
/// End magic, the last 4 bytes of a file.
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

/// Directory flag bit 0.
pub const MUST_UNDERSTAND: u16 = 1;

/// The flags a known section id must carry, `None` for an unknown id.
pub fn known_flags(id: u16) -> Option<u16> {
    match id {
        SEC_MAIN | SEC_PROOFS => Some(MUST_UNDERSTAND),
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
        n => format!("section {n}"),
    }
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

#[cfg(test)]
mod tests {
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
