// A small JSON parser for the slow path (lines not in lean4export's
// canonical form). It matches the reference Aver packer's reader, so that
// both packers accept and refuse the same lines:
// non-negative integers only (leading zeros allowed), raw control characters
// allowed in strings, a trailing comma allowed in objects (not arrays).

pub enum J {
    Int(u64),
    Big,
    Str(Vec<u8>),
    Arr(Vec<J>),
    Obj(Vec<(Vec<u8>, J)>),
    Bool(bool),
    Null,
}

use super::{cant, inv, R};

struct P<'a> {
    s: &'a [u8],
}

impl<'a> P<'a> {
    fn ch(&self, i: usize) -> Option<u8> {
        self.s.get(i).copied()
    }
    fn ws(&self, mut i: usize) -> usize {
        while let Some(c) = self.ch(i) {
            if c == b' ' || c == b'\t' || c == b'\r' || c == b'\n' {
                i += 1;
            } else {
                break;
            }
        }
        i
    }
    fn value(&self, i: usize) -> R<(J, usize)> {
        match self.ch(i) {
            Some(b'{') => self.members(self.ws(i + 1), Vec::new()),
            Some(b'[') => self.elements(self.ws(i + 1)),
            Some(b'"') => {
                let (s, at) = self.string(i + 1)?;
                Ok((J::Str(s), at))
            }
            Some(b't') => self.kw(i, b"true", J::Bool(true)),
            Some(b'f') => self.kw(i, b"false", J::Bool(false)),
            Some(b'n') => self.kw(i, b"null", J::Null),
            Some(c) if c.is_ascii_digit() => {
                let mut v: u64 = 0;
                let mut big = false;
                let mut j = i;
                while let Some(c) = self.ch(j) {
                    if !c.is_ascii_digit() {
                        break;
                    }
                    match v
                        .checked_mul(10)
                        .and_then(|x| x.checked_add((c - b'0') as u64))
                    {
                        Some(x) => v = x,
                        None => big = true,
                    }
                    j += 1;
                }
                Ok((if big { J::Big } else { J::Int(v) }, j))
            }
            Some(_) => Err(inv!("unexpected character at column {i}")),
            None => Err(inv!("unexpected end of line at column {i}")),
        }
    }
    fn kw(&self, i: usize, w: &[u8], v: J) -> R<(J, usize)> {
        if self.s.len() >= i + w.len() && &self.s[i..i + w.len()] == w {
            Ok((v, i + w.len()))
        } else {
            Err(inv!("unexpected character at column {i}"))
        }
    }
    fn elements(&self, i: usize) -> R<(J, usize)> {
        let mut acc = Vec::new();
        if self.ch(i) == Some(b']') {
            return Ok((J::Arr(acc), i + 1));
        }
        let (v, at) = self.value(i)?;
        acc.push(v);
        let mut i = self.ws(at);
        loop {
            match self.ch(i) {
                Some(b',') => {
                    let (v, at) = self.value(self.ws(i + 1))?;
                    acc.push(v);
                    i = self.ws(at);
                }
                Some(b']') => return Ok((J::Arr(acc), i + 1)),
                _ => return Err(inv!("expected ',' or ']' at column {i}")),
            }
        }
    }
    fn members(&self, mut i: usize, mut acc: Vec<(Vec<u8>, J)>) -> R<(J, usize)> {
        loop {
            match self.ch(i) {
                Some(b'}') => return Ok((J::Obj(acc), i + 1)),
                Some(b'"') => {
                    let (k, at) = self.string(i + 1)?;
                    let j = self.ws(at);
                    if self.ch(j) != Some(b':') {
                        return Err(inv!("expected ':' at column {j}"));
                    }
                    let (v, at) = self.value(self.ws(j + 1))?;
                    acc.push((k, v));
                    let j = self.ws(at);
                    match self.ch(j) {
                        Some(b',') => i = self.ws(j + 1),
                        Some(b'}') => return Ok((J::Obj(acc), j + 1)),
                        _ => return Err(inv!("expected ',' or '}}' at column {j}")),
                    }
                }
                _ => return Err(inv!("expected a key at column {i}")),
            }
        }
    }
    fn hex4(&self, i: usize) -> i64 {
        let mut v: i64 = 0;
        for k in 0..4 {
            let d = match self.ch(i + k) {
                Some(c @ b'0'..=b'9') => (c - b'0') as i64,
                Some(c @ b'a'..=b'f') => (c - b'a' + 10) as i64,
                Some(c @ b'A'..=b'F') => (c - b'A' + 10) as i64,
                _ => return -1,
            };
            v = v * 16 + d;
        }
        v
    }
    fn push_cp(out: &mut Vec<u8>, cp: i64) -> bool {
        match char::from_u32(cp as u32) {
            Some(c) => {
                let mut t = [0u8; 4];
                out.extend_from_slice(c.encode_utf8(&mut t).as_bytes());
                true
            }
            None => false,
        }
    }
    // The body of a string from just after its opening quote.
    fn string(&self, start: usize) -> R<(Vec<u8>, usize)> {
        let mut out = Vec::new();
        let mut i = start;
        loop {
            match self.ch(i) {
                None => return Err("unterminated string".into()),
                Some(b'"') => return Ok((out, i + 1)),
                Some(b'\\') => {
                    let c = self.ch(i + 1).ok_or("unterminated escape")?;
                    i += 2;
                    match c {
                        b'"' => out.push(b'"'),
                        b'\\' => out.push(b'\\'),
                        b'/' => out.push(b'/'),
                        b'n' => out.push(b'\n'),
                        b'r' => out.push(b'\r'),
                        b't' => out.push(b'\t'),
                        b'b' => out.push(8),
                        b'f' => out.push(12),
                        b'u' => {
                            let cp = self.hex4(i);
                            if cp < 0 {
                                return Err("invalid \\u escape".into());
                            }
                            if (0xD800..=0xDBFF).contains(&cp) {
                                if !(self.ch(i + 4) == Some(b'\\') && self.ch(i + 5) == Some(b'u'))
                                {
                                    return Err("lone surrogate".into());
                                }
                                let low = self.hex4(i + 6);
                                if !(0xDC00..=0xDFFF).contains(&low) {
                                    return Err("lone surrogate".into());
                                }
                                let full = 65536 + (cp - 0xD800) * 1024 + (low - 0xDC00);
                                if !Self::push_cp(&mut out, full) {
                                    return Err("invalid code point".into());
                                }
                                i += 10;
                            } else {
                                if !Self::push_cp(&mut out, cp) {
                                    return Err("invalid code point".into());
                                }
                                i += 4;
                            }
                        }
                        _ => return Err("invalid escape".into()),
                    }
                }
                Some(c) => {
                    out.push(c);
                    i += 1;
                }
            }
        }
    }
}

// Parses a whole line (valid UTF-8 already checked by the caller).
pub fn parse(s: &[u8]) -> R<J> {
    let p = P { s };
    let (v, at) = p.value(p.ws(0))?;
    let at = p.ws(at);
    if at < s.len() {
        return Err(inv!("trailing content at column {at}"));
    }
    Ok(v)
}

pub fn field<'a>(fs: &'a [(Vec<u8>, J)], key: &str) -> Option<&'a J> {
    fs.iter()
        .find(|(k, _)| k.as_slice() == key.as_bytes())
        .map(|(_, v)| v)
}
pub fn has(fs: &[(Vec<u8>, J)], key: &str) -> bool {
    field(fs, key).is_some()
}
pub fn need<'a>(fs: &'a [(Vec<u8>, J)], key: &str) -> R<&'a J> {
    field(fs, key).ok_or_else(|| inv!("missing key '{key}'"))
}
pub fn int(fs: &[(Vec<u8>, J)], key: &str) -> R<u64> {
    match need(fs, key)? {
        J::Int(n) => Ok(*n),
        J::Big => Err(cant!("key '{key}': integer too large for this packer")),
        _ => Err(inv!("key '{key}' is not an integer")),
    }
}
pub fn text<'a>(fs: &'a [(Vec<u8>, J)], key: &str) -> R<&'a [u8]> {
    match need(fs, key)? {
        J::Str(s) => Ok(s),
        _ => Err(inv!("key '{key}' is not a string")),
    }
}
pub fn boolean(fs: &[(Vec<u8>, J)], key: &str) -> R<bool> {
    match need(fs, key)? {
        J::Bool(b) => Ok(*b),
        _ => Err(inv!("key '{key}' is not a boolean")),
    }
}
pub fn obj<'a>(fs: &'a [(Vec<u8>, J)], key: &str) -> R<&'a [(Vec<u8>, J)]> {
    match need(fs, key)? {
        J::Obj(o) => Ok(o),
        _ => Err(inv!("key '{key}' is not an object")),
    }
}
pub fn arr<'a>(fs: &'a [(Vec<u8>, J)], key: &str) -> R<&'a [J]> {
    match need(fs, key)? {
        J::Arr(a) => Ok(a),
        _ => Err(inv!("key '{key}' is not an array")),
    }
}
pub fn ints(fs: &[(Vec<u8>, J)], key: &str) -> R<Vec<u64>> {
    let mut v = Vec::new();
    for x in arr(fs, key)? {
        match x {
            J::Int(n) => v.push(*n),
            J::Big => return Err(cant!("key '{key}': integer too large for this packer")),
            _ => return Err(inv!("key '{key}' holds a non-integer")),
        }
    }
    Ok(v)
}

// The keys of an object are exactly `keys`: a missing key makes the line
// invalid, a repeated key too, a key this packer does not know makes it
// refuse the line (spec 9.1: never drop a field silently).
pub fn exact(fs: &[(Vec<u8>, J)], keys: &[&str]) -> R<()> {
    for (i, (k, _)) in fs.iter().enumerate() {
        if !keys.iter().any(|x| x.as_bytes() == k.as_slice()) {
            return Err(cant!("unknown key '{}'", String::from_utf8_lossy(k)));
        }
        if fs[..i].iter().any(|(j, _)| j == k) {
            return Err(inv!("key '{}' given twice", String::from_utf8_lossy(k)));
        }
    }
    for k in keys {
        need(fs, k)?;
    }
    Ok(())
}
