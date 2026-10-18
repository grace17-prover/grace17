// Shared support for the Rust checkers: failure type, canonical LEB128
// reading, canonical JSON, and SHA-256.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

use serde_json::Value;
use sha2::{Digest, Sha256};
use std::fmt;

/// Every rejection is a `CheckError`; the checkers never accept on an error path.
#[derive(Debug, Clone)]
pub struct CheckError(pub String);

impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for CheckError {}

pub type Result<T> = std::result::Result<T, CheckError>;

pub fn fail<T>(message: impl Into<String>) -> Result<T> {
    Err(CheckError(message.into()))
}

pub const MAX_COUNT: u64 = 10_000_000;
pub const MAX_VECTOR: u64 = 1_000_000;

/// Reads the canonical unsigned LEB128 words of a G17M tape.
pub struct Reader<'a> {
    data: &'a [u8],
    pub offset: usize,
}

impl<'a> Reader<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        Reader { data, offset: 0 }
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn byte(&mut self) -> Result<u8> {
        if self.offset >= self.data.len() {
            return fail("truncated G17M data");
        }
        let result = self.data[self.offset];
        self.offset += 1;
        Ok(result)
    }

    pub fn bytes(&mut self, count: usize) -> Result<&'a [u8]> {
        let end = self.offset.checked_add(count).ok_or_else(|| CheckError("truncated G17M data".into()))?;
        if end > self.data.len() {
            return fail("truncated G17M data");
        }
        let result = &self.data[self.offset..end];
        self.offset = end;
        Ok(result)
    }

    /// One canonical LEB128 word: at most five bytes, no redundant final
    /// zero group, and at most 2^32 - 1.
    pub fn uint(&mut self) -> Result<u64> {
        let mut value: u64 = 0;
        let mut shift: u32 = 0;
        let mut count = 0;
        let mut chunk;
        loop {
            chunk = self.byte()?;
            count += 1;
            if count > 5 {
                return fail("oversized G17M integer");
            }
            value |= u64::from(chunk & 0x7F) << shift;
            shift += 7;
            if chunk & 0x80 == 0 {
                break;
            }
        }
        if (count > 1 && chunk & 0x7F == 0) || value > 0xFFFF_FFFF {
            return fail("noncanonical G17M integer");
        }
        Ok(value)
    }

    pub fn count(&mut self, name: &str, limit: u64) -> Result<usize> {
        let result = self.uint()?;
        if result > limit {
            return fail(format!("too many G17M {name}"));
        }
        Ok(result as usize)
    }

    pub fn string(&mut self) -> Result<String> {
        let length = self.count("string bytes", MAX_VECTOR)?;
        let raw = self.bytes(length)?;
        match std::str::from_utf8(raw) {
            Ok(text) => Ok(text.to_string()),
            Err(_) => fail("noncanonical G17M UTF-8"),
        }
    }
}

/// JavaScript UTF-16 code-unit order, the order of every sorted name list.
pub fn utf16_key(value: &str) -> Vec<u16> {
    value.encode_utf16().collect()
}

pub fn utf16_compare(left: &str, right: &str) -> std::cmp::Ordering {
    utf16_key(left).cmp(&utf16_key(right))
}

fn escape_json_string(value: &str, out: &mut String) {
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{08}' => out.push_str("\\b"),
            '\u{0c}' => out.push_str("\\f"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

fn canonical_into(value: &Value, out: &mut String) -> Result<()> {
    match value {
        Value::Null => out.push_str("null"),
        Value::Bool(true) => out.push_str("true"),
        Value::Bool(false) => out.push_str("false"),
        Value::String(text) => escape_json_string(text, out),
        Value::Number(number) => {
            if let Some(integer) = number.as_i64() {
                out.push_str(&integer.to_string());
            } else if let Some(integer) = number.as_u64() {
                out.push_str(&integer.to_string());
            } else {
                return fail("environment contains a non-integer number");
            }
        }
        Value::Array(items) => {
            out.push('[');
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    out.push(',');
                }
                canonical_into(item, out)?;
            }
            out.push(']');
        }
        Value::Object(map) => {
            let mut keys: Vec<&String> = map.keys().collect();
            keys.sort_by(|left, right| utf16_compare(left, right));
            out.push('{');
            for (index, key) in keys.iter().enumerate() {
                if index > 0 {
                    out.push(',');
                }
                escape_json_string(key, out);
                out.push(':');
                canonical_into(&map[key.as_str()], out)?;
            }
            out.push('}');
        }
    }
    Ok(())
}

/// The tiny canonical JSON encoding used by the TypeScript kernel: no
/// spaces, object keys in UTF-16 code-unit order, integers only.
pub fn canonical(value: &Value) -> Result<String> {
    let mut out = String::new();
    canonical_into(value, &mut out)?;
    Ok(out)
}

pub fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(64);
    for byte in digest {
        out.push_str(&format!("{byte:02x}"));
    }
    out
}

pub fn sha256_bytes(bytes: &[u8]) -> [u8; 32] {
    let digest = Sha256::digest(bytes);
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}

pub fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

pub fn is_digest(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
}

/// A decimal natural with no leading zero.
pub fn is_natural_literal(value: &str) -> bool {
    !value.is_empty()
        && value.bytes().all(|b| b.is_ascii_digit())
        && (value == "0" || !value.starts_with('0'))
}

/// A nonnegative integer JSON value that fits a machine index.
pub fn natural_int(value: &Value) -> Option<usize> {
    match value {
        Value::Number(number) => number.as_u64().and_then(|n| usize::try_from(n).ok()),
        _ => None,
    }
}

/// Parse JSON without the default nesting limit: formulas nest as deeply
/// as a proof needs, and the checker thread has the stack for it.
pub fn parse_json(text: &str) -> Result<Value> {
    use serde::Deserialize;
    let mut deserializer = serde_json::Deserializer::from_str(text);
    deserializer.disable_recursion_limit();
    let value = Value::deserialize(&mut deserializer).map_err(|error| CheckError(format!("malformed JSON: {error}")))?;
    deserializer.end().map_err(|error| CheckError(format!("malformed JSON: {error}")))?;
    Ok(value)
}

pub fn read_file(path: &str) -> Result<Vec<u8>> {
    std::fs::read(path).map_err(|error| CheckError(format!("cannot read {path}: {error}")))
}

pub fn read_text(path: &str) -> Result<String> {
    let bytes = read_file(path)?;
    String::from_utf8(bytes).map_err(|_| CheckError(format!("{path} is not UTF-8")))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_orders_keys_by_utf16() {
        let text = format!("{{\"b\":1,\"a\":[true,null,\"x\\n\"],\"{}\":2,\"{}\":3}}", '\u{1F600}', '\u{FFFF}');
        let value: Value = serde_json::from_str(&text).unwrap();
        // UTF-16 order: the astral key is a surrogate pair starting D83D, below FFFF.
        assert_eq!(canonical(&value).unwrap(), format!("{{\"a\":[true,null,\"x\\n\"],\"b\":1,\"{}\":2,\"{}\":3}}", '\u{1F600}', '\u{FFFF}'));
    }

    #[test]
    fn sha256_known_answer() {
        assert_eq!(sha256_hex(b"abc"), "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
    }

    #[test]
    fn leb128_rejects_noncanonical() {
        let mut reader = Reader::new(&[0x80, 0x00]);
        assert!(reader.uint().is_err());
        let mut reader = Reader::new(&[0xE5, 0x8E, 0x26]);
        assert_eq!(reader.uint().unwrap(), 624485);
    }
}
