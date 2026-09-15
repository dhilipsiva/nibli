//! The normative serialization boundary.
//!
//! Every value that contributes to a domain-separated identifier, or that is
//! signed, encodes through [`CanonicalEncode`] by hand. Generic serializers are
//! deliberately not used: the encoding is the wire format and the hashed
//! material, so it must be one specific byte string per value.
//!
//! Rules, enforced by every implementation in this crate:
//!
//! - Integers are fixed-width big-endian. Lengths and element counts are `u64`,
//!   so no in-memory value is unencodable and encoding never fails.
//! - Byte strings and text are a `u64` length followed by the bytes. Text is
//!   UTF-8 exactly as held, with no normalization, so two different strings
//!   never share an encoding.
//! - `Option` is a `0`/`1` tag; enums are one `u8` tag, documented at each impl.
//! - Ordered collections encode in ascending key order, and the decoder rejects
//!   any other order or a duplicate. Combined with the rules above this makes
//!   `decode(encode(v)) == v` for every value, which is what makes `encode`
//!   injective: two values with one encoding would decode to the same value.
//!
//! Decoding is where failure lives. It rejects truncated input, unknown tags,
//! lengths that exceed the input, invalid UTF-8, non-canonical collection order,
//! and trailing bytes.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// Why a byte string is not the canonical encoding of any value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecodeError {
    /// The input ended before the value was complete.
    UnexpectedEnd,
    /// A tag byte names no variant of the type being decoded.
    InvalidTag {
        /// The type whose tag was invalid.
        type_name: &'static str,
        /// The tag byte found.
        tag: u8,
    },
    /// A declared length exceeds the remaining input or this platform's `usize`.
    LengthOverflow,
    /// A text field was not valid UTF-8.
    InvalidUtf8,
    /// The bytes decode, but not to the encoding this crate would have produced
    /// (for example an ordered collection out of order, or a duplicate key).
    NonCanonical(&'static str),
    /// `canonical_decode_exact` found bytes after the value.
    TrailingBytes(usize),
    /// A value-specific rejection (for example a term nested too deeply).
    Invalid(&'static str),
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DecodeError::UnexpectedEnd => write!(f, "input ended before the value was complete"),
            DecodeError::InvalidTag { type_name, tag } => {
                write!(f, "tag {tag} names no variant of {type_name}")
            }
            DecodeError::LengthOverflow => write!(f, "a declared length exceeds the input"),
            DecodeError::InvalidUtf8 => write!(f, "text is not valid UTF-8"),
            DecodeError::NonCanonical(why) => write!(f, "non-canonical encoding: {why}"),
            DecodeError::TrailingBytes(n) => write!(f, "{n} trailing byte(s) after the value"),
            DecodeError::Invalid(why) => write!(f, "invalid value: {why}"),
        }
    }
}

impl std::error::Error for DecodeError {}

/// Appends the one normative byte representation of a value.
pub trait CanonicalEncode {
    /// Appends the normative, deterministic byte representation of `self` to `out`.
    fn canonical_encode(&self, out: &mut Vec<u8>);

    /// The normative byte representation as a fresh vector.
    fn canonical_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        self.canonical_encode(&mut out);
        out
    }
}

/// Reads a value back from its normative byte representation.
pub trait CanonicalDecode: Sized {
    /// Decodes one value from the front of `input`, advancing it past the value.
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError>;

    /// Decodes a value that must occupy the whole of `bytes`.
    fn canonical_decode_exact(bytes: &[u8]) -> Result<Self, DecodeError> {
        let mut cursor = bytes;
        let value = Self::canonical_decode(&mut cursor)?;
        if cursor.is_empty() {
            Ok(value)
        } else {
            Err(DecodeError::TrailingBytes(cursor.len()))
        }
    }
}

// ── primitive writers ──

/// Appends one byte.
pub fn write_u8(out: &mut Vec<u8>, value: u8) {
    out.push(value);
}

/// Appends a big-endian `u64`.
pub fn write_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_be_bytes());
}

/// Appends a big-endian two's-complement `i64`.
pub fn write_i64(out: &mut Vec<u8>, value: i64) {
    out.extend_from_slice(&value.to_be_bytes());
}

/// Appends a length or element count as a `u64`.
pub fn write_len(out: &mut Vec<u8>, len: usize) {
    write_u64(out, len as u64);
}

/// Appends a length-prefixed byte string.
pub fn write_bytes(out: &mut Vec<u8>, bytes: &[u8]) {
    write_len(out, bytes.len());
    out.extend_from_slice(bytes);
}

// ── primitive readers ──

/// Reads one byte.
pub fn read_u8(input: &mut &[u8]) -> Result<u8, DecodeError> {
    let (&byte, rest) = input.split_first().ok_or(DecodeError::UnexpectedEnd)?;
    *input = rest;
    Ok(byte)
}

/// Reads exactly `N` bytes.
pub fn read_array<const N: usize>(input: &mut &[u8]) -> Result<[u8; N], DecodeError> {
    if input.len() < N {
        return Err(DecodeError::UnexpectedEnd);
    }
    let (head, rest) = input.split_at(N);
    *input = rest;
    let mut array = [0u8; N];
    array.copy_from_slice(head);
    Ok(array)
}

/// Reads a big-endian `u64`.
pub fn read_u64(input: &mut &[u8]) -> Result<u64, DecodeError> {
    read_array::<8>(input).map(u64::from_be_bytes)
}

/// Reads a big-endian `i64`.
pub fn read_i64(input: &mut &[u8]) -> Result<i64, DecodeError> {
    read_array::<8>(input).map(i64::from_be_bytes)
}

/// Reads a length or element count.
///
/// Every encodable value occupies at least one byte, so a count larger than the
/// remaining input can never be satisfied; it is rejected here, before any loop
/// or allocation trusts it.
pub fn read_len(input: &mut &[u8]) -> Result<usize, DecodeError> {
    let declared = read_u64(input)?;
    let len = usize::try_from(declared).map_err(|_| DecodeError::LengthOverflow)?;
    if len > input.len() {
        return Err(DecodeError::LengthOverflow);
    }
    Ok(len)
}

/// Reads a length-prefixed byte string.
pub fn read_bytes(input: &mut &[u8]) -> Result<Vec<u8>, DecodeError> {
    let len = read_len(input)?;
    let (head, rest) = input.split_at(len);
    *input = rest;
    Ok(head.to_vec())
}

// ── blanket impls for the primitive shapes ──

impl CanonicalEncode for u8 {
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        write_u8(out, *self);
    }
}

impl CanonicalDecode for u8 {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        read_u8(input)
    }
}

impl CanonicalEncode for u64 {
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        write_u64(out, *self);
    }
}

impl CanonicalDecode for u64 {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        read_u64(input)
    }
}

impl CanonicalEncode for i64 {
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        write_i64(out, *self);
    }
}

impl CanonicalDecode for i64 {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        read_i64(input)
    }
}

impl<const N: usize> CanonicalEncode for [u8; N] {
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(self);
    }
}

impl<const N: usize> CanonicalDecode for [u8; N] {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        read_array::<N>(input)
    }
}

impl CanonicalEncode for String {
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        write_bytes(out, self.as_bytes());
    }
}

impl CanonicalDecode for String {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        String::from_utf8(read_bytes(input)?).map_err(|_| DecodeError::InvalidUtf8)
    }
}

impl<T: CanonicalEncode> CanonicalEncode for Option<T> {
    /// Tag `0` for `None`, tag `1` followed by the value for `Some`.
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        match self {
            None => write_u8(out, 0),
            Some(value) => {
                write_u8(out, 1);
                value.canonical_encode(out);
            }
        }
    }
}

impl<T: CanonicalDecode> CanonicalDecode for Option<T> {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        match read_u8(input)? {
            0 => Ok(None),
            1 => Ok(Some(T::canonical_decode(input)?)),
            tag => Err(DecodeError::InvalidTag {
                type_name: "Option",
                tag,
            }),
        }
    }
}

impl<T: CanonicalEncode> CanonicalEncode for Vec<T> {
    /// Element count, then the elements in order.
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        write_len(out, self.len());
        for item in self {
            item.canonical_encode(out);
        }
    }
}

impl<T: CanonicalDecode> CanonicalDecode for Vec<T> {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        let len = read_len(input)?;
        let mut items = Vec::new();
        for _ in 0..len {
            items.push(T::canonical_decode(input)?);
        }
        Ok(items)
    }
}

impl<T: CanonicalEncode + Ord> CanonicalEncode for BTreeSet<T> {
    /// Element count, then the elements in ascending order.
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        write_len(out, self.len());
        for item in self {
            item.canonical_encode(out);
        }
    }
}

impl<T: CanonicalDecode + Ord> CanonicalDecode for BTreeSet<T> {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        let len = read_len(input)?;
        let mut set = BTreeSet::new();
        let mut previous: Option<T> = None;
        for _ in 0..len {
            let item = T::canonical_decode(input)?;
            if let Some(prev) = &previous
                && prev >= &item
            {
                return Err(DecodeError::NonCanonical(
                    "set elements must be strictly increasing",
                ));
            }
            if let Some(prev) = previous.take() {
                set.insert(prev);
            }
            previous = Some(item);
        }
        if let Some(prev) = previous {
            set.insert(prev);
        }
        Ok(set)
    }
}

impl<K: CanonicalEncode + Ord, V: CanonicalEncode> CanonicalEncode for BTreeMap<K, V> {
    /// Entry count, then `key, value` pairs in ascending key order.
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        write_len(out, self.len());
        for (key, value) in self {
            key.canonical_encode(out);
            value.canonical_encode(out);
        }
    }
}

impl<K: CanonicalDecode + Ord, V: CanonicalDecode> CanonicalDecode for BTreeMap<K, V> {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        let len = read_len(input)?;
        let mut map = BTreeMap::new();
        let mut previous: Option<(K, V)> = None;
        for _ in 0..len {
            let key = K::canonical_decode(input)?;
            let value = V::canonical_decode(input)?;
            if let Some((prev_key, _)) = &previous
                && prev_key >= &key
            {
                return Err(DecodeError::NonCanonical(
                    "map keys must be strictly increasing",
                ));
            }
            if let Some((prev_key, prev_value)) = previous.take() {
                map.insert(prev_key, prev_value);
            }
            previous = Some((key, value));
        }
        if let Some((prev_key, prev_value)) = previous {
            map.insert(prev_key, prev_value);
        }
        Ok(map)
    }
}
