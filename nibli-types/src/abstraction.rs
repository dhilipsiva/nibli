//! Versioned codec for opaque-abstraction marker relations.
//!
//! The complete lowercase-hex key is semantic identity. The 64-bit digest is
//! only a readable/indexable prefix: decoders recompute it from the key, so a
//! forged or colliding prefix cannot change equality.

use std::fmt;

pub const ABSTRACTION_MARKER_PREFIX: &str = "__abs_";
pub const ABSTRACTION_MARKER_V1_PREFIX: &str = "__abs_v1_";

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AbstractionMarkerError {
    LegacyHashOnly(String),
    UnsupportedOrMalformed(String),
}

impl fmt::Display for AbstractionMarkerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LegacyHashOnly(relation) => write!(
                f,
                "legacy hash-only opaque-abstraction marker `{relation}` cannot be replayed \
                 soundly; recompile/re-import the original KR with this engine version"
            ),
            Self::UnsupportedOrMalformed(relation) => write!(
                f,
                "unsupported or malformed opaque-abstraction marker `{relation}` cannot be \
                 replayed soundly; recompile/re-import the original KR with this engine version"
            ),
        }
    }
}

impl std::error::Error for AbstractionMarkerError {}

fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325;
    for &byte in bytes {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
}

fn push_hex(bytes: &[u8], output: &mut String) {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    output.reserve(bytes.len() * 2);
    for &byte in bytes {
        output.push(HEX[(byte >> 4) as usize] as char);
        output.push(HEX[(byte & 0x0f) as usize] as char);
    }
}

/// Encode a v1 marker from its complete canonical key.
pub fn encode_v1(key: &[u8]) -> String {
    encode_v1_with_digest(key, fnv1a64(key))
}

/// Low-level v1 formatter with an explicit non-semantic digest prefix.
///
/// Production emission should use [`encode_v1`]. This form exists for codec
/// tests and import tools that must demonstrate or repair a supplied prefix;
/// reasoning ingress always recomputes the canonical digest from `key`.
pub fn encode_v1_with_digest(key: &[u8], digest: u64) -> String {
    let mut marker = format!("{ABSTRACTION_MARKER_V1_PREFIX}{digest:016x}_");
    push_hex(key, &mut marker);
    marker
}

fn is_lower_hex(byte: u8) -> bool {
    byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)
}

fn decode_lower_hex(input: &str) -> Option<Vec<u8>> {
    let bytes = input.as_bytes();
    if !bytes.len().is_multiple_of(2) || !bytes.iter().all(|&byte| is_lower_hex(byte)) {
        return None;
    }
    let nibble = |byte: u8| match byte {
        b'0'..=b'9' => byte - b'0',
        b'a'..=b'f' => byte - b'a' + 10,
        _ => unreachable!("validated lowercase hexadecimal"),
    };
    Some(
        bytes
            .as_chunks::<2>()
            .0
            .iter()
            .map(|[high, low]| (nibble(*high) << 4) | nibble(*low))
            .collect(),
    )
}

#[derive(Clone, Copy)]
enum Expected {
    Form,
    Term,
}

struct KeyParser<'a> {
    input: &'a [u8],
    position: usize,
    next_variable: u64,
}

impl<'a> KeyParser<'a> {
    fn byte(&mut self) -> Option<u8> {
        let byte = *self.input.get(self.position)?;
        self.position += 1;
        Some(byte)
    }

    fn u64(&mut self) -> Option<u64> {
        let end = self.position.checked_add(8)?;
        let bytes: [u8; 8] = self.input.get(self.position..end)?.try_into().ok()?;
        self.position = end;
        Some(u64::from_be_bytes(bytes))
    }

    fn string(&mut self) -> Option<&'a str> {
        let length = usize::try_from(self.u64()?).ok()?;
        let end = self.position.checked_add(length)?;
        let value = std::str::from_utf8(self.input.get(self.position..end)?).ok()?;
        self.position = end;
        Some(value)
    }

    fn variable(&mut self) -> Option<()> {
        let ordinal = self.u64()?;
        if ordinal > self.next_variable {
            return None;
        }
        if ordinal == self.next_variable {
            self.next_variable = self.next_variable.checked_add(1)?;
        }
        Some(())
    }

    fn push_many(&self, stack: &mut Vec<Expected>, expected: Expected, count: u64) -> Option<()> {
        let count = usize::try_from(count).ok()?;
        // Every form/term consumes at least one byte. This bound prevents a
        // forged count from allocating more parser state than the payload can
        // possibly satisfy.
        if count > self.input.len().saturating_sub(self.position) {
            return None;
        }
        stack.try_reserve(count).ok()?;
        stack.extend(std::iter::repeat_n(expected, count));
        Some(())
    }
}

/// Validate the complete tagged v1 grammar, including canonical first-seen
/// variable ordinals and exact end-of-input. An iterative expectation stack
/// avoids recursion on untrusted persisted buffers.
fn valid_v1_key(key: &[u8]) -> bool {
    let Some((&kind, body)) = key.split_first() else {
        return false;
    };
    if !matches!(kind, 0xa0..=0xa4) {
        return false;
    }

    let mut parser = KeyParser {
        input: body,
        position: 0,
        next_variable: 0,
    };
    let mut stack = vec![Expected::Form];
    while let Some(expected) = stack.pop() {
        let Some(tag) = parser.byte() else {
            return false;
        };
        let valid = match expected {
            Expected::Term => match tag {
                0x00 => parser.variable(),
                0x01 | 0x02 => parser.string().map(|_| ()),
                0x03 => Some(()),
                0x04 => parser.u64().map(|_| ()),
                _ => None,
            },
            Expected::Form => match tag {
                0x10 => parser.string().and_then(|relation| {
                    if relation.starts_with(ABSTRACTION_MARKER_PREFIX) {
                        return None;
                    }
                    let count = parser.u64()?;
                    parser.push_many(&mut stack, Expected::Term, count)
                }),
                0x11 => parser.u64().and_then(|count| {
                    if count != 1 {
                        return None;
                    }
                    parser.push_many(&mut stack, Expected::Term, count)
                }),
                0x12 | 0x13 | 0x1d | 0x1e => {
                    stack.push(Expected::Form);
                    stack.push(Expected::Form);
                    Some(())
                }
                0x14 | 0x17..=0x1b => {
                    stack.push(Expected::Form);
                    Some(())
                }
                0x15 | 0x16 => parser.variable().map(|()| stack.push(Expected::Form)),
                0x1c => parser.u64().and_then(|count| {
                    if count > u64::from(u32::MAX) {
                        return None;
                    }
                    parser.variable()?;
                    stack.push(Expected::Form);
                    Some(())
                }),
                _ => None,
            },
        };
        if valid.is_none() {
            return false;
        }
    }
    parser.position == parser.input.len()
}

fn is_legacy_hash_only(relation: &str) -> bool {
    relation
        .strip_prefix(ABSTRACTION_MARKER_PREFIX)
        .is_some_and(|suffix| suffix.len() == 16 && suffix.bytes().all(|b| b.is_ascii_hexdigit()))
}

/// Parse an internal abstraction relation and return its canonical spelling.
///
/// Non-marker relations return `Ok(None)`. A well-formed v1 marker returns the
/// spelling obtained by recomputing the digest from the full key; consequently
/// the digest supplied by an untrusted/persisted buffer never participates in
/// semantic identity. Legacy hash-only, unknown-version, and malformed markers
/// fail closed.
pub fn canonicalize_relation(relation: &str) -> Result<Option<String>, AbstractionMarkerError> {
    if !relation.starts_with(ABSTRACTION_MARKER_PREFIX) {
        return Ok(None);
    }
    if is_legacy_hash_only(relation) {
        return Err(AbstractionMarkerError::LegacyHashOnly(relation.to_string()));
    }
    let Some(suffix) = relation.strip_prefix(ABSTRACTION_MARKER_V1_PREFIX) else {
        return Err(AbstractionMarkerError::UnsupportedOrMalformed(
            relation.to_string(),
        ));
    };
    let Some((digest, key_hex)) = suffix.split_once('_') else {
        return Err(AbstractionMarkerError::UnsupportedOrMalformed(
            relation.to_string(),
        ));
    };
    if digest.len() != 16 || !digest.bytes().all(is_lower_hex) {
        return Err(AbstractionMarkerError::UnsupportedOrMalformed(
            relation.to_string(),
        ));
    }
    let Some(key) = decode_lower_hex(key_hex) else {
        return Err(AbstractionMarkerError::UnsupportedOrMalformed(
            relation.to_string(),
        ));
    };
    if !valid_v1_key(&key) {
        return Err(AbstractionMarkerError::UnsupportedOrMalformed(
            relation.to_string(),
        ));
    }
    Ok(Some(encode_v1(&key)))
}

/// The kind of a decoded abstraction, as the key's first byte names it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BodyKind {
    Event,
    Fact,
    Property,
    Amount,
    Concept,
}

/// A term of a decoded abstraction body.
#[derive(Clone, Debug, PartialEq)]
pub enum BodyTerm {
    /// A bound variable, by its canonical first-seen ordinal.
    Variable(u64),
    Constant(String),
    Description(String),
    Unspecified,
    Number(f64),
}

/// A form of a decoded abstraction body: the IR shapes the v1 key encodes.
#[derive(Clone, Debug, PartialEq)]
pub enum BodyForm {
    Predicate {
        relation: String,
        args: Vec<BodyTerm>,
    },
    /// A nested abstraction's marker: the key keeps only its referent; the
    /// nested body is the sibling form that follows it.
    NestedMarker {
        args: Vec<BodyTerm>,
    },
    And(Box<BodyForm>, Box<BodyForm>),
    Or(Box<BodyForm>, Box<BodyForm>),
    Not(Box<BodyForm>),
    Exists(u64, Box<BodyForm>),
    ForAll(u64, Box<BodyForm>),
    Past(Box<BodyForm>),
    Present(Box<BodyForm>),
    Future(Box<BodyForm>),
    Obligatory(Box<BodyForm>),
    Permitted(Box<BodyForm>),
    Count {
        var: u64,
        count: u64,
        body: Box<BodyForm>,
    },
    Biconditional(Box<BodyForm>, Box<BodyForm>),
    Xor(Box<BodyForm>, Box<BodyForm>),
}

/// A decoded abstraction: its kind and the body the key retained for rendering.
#[derive(Clone, Debug, PartialEq)]
pub struct AbstractionBody {
    pub kind: BodyKind,
    pub form: BodyForm,
}

const MAX_BODY_DEPTH: usize = 256;

/// Decode a well-formed v1 marker into the body it retains, for rendering.
///
/// The marker was made lossless so a renderer can read the abstraction back
/// (the reasoner only matches it). `None` for a non-marker, a legacy hash-only
/// marker, an unknown version or a malformed key: callers fall back to the
/// opaque spelling. The key is validated by the same grammar check reasoning
/// ingress uses before any of it is read.
pub fn decode_v1(relation: &str) -> Option<AbstractionBody> {
    let suffix = relation.strip_prefix(ABSTRACTION_MARKER_V1_PREFIX)?;
    let (_digest, key_hex) = suffix.split_once('_')?;
    let key = decode_lower_hex(key_hex)?;
    if !valid_v1_key(&key) {
        return None;
    }
    let (&kind, body) = key.split_first()?;
    let kind = match kind {
        0xa0 => BodyKind::Event,
        0xa1 => BodyKind::Fact,
        0xa2 => BodyKind::Property,
        0xa3 => BodyKind::Amount,
        0xa4 => BodyKind::Concept,
        _ => return None,
    };
    let mut parser = KeyParser {
        input: body,
        position: 0,
        next_variable: 0,
    };
    let form = read_form(&mut parser, 0)?;
    (parser.position == body.len()).then_some(AbstractionBody { kind, form })
}

fn read_terms(parser: &mut KeyParser<'_>) -> Option<Vec<BodyTerm>> {
    let count = usize::try_from(parser.u64()?).ok()?;
    if count > parser.input.len().saturating_sub(parser.position) {
        return None;
    }
    let mut args = Vec::with_capacity(count);
    for _ in 0..count {
        args.push(read_term(parser)?);
    }
    Some(args)
}

fn read_term(parser: &mut KeyParser<'_>) -> Option<BodyTerm> {
    Some(match parser.byte()? {
        0x00 => BodyTerm::Variable(parser.u64()?),
        0x01 => BodyTerm::Constant(parser.string()?.to_string()),
        0x02 => BodyTerm::Description(parser.string()?.to_string()),
        0x03 => BodyTerm::Unspecified,
        0x04 => BodyTerm::Number(f64::from_bits(parser.u64()?)),
        _ => return None,
    })
}

fn read_form(parser: &mut KeyParser<'_>, depth: usize) -> Option<BodyForm> {
    if depth > MAX_BODY_DEPTH {
        return None;
    }
    let two = |parser: &mut KeyParser<'_>| -> Option<(Box<BodyForm>, Box<BodyForm>)> {
        let l = read_form(parser, depth + 1)?;
        let r = read_form(parser, depth + 1)?;
        Some((Box::new(l), Box::new(r)))
    };
    Some(match parser.byte()? {
        0x10 => {
            let relation = parser.string()?.to_string();
            let args = read_terms(parser)?;
            BodyForm::Predicate { relation, args }
        }
        0x11 => BodyForm::NestedMarker {
            args: read_terms(parser)?,
        },
        0x12 => {
            let (l, r) = two(parser)?;
            BodyForm::And(l, r)
        }
        0x13 => {
            let (l, r) = two(parser)?;
            BodyForm::Or(l, r)
        }
        0x14 => BodyForm::Not(Box::new(read_form(parser, depth + 1)?)),
        0x15 => {
            let var = parser.u64()?;
            BodyForm::Exists(var, Box::new(read_form(parser, depth + 1)?))
        }
        0x16 => {
            let var = parser.u64()?;
            BodyForm::ForAll(var, Box::new(read_form(parser, depth + 1)?))
        }
        0x17 => BodyForm::Past(Box::new(read_form(parser, depth + 1)?)),
        0x18 => BodyForm::Present(Box::new(read_form(parser, depth + 1)?)),
        0x19 => BodyForm::Future(Box::new(read_form(parser, depth + 1)?)),
        0x1a => BodyForm::Obligatory(Box::new(read_form(parser, depth + 1)?)),
        0x1b => BodyForm::Permitted(Box::new(read_form(parser, depth + 1)?)),
        0x1c => {
            let count = parser.u64()?;
            let var = parser.u64()?;
            BodyForm::Count {
                var,
                count,
                body: Box::new(read_form(parser, depth + 1)?),
            }
        }
        0x1d => {
            let (l, r) = two(parser)?;
            BodyForm::Biconditional(l, r)
        }
        0x1e => {
            let (l, r) = two(parser)?;
            BodyForm::Xor(l, r)
        }
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key_predicate(relation: &str, args: &[&[u8]]) -> Vec<u8> {
        let mut key = vec![0x10];
        key.extend_from_slice(&(relation.len() as u64).to_be_bytes());
        key.extend_from_slice(relation.as_bytes());
        key.extend_from_slice(&(args.len() as u64).to_be_bytes());
        for a in args {
            key.extend_from_slice(a);
        }
        key
    }
    fn term_var(n: u64) -> Vec<u8> {
        let mut t = vec![0x00];
        t.extend_from_slice(&n.to_be_bytes());
        t
    }
    fn term_const(s: &str) -> Vec<u8> {
        let mut t = vec![0x01];
        t.extend_from_slice(&(s.len() as u64).to_be_bytes());
        t.extend_from_slice(s.as_bytes());
        t
    }

    #[test]
    fn a_marker_decodes_to_the_body_it_retains() {
        // event { protest() } as the compiler keys it: protest(ev) ∧ protest_x1(ev, _)
        let mut key = vec![0xa0, 0x12];
        key.extend(key_predicate("protest", &[&term_var(0)]));
        key.extend(key_predicate("protest_x1", &[&term_var(0), &[0x03]]));
        let marker = encode_v1(&key);
        let body = decode_v1(&marker).expect("a well-formed v1 marker decodes");
        assert_eq!(body.kind, BodyKind::Event);
        let BodyForm::And(l, r) = body.form else {
            panic!("expected a conjunction");
        };
        assert_eq!(
            *l,
            BodyForm::Predicate {
                relation: "protest".into(),
                args: vec![BodyTerm::Variable(0)],
            }
        );
        assert_eq!(
            *r,
            BodyForm::Predicate {
                relation: "protest_x1".into(),
                args: vec![BodyTerm::Variable(0), BodyTerm::Unspecified],
            }
        );
    }

    #[test]
    fn constants_descriptions_numbers_and_binders_decode() {
        let mut key = vec![0xa1, 0x15];
        key.extend_from_slice(&0_u64.to_be_bytes());
        key.push(0x14);
        let mut num = vec![0x04];
        num.extend_from_slice(&2.5_f64.to_bits().to_be_bytes());
        let mut desc = vec![0x02];
        desc.extend_from_slice(&3_u64.to_be_bytes());
        desc.extend_from_slice(b"dog");
        key.extend(key_predicate(
            "sees",
            &[&term_var(0), &term_const("Adam"), &num, &desc],
        ));
        let marker = encode_v1(&key);
        let body = decode_v1(&marker).unwrap();
        assert_eq!(body.kind, BodyKind::Fact);
        assert_eq!(
            body.form,
            BodyForm::Exists(
                0,
                Box::new(BodyForm::Not(Box::new(BodyForm::Predicate {
                    relation: "sees".into(),
                    args: vec![
                        BodyTerm::Variable(0),
                        BodyTerm::Constant("Adam".into()),
                        BodyTerm::Number(2.5),
                        BodyTerm::Description("dog".into()),
                    ],
                })))
            )
        );
    }

    #[test]
    fn decoding_fails_closed_where_canonicalization_does() {
        assert!(decode_v1("protest").is_none());
        assert!(decode_v1("__abs_0123456789abcdef").is_none());
        assert!(decode_v1("__abs_v1_0123456789abcdef_FF").is_none());
        let mut trailing = vec![0xa0];
        trailing.extend(key_predicate("p", &[]));
        trailing.push(0xff);
        assert!(decode_v1(&encode_v1(&trailing)).is_none());
    }

    #[test]
    fn fnv1a_matches_reference_vectors() {
        assert_eq!(fnv1a64(b""), 0xcbf29ce484222325);
        assert_eq!(fnv1a64(b"a"), 0xaf63dc4c8601ec8c);
        assert_eq!(fnv1a64(b"foobar"), 0x85944171f73967e8);
    }

    #[test]
    fn digest_is_canonicalized_from_the_lossless_key() {
        // event-kind + Predicate("p", []).
        let mut key = vec![0xa0, 0x10];
        key.extend_from_slice(&1_u64.to_be_bytes());
        key.push(b'p');
        key.extend_from_slice(&0_u64.to_be_bytes());
        let canonical = encode_v1(&key);
        assert_eq!(
            canonicalize_relation(&canonical).unwrap(),
            Some(canonical.clone())
        );

        let mut forged = canonical.clone();
        forged.replace_range(
            ABSTRACTION_MARKER_V1_PREFIX.len()..ABSTRACTION_MARKER_V1_PREFIX.len() + 16,
            "0000000000000000",
        );
        assert_eq!(canonicalize_relation(&forged).unwrap(), Some(canonical));
    }

    #[test]
    fn legacy_unknown_and_malformed_markers_fail_closed() {
        assert!(matches!(
            canonicalize_relation("__abs_0123456789abcdef"),
            Err(AbstractionMarkerError::LegacyHashOnly(_))
        ));
        for marker in [
            "__abs_v2_deadbeef",
            "__abs_v1_short_00",
            "__abs_v1_0123456789abcdef_0",
            "__abs_v1_0123456789abcdef_FF",
        ] {
            assert!(matches!(
                canonicalize_relation(marker),
                Err(AbstractionMarkerError::UnsupportedOrMalformed(_))
            ));
        }

        let mut minimal = vec![0xa0, 0x10];
        minimal.extend_from_slice(&0_u64.to_be_bytes());
        minimal.extend_from_slice(&0_u64.to_be_bytes());
        let mut trailing = minimal.clone();
        trailing.push(0xff);
        let mut variable_gap = vec![0xa0, 0x15];
        variable_gap.extend_from_slice(&1_u64.to_be_bytes());
        variable_gap.extend_from_slice(&minimal[1..]);
        let mut nested_wrong_arity = vec![0xa0, 0x11];
        nested_wrong_arity.extend_from_slice(&0_u64.to_be_bytes());
        let internal_name = "__abs_not-a-regular-predicate";
        let mut internal_as_regular = vec![0xa0, 0x10];
        internal_as_regular.extend_from_slice(&(internal_name.len() as u64).to_be_bytes());
        internal_as_regular.extend_from_slice(internal_name.as_bytes());
        internal_as_regular.extend_from_slice(&0_u64.to_be_bytes());
        for invalid_key in [
            Vec::new(),
            vec![0x00],
            vec![0xa0, 0x10],
            trailing,
            variable_gap,
            nested_wrong_arity,
            internal_as_regular,
        ] {
            let marker = encode_v1(&invalid_key);
            assert!(matches!(
                canonicalize_relation(&marker),
                Err(AbstractionMarkerError::UnsupportedOrMalformed(_))
            ));
        }

        assert_eq!(
            canonicalize_relation(&encode_v1(&minimal)).unwrap(),
            Some(encode_v1(&minimal)),
            "the strict parser must still admit a complete canonical key"
        );
    }
}
