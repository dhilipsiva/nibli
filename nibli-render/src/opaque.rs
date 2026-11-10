//! Display-only decoding of the lossless v1 opaque-event key. This does not
//! assert its quoted body or change marker identity. Unknown, open, oversized,
//! or deeply nested content stays in the original structural proof.

use nibli_types::abstraction::{ABSTRACTION_MARKER_V1_PREFIX, canonicalize_relation};
use nibli_types::logic::{LogicBuffer, LogicNode, LogicalTerm};

pub(crate) fn event_body(marker: &str) -> Option<LogicBuffer> {
    if marker.len() > 131_072 {
        return None;
    }
    let canonical = canonicalize_relation(marker).ok()??;
    let (_, hex) = canonical
        .strip_prefix(ABSTRACTION_MARKER_V1_PREFIX)?
        .split_once('_')?;
    let bytes = hex
        .as_bytes()
        .chunks_exact(2)
        .map(|p| {
            let digit = |c: u8| if c <= b'9' { c - b'0' } else { c - b'a' + 10 };
            digit(p[0]) * 16 + digit(p[1])
        })
        .collect::<Vec<_>>();
    let mut decoder = Decoder {
        bytes: &bytes,
        pos: 0,
        nodes: Vec::new(),
        bound: Vec::new(),
    };
    if decoder.byte()? != 0xa0 {
        return None;
    }
    let root = decoder.form(0)?;
    (decoder.pos == bytes.len()).then_some(LogicBuffer {
        nodes: decoder.nodes,
        roots: vec![root],
    })
}

struct Decoder<'a> {
    bytes: &'a [u8],
    pos: usize,
    nodes: Vec<LogicNode>,
    bound: Vec<u64>,
}

impl Decoder<'_> {
    fn byte(&mut self) -> Option<u8> {
        let value = *self.bytes.get(self.pos)?;
        self.pos += 1;
        Some(value)
    }

    fn number(&mut self) -> Option<u64> {
        let end = self.pos.checked_add(8)?;
        let value = u64::from_be_bytes(self.bytes.get(self.pos..end)?.try_into().ok()?);
        self.pos = end;
        Some(value)
    }

    fn string(&mut self) -> Option<String> {
        let len = usize::try_from(self.number()?).ok()?;
        let end = self.pos.checked_add(len)?;
        let value = std::str::from_utf8(self.bytes.get(self.pos..end)?)
            .ok()?
            .to_owned();
        self.pos = end;
        Some(value)
    }

    fn term(&mut self) -> Option<LogicalTerm> {
        Some(match self.byte()? {
            0x00 => {
                let ordinal = self.number()?;
                // The key does not carry the enclosing proof's substitution.
                // Never silently turn an external dependency into a fresh X.
                if !self.bound.contains(&ordinal) {
                    return None;
                }
                LogicalTerm::Variable(format!("_abs{ordinal}"))
            }
            0x01 => LogicalTerm::Constant(self.string()?),
            0x02 => LogicalTerm::Description(self.string()?),
            0x03 => LogicalTerm::Unspecified,
            0x04 => LogicalTerm::Number(f64::from_bits(self.number()?)),
            _ => return None,
        })
    }

    fn push(&mut self, node: LogicNode) -> u32 {
        let id = self.nodes.len() as u32;
        self.nodes.push(node);
        id
    }

    fn form(&mut self, depth: usize) -> Option<u32> {
        if depth > 64 {
            return None;
        }
        let tag = self.byte()?;
        let node = match tag {
            0x10 | 0x11 => {
                let relation = if tag == 0x10 {
                    self.string()?
                } else {
                    "__abs_nested".to_owned()
                };
                let count = usize::try_from(self.number()?).ok()?;
                let mut terms = Vec::new();
                for _ in 0..count {
                    terms.push(self.term()?);
                }
                LogicNode::Predicate((relation, terms))
            }
            0x12 | 0x13 | 0x1d | 0x1e => {
                let left = self.form(depth + 1)?;
                let right = self.form(depth + 1)?;
                match tag {
                    0x12 => LogicNode::AndNode((left, right)),
                    0x13 => LogicNode::OrNode((left, right)),
                    0x1d => {
                        let not_left = self.push(LogicNode::NotNode(left));
                        let not_right = self.push(LogicNode::NotNode(right));
                        let forward = self.push(LogicNode::OrNode((not_left, right)));
                        let backward = self.push(LogicNode::OrNode((not_right, left)));
                        LogicNode::AndNode((forward, backward))
                    }
                    _ => {
                        let either = self.push(LogicNode::OrNode((left, right)));
                        let both = self.push(LogicNode::AndNode((left, right)));
                        let not_both = self.push(LogicNode::NotNode(both));
                        LogicNode::AndNode((either, not_both))
                    }
                }
            }
            0x15 | 0x16 | 0x1c => {
                let count = if tag == 0x1c {
                    Some(u32::try_from(self.number()?).ok()?)
                } else {
                    None
                };
                let ordinal = self.number()?;
                self.bound.push(ordinal);
                let body = self.form(depth + 1)?;
                self.bound.pop();
                let var = format!("_abs{ordinal}");
                match tag {
                    0x15 => LogicNode::ExistsNode((var, body)),
                    0x16 => LogicNode::ForAllNode((var, body)),
                    _ => LogicNode::CountNode((var, count?, body)),
                }
            }
            0x14 | 0x17..=0x1b => {
                let body = self.form(depth + 1)?;
                match tag {
                    0x14 => LogicNode::NotNode(body),
                    0x17 => LogicNode::PastNode(body),
                    0x18 => LogicNode::PresentNode(body),
                    0x19 => LogicNode::FutureNode(body),
                    0x1a => LogicNode::ObligatoryNode(body),
                    _ => LogicNode::PermittedNode(body),
                }
            }
            _ => return None,
        };
        Some(self.push(node))
    }
}
