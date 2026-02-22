// parser/src/lib.rs
//
// WASM component entry point. Pipeline:
//   1. Lex (Logos DFA)
//   2. Preprocess (metalinguistic resolution)
//   3. Parse (recursive descent)
//   4. Flatten (tree AST → index-based WIT buffer)

pub mod ast;
#[allow(warnings)]
mod bindings;
pub mod grammar;
pub mod lexer;
pub mod preprocessor;

use bindings::exports::lojban::nesy::parser::Guest;
use bindings::lojban::nesy::ast_types as wit;

struct ParserComponent;

impl Guest for ParserComponent {
    fn parse_text(input: String) -> Result<wit::AstBuffer, String> {
        // 1. Lex into morphological classification stream
        let raw_tokens = crate::lexer::tokenize(&input);

        // 2. Resolve metalinguistic operators (si/sa/su/zo/zoi/zei)
        let normalized = crate::preprocessor::preprocess(raw_tokens.into_iter(), &input);

        // 3. Recursive descent parse
        let parsed = crate::grammar::parse_tokens_to_ast(&normalized)?;

        // 4. Flatten tree AST → index-based WIT buffer
        Ok(Flattener::flatten(parsed))
    }
}

// ─── AST → WIT Buffer Flattener ─────────────────────────────────

/// Converts the tree-structured AST into the flat index-based WIT buffer.
/// Each recursive AST node is pushed into the appropriate array and
/// referenced by index from its parent.
///
/// Top-level sentences are recorded in `buffer.roots`.
/// Rel clause bodies are stored in `buffer.sentences` but are NOT roots.
struct Flattener {
    buffer: wit::AstBuffer,
}

impl Flattener {
    fn new() -> Self {
        Self {
            buffer: wit::AstBuffer {
                selbris: Vec::new(),
                sumtis: Vec::new(),
                sentences: Vec::new(),
                roots: Vec::new(),
            },
        }
    }

    fn flatten(parsed: ast::ParsedText) -> wit::AstBuffer {
        let mut f = Self::new();
        for bridi in parsed.sentences {
            f.push_bridi(bridi);
            // The top-level sentence is always the LAST entry added by
            // push_bridi.  Rel clause bodies are pushed earlier (during
            // push_sumti for Restricted variants), so they have lower indices.
        }
        // Top-level sentence is LAST pushed (abstraction/rel clause bodies pushed earlier)
        let root_idx = (f.buffer.sentences.len() - 1) as u32;
        f.buffer.roots.push(root_idx);
        f.buffer
    }

    // ─── Bridi ───────────────────────────────────────────────

    fn push_bridi(&mut self, bridi: ast::Bridi) {
        let relation = self.push_selbri(bridi.selbri);

        let head_terms: Vec<u32> = bridi
            .head_terms
            .into_iter()
            .map(|s| self.push_sumti(s))
            .collect();

        let tail_terms: Vec<u32> = bridi
            .tail_terms
            .into_iter()
            .map(|s| self.push_sumti(s))
            .collect();

        self.buffer.sentences.push(wit::Bridi {
            relation,
            head_terms,
            tail_terms,
            negated: bridi.negated,
        });
    }

    // ─── Selbri ──────────────────────────────────────────────

    fn push_selbri(&mut self, selbri: ast::Selbri) -> u32 {
        let wit_selbri = match selbri {
            ast::Selbri::Root(s) => wit::Selbri::Root(s),

            ast::Selbri::Compound(parts) => wit::Selbri::Compound(parts),

            ast::Selbri::Tanru(modifier, head) => {
                let m_id = self.push_selbri(*modifier);
                let h_id = self.push_selbri(*head);
                wit::Selbri::Tanru((m_id, h_id))
            }

            ast::Selbri::Converted(conv, inner) => {
                let inner_id = self.push_selbri(*inner);
                let wit_conv = match conv {
                    ast::Conversion::Se => wit::Conversion::Se,
                    ast::Conversion::Te => wit::Conversion::Te,
                    ast::Conversion::Ve => wit::Conversion::Ve,
                    ast::Conversion::Xe => wit::Conversion::Xe,
                };
                wit::Selbri::Converted((wit_conv, inner_id))
            }

            ast::Selbri::Negated(inner) => {
                let inner_id = self.push_selbri(*inner);
                wit::Selbri::Negated(inner_id)
            }

            ast::Selbri::Grouped(inner) => {
                let inner_id = self.push_selbri(*inner);
                wit::Selbri::Grouped(inner_id)
            }

            ast::Selbri::WithArgs { core, args } => {
                let core_id = self.push_selbri(*core);
                let arg_ids: Vec<u32> = args.into_iter().map(|s| self.push_sumti(s)).collect();
                wit::Selbri::WithArgs((core_id, arg_ids))
            }

            ast::Selbri::Connected {
                left,
                connective,
                right,
            } => {
                let l_id = self.push_selbri(*left);
                let r_id = self.push_selbri(*right);
                let wit_conn = match connective {
                    ast::Connective::Je => wit::Connective::Je,
                    ast::Connective::Ja => wit::Connective::Ja,
                    ast::Connective::Jo => wit::Connective::Jo,
                    ast::Connective::Ju => wit::Connective::Ju,
                };
                wit::Selbri::Connected((l_id, wit_conn, r_id))
            }
            ast::Selbri::Abstraction(inner_bridi) => {
                // Inner bridi goes into sentences (NOT a root —
                // same pattern as rel clause bodies).
                let body_idx = self.buffer.sentences.len() as u32;
                self.push_bridi(*inner_bridi);
                wit::Selbri::Abstraction(body_idx)
            }
        };

        let id = self.buffer.selbris.len() as u32;
        self.buffer.selbris.push(wit_selbri);
        id
    }

    // ─── Sumti ───────────────────────────────────────────────

    fn push_sumti(&mut self, sumti: ast::Sumti) -> u32 {
        let wit_sumti = match sumti {
            ast::Sumti::ProSumti(s) => wit::Sumti::ProSumti(s),

            ast::Sumti::Description { gadri, inner } => {
                let inner_id = self.push_selbri(*inner);
                let wit_gadri = match gadri {
                    ast::Gadri::Lo => wit::Gadri::Lo,
                    ast::Gadri::Le => wit::Gadri::Le,
                    ast::Gadri::La => wit::Gadri::La,
                    ast::Gadri::RoLo => wit::Gadri::RoLo,
                    ast::Gadri::RoLe => wit::Gadri::RoLe,
                };
                wit::Sumti::Description((wit_gadri, inner_id))
            }

            ast::Sumti::Name(n) => wit::Sumti::Name(n),

            ast::Sumti::QuotedLiteral(q) => wit::Sumti::QuotedLiteral(q),

            ast::Sumti::Unspecified => wit::Sumti::Unspecified,

            ast::Sumti::Tagged(tag, inner) => {
                let inner_id = self.push_sumti(*inner);
                let wit_tag = match tag {
                    ast::PlaceTag::Fa => wit::PlaceTag::Fa,
                    ast::PlaceTag::Fe => wit::PlaceTag::Fe,
                    ast::PlaceTag::Fi => wit::PlaceTag::Fi,
                    ast::PlaceTag::Fo => wit::PlaceTag::Fo,
                    ast::PlaceTag::Fu => wit::PlaceTag::Fu,
                };
                wit::Sumti::Tagged((wit_tag, inner_id))
            }

            ast::Sumti::Restricted { inner, clause } => {
                let inner_id = self.push_sumti(*inner);

                // The rel clause body is a sentence — push it as a bridi.
                // It is NOT a root; it lives in `sentences` only for
                // cross-referencing by index from the Restricted variant.
                let body_idx = self.buffer.sentences.len() as u32;
                self.push_bridi(*clause.body);

                let wit_kind = match clause.kind {
                    ast::RelClauseKind::Poi => wit::RelClauseKind::Poi,
                    ast::RelClauseKind::Noi => wit::RelClauseKind::Noi,
                };

                wit::Sumti::Restricted((
                    inner_id,
                    wit::RelClause {
                        kind: wit_kind,
                        body_sentence: body_idx,
                    },
                ))
            }
        };

        let id = self.buffer.sumtis.len() as u32;
        self.buffer.sumtis.push(wit_sumti);
        id
    }
}

bindings::export!(ParserComponent with_types_in bindings);
