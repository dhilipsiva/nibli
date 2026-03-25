//! Shared wire-format types for the nibli proof trace protocol.
//!
//! Both nibli-engine (native, serializes) and nibli-ui (browser WASM, deserializes)
//! depend on this crate. It has no heavy dependencies — just serde.

use serde::{Deserialize, Serialize};

// ── Proof trace wire types ──

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ProofTrace {
    pub steps: Vec<ProofStep>,
    pub root: u32,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ProofStep {
    pub rule: ProofRule,
    pub holds: bool,
    pub children: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct LogicalTerm {
    pub kind: String,
    pub value: Option<String>,
    pub number: Option<f64>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum ProofRule {
    #[serde(rename = "conjunction")]
    Conjunction,
    #[serde(rename = "disjunction_check")]
    DisjunctionCheck { detail: String },
    #[serde(rename = "disjunction_intro")]
    DisjunctionIntro { side: String },
    #[serde(rename = "negation")]
    Negation,
    #[serde(rename = "modal_passthrough")]
    ModalPassthrough { kind: String },
    #[serde(rename = "exists_witness")]
    ExistsWitness { var: String, term: LogicalTerm },
    #[serde(rename = "exists_failed")]
    ExistsFailed,
    #[serde(rename = "forall_vacuous")]
    ForallVacuous,
    #[serde(rename = "forall_verified")]
    ForallVerified { entities: Vec<LogicalTerm> },
    #[serde(rename = "forall_counterexample")]
    ForallCounterexample { entity: LogicalTerm },
    #[serde(rename = "count_result")]
    CountResult { expected: u32, actual: u32 },
    #[serde(rename = "predicate_check")]
    PredicateCheck { method: String, detail: String },
    #[serde(rename = "compute_check")]
    ComputeCheck { method: String, detail: String },
    #[serde(rename = "asserted")]
    Asserted { #[serde(rename = "sexp")] fact: String },
    #[serde(rename = "derived")]
    Derived { label: String, #[serde(rename = "sexp")] fact: String },
    #[serde(rename = "proof_ref")]
    ProofRef { #[serde(rename = "sexp")] fact: String },
}

// ── KB status wire types ──

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct LineResult {
    pub line_number: u32,
    pub text: String,
    pub success: bool,
    pub fact_id: Option<u64>,
    pub error: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct KbStatus {
    pub asserted: u32,
    pub errors: u32,
    pub skipped: u32,
    pub line_results: Vec<LineResult>,
}

// ── Serialization helper ──

impl ProofTrace {
    /// Serialize to JSON string for wire transport.
    pub fn to_json(&self) -> String {
        serde_json::to_string(self).unwrap_or_default()
    }

    /// Deserialize from JSON string.
    pub fn from_json(s: &str) -> Option<Self> {
        serde_json::from_str(s).ok()
    }

    /// Render the proof tree as compact indented text.
    pub fn to_pretty_text(&self) -> String {
        self.to_pretty_text_with_indent(0)
    }

    /// Render the proof tree as compact indented text with a base indent.
    pub fn to_pretty_text_with_indent(&self, base_indent: usize) -> String {
        let mut out = String::new();
        format_proof_step(self, self.root, base_indent, &mut out);
        out
    }
}

// ── Fact display humanizer ──

/// Parse and humanize a logji internal representation into readable notation.
///
/// Converts internal representations like:
///   `(Pred "danlu" (Cons (SkolemFn "sk_1" (Const "adam")) (Nil)))` → `danlu(#1(adam))`
///   `(Past (Pred "klama" (Cons (Const "adam") (Nil))))` → `[past] klama(adam)`
///   `(Const "adam")` → `adam`
pub fn humanize_fact(input: &str) -> String {
    let tokens = tokenize_repr(input);
    let mut pos = 0;
    match parse_fact_node(&tokens, &mut pos) {
        Some(node) => format_fact_node(&node),
        None => input.to_string(),
    }
}

enum FactNode {
    Atom(String),
    List(Vec<FactNode>),
}

fn tokenize_repr(s: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut chars = s.chars().peekable();
    while let Some(&c) = chars.peek() {
        match c {
            '(' => {
                tokens.push("(".to_string());
                chars.next();
            }
            ')' => {
                tokens.push(")".to_string());
                chars.next();
            }
            '"' => {
                chars.next();
                let mut buf = String::new();
                while let Some(&ch) = chars.peek() {
                    if ch == '"' {
                        chars.next();
                        break;
                    }
                    buf.push(ch);
                    chars.next();
                }
                tokens.push(format!("\"{}\"", buf));
            }
            c if c.is_whitespace() => {
                chars.next();
            }
            _ => {
                let mut word = String::new();
                while let Some(&ch) = chars.peek() {
                    if ch == '(' || ch == ')' || ch == '"' || ch.is_whitespace() {
                        break;
                    }
                    word.push(ch);
                    chars.next();
                }
                tokens.push(word);
            }
        }
    }
    tokens
}

fn parse_fact_node(tokens: &[String], pos: &mut usize) -> Option<FactNode> {
    if *pos >= tokens.len() {
        return None;
    }
    if tokens[*pos] == "(" {
        *pos += 1;
        let mut children = Vec::new();
        while *pos < tokens.len() && tokens[*pos] != ")" {
            if let Some(child) = parse_fact_node(tokens, pos) {
                children.push(child);
            } else {
                break;
            }
        }
        if *pos < tokens.len() {
            *pos += 1; // skip )
        }
        Some(FactNode::List(children))
    } else {
        let tok = tokens[*pos].clone();
        *pos += 1;
        Some(FactNode::Atom(tok))
    }
}

fn unquote(s: &str) -> &str {
    s.strip_prefix('"')
        .and_then(|s| s.strip_suffix('"'))
        .unwrap_or(s)
}

fn format_fact_node(node: &FactNode) -> String {
    match node {
        FactNode::Atom(s) => unquote(s).to_string(),
        FactNode::List(children) => {
            if children.is_empty() {
                return "()".to_string();
            }
            let tag = match &children[0] {
                FactNode::Atom(s) => s.as_str(),
                _ => return format_fact_generic(children),
            };
            match tag {
                "Pred" => format_fact_pred(children),
                "Const" => format_fact_extract(children),
                "Var" => {
                    if children.len() < 2 {
                        "?".to_string()
                    } else {
                        format!("?{}", format_fact_node(&children[1]))
                    }
                }
                "Num" => format_fact_num(children),
                "Desc" => {
                    if children.len() < 2 {
                        "le ?".to_string()
                    } else {
                        format!("le {}", format_fact_node(&children[1]))
                    }
                }
                "Zoe" => "_".to_string(),
                "Nil" => String::new(),
                "Cons" => {
                    let items = collect_arg_items(children);
                    items
                        .iter()
                        .map(|n| format_fact_node(n))
                        .collect::<Vec<_>>()
                        .join(", ")
                }
                "SkolemFn" => {
                    if children.len() < 3 {
                        "#?".to_string()
                    } else {
                        let name = format_fact_node(&children[1]);
                        let dep = format_fact_node(&children[2]);
                        format!("{}({})", humanize_term(name), humanize_term(dep))
                    }
                }
                "DepPair" => {
                    if children.len() < 3 {
                        "?".to_string()
                    } else {
                        format!(
                            "{}, {}",
                            format_fact_node(&children[1]),
                            format_fact_node(&children[2])
                        )
                    }
                }
                "Past" | "Present" | "Future" | "Obligatory" | "Permitted" => {
                    let label = tag.to_lowercase();
                    if children.len() < 2 {
                        label
                    } else {
                        format!("[{}] {}", label, format_fact_node(&children[1]))
                    }
                }
                "Or" => format_fact_binop("∨", children),
                "And" => format_fact_binop("∧", children),
                "Not" => {
                    if children.len() < 2 {
                        "¬?".to_string()
                    } else {
                        format!("¬{}", format_fact_node(&children[1]))
                    }
                }
                _ => format_fact_generic(children),
            }
        }
    }
}

fn format_fact_pred(children: &[FactNode]) -> String {
    if children.len() < 3 {
        return "?pred".to_string();
    }
    let name = format_fact_node(&children[1]);
    let args = collect_arg_list(&children[2]);

    // Collapse Neo-Davidsonian role predicates (e.g., "gerku_x1") into compact form.
    // "gerku_x1(sk_0, adam)" → "gerku.x1(adam)" (hide event variable)
    if let Some(base_and_role) = parse_role_predicate(&name) {
        let formatted: Vec<String> = args.iter()
            .map(|a| humanize_term(format_fact_node(a)))
            .filter(|s| !is_event_skolem(s))  // hide event Skolem args
            .collect();
        if formatted.is_empty() {
            base_and_role
        } else {
            format!("{}({})", base_and_role, formatted.join(", "))
        }
    } else {
        let formatted: Vec<String> = args.iter()
            .map(|a| humanize_term(format_fact_node(a)))
            .collect();
        if formatted.is_empty() {
            name
        } else {
            format!("{}({})", name, formatted.join(", "))
        }
    }
}

/// Detect Neo-Davidsonian role predicates: "gerku_x1" → "gerku.x1"
fn parse_role_predicate(name: &str) -> Option<String> {
    // Match patterns like "name_x1", "name_x2", etc.
    if let Some(underscore_pos) = name.rfind('_') {
        let suffix = &name[underscore_pos + 1..];
        if suffix.starts_with('x') && suffix[1..].chars().all(|c| c.is_ascii_digit()) {
            let base = &name[..underscore_pos];
            return Some(format!("{}.{}", base, suffix));
        }
    }
    None
}

/// Check if a term string looks like an event Skolem (starts with "sk_" and followed by digits).
fn is_event_skolem(s: &str) -> bool {
    s.starts_with("sk_") && s[3..].chars().all(|c| c.is_ascii_digit())
}

/// Humanize a single term: rename Skolem constants for readability.
fn humanize_term(s: String) -> String {
    // sk_N → #N (compact Skolem display)
    if s.starts_with("sk_") && s[3..].chars().all(|c| c.is_ascii_digit()) {
        return format!("#{}", &s[3..]);
    }
    // SkolemFn display: sk_N(arg) → #N(arg)
    if s.starts_with("sk_") {
        if let Some(paren) = s.find('(') {
            let num_part = &s[3..paren];
            if num_part.chars().all(|c| c.is_ascii_digit()) {
                return format!("#{}{}", num_part, &s[paren..]);
            }
        }
    }
    s
}

fn format_fact_extract(children: &[FactNode]) -> String {
    if children.len() < 2 {
        "?".to_string()
    } else {
        humanize_term(format_fact_node(&children[1]))
    }
}

fn format_fact_num(children: &[FactNode]) -> String {
    if children.len() < 2 {
        return "0".to_string();
    }
    match &children[1] {
        FactNode::Atom(s) => {
            if let Ok(n) = s.parse::<f64>() {
                if n == (n as i64) as f64 {
                    format!("{}", n as i64)
                } else {
                    format!("{}", n)
                }
            } else {
                s.clone()
            }
        }
        n => format_fact_node(n),
    }
}

fn collect_arg_list(node: &FactNode) -> Vec<&FactNode> {
    match node {
        FactNode::List(children) => {
            if children.is_empty() {
                return vec![];
            }
            let tag = match &children[0] {
                FactNode::Atom(s) => s.as_str(),
                _ => return vec![node],
            };
            match tag {
                "Cons" if children.len() >= 3 => {
                    let mut result = vec![&children[1]];
                    result.extend(collect_arg_list(&children[2]));
                    result
                }
                "Nil" => vec![],
                _ => vec![node],
            }
        }
        _ => vec![node],
    }
}

fn collect_arg_items(children: &[FactNode]) -> Vec<&FactNode> {
    if children.len() < 3 {
        return vec![];
    }
    let mut result = vec![&children[1]];
    result.extend(collect_arg_list(&children[2]));
    result
}

fn format_fact_binop(op: &str, children: &[FactNode]) -> String {
    if children.len() < 3 {
        return op.to_string();
    }
    format!(
        "({} {} {})",
        format_fact_node(&children[1]),
        op,
        format_fact_node(&children[2])
    )
}

fn format_fact_generic(children: &[FactNode]) -> String {
    let parts: Vec<String> = children.iter().map(format_fact_node).collect();
    format!("({})", parts.join(" "))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_humanize_simple_pred() {
        assert_eq!(
            humanize_fact(r#"(Pred "gerku" (Cons (Const "adam") (Nil)))"#),
            "gerku(adam)"
        );
    }

    #[test]
    fn test_humanize_skolem() {
        assert_eq!(
            humanize_fact(r#"(Pred "danlu" (Cons (SkolemFn "sk_1" (Const "adam")) (Nil)))"#),
            "danlu(sk_1(adam))"
        );
    }

    #[test]
    fn test_humanize_tense() {
        assert_eq!(
            humanize_fact(r#"(Past (Pred "klama" (Cons (Const "adam") (Nil))))"#),
            "[past] klama(adam)"
        );
    }

    #[test]
    fn test_humanize_multi_arg() {
        assert_eq!(
            humanize_fact(r#"(Pred "klama" (Cons (Const "adam") (Cons (Const "paris") (Nil))))"#),
            "klama(adam, paris)"
        );
    }

    #[test]
    fn test_humanize_zoe() {
        assert_eq!(
            humanize_fact(r#"(Pred "klama" (Cons (Const "adam") (Cons (Zoe) (Nil))))"#),
            "klama(adam, _)"
        );
    }

    #[test]
    fn test_humanize_number() {
        assert_eq!(
            humanize_fact(r#"(Pred "pilji" (Cons (Num 3) (Cons (Num 4) (Nil))))"#),
            "pilji(3, 4)"
        );
    }

    #[test]
    fn test_humanize_desc() {
        assert_eq!(
            humanize_fact(r#"(Pred "klama" (Cons (Desc "gerku") (Nil)))"#),
            "klama(le gerku)"
        );
    }

    #[test]
    fn test_humanize_negation() {
        assert_eq!(
            humanize_fact(r#"(Not (Pred "gerku" (Cons (Const "adam") (Nil))))"#),
            "¬gerku(adam)"
        );
    }

    #[test]
    fn test_humanize_dep_pair_skolem() {
        assert_eq!(
            humanize_fact(r#"(SkolemFn "sk_2" (DepPair (Const "adam") (Const "bob")))"#),
            "sk_2(adam, bob)"
        );
    }

    #[test]
    fn test_humanize_fallback() {
        // Plain string that isn't an s-expression
        assert_eq!(humanize_fact("hello"), "hello");
    }

    #[test]
    fn test_proof_trace_pretty_text() {
        let trace = ProofTrace {
            steps: vec![ProofStep {
                rule: ProofRule::Asserted {
                    fact: r#"(Pred "gerku" (Cons (Const "adam") (Nil)))"#.to_string(),
                },
                holds: true,
                children: vec![],
            }],
            root: 0,
        };

        assert_eq!(trace.to_pretty_text(), "Asserted: gerku(adam) -> TRUE\n");
        assert_eq!(
            trace.to_pretty_text_with_indent(1),
            "  Asserted: gerku(adam) -> TRUE\n"
        );
    }
}

// ── Gossip network types (shared between nibli-server and nibli-ui) ──

/// A gossip event pushed to the UI via GraphQL subscription or WebRTC.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum GossipEvent {
    /// New envelope received and ingested.
    #[serde(rename = "envelope")]
    NewEnvelope {
        envelope_id: String,
        author: String,
        lojban: Option<String>,
        stance: String,
        topics: Vec<String>,
        timestamp: String,
    },
    /// Contradiction detected between two assertions.
    #[serde(rename = "contradiction")]
    Contradiction {
        id: usize,
        envelope_id: String,
        assertion: String,
        author: String,
    },
    /// Trust change (trust or distrust).
    #[serde(rename = "trust_change")]
    TrustChange {
        from: String,
        to: String,
        trusted: bool,
    },
    /// Peer connected or disconnected.
    #[serde(rename = "peer_change")]
    PeerChange { peer_id: String, connected: bool },
    /// Sync completed with a peer.
    #[serde(rename = "sync")]
    Sync {
        peer_id: String,
        envelope_count: usize,
    },
}

/// Summary of a gossip agent visible on the network.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct NetworkAgent {
    pub name: String,
    pub envelope_count: u32,
    pub stance_counts: StanceCounts,
    pub topics: Vec<String>,
    pub is_local: bool,
}

/// Distribution of epistemic stances for an agent.
#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct StanceCounts {
    pub deduced: u32,
    pub expected: u32,
    pub opinion: u32,
    pub hearsay: u32,
}

/// Summary of an envelope for the UI.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct EnvelopeSummary {
    pub id: String,
    pub author: String,
    pub lojban: Option<String>,
    pub stance: String,
    pub topics: Vec<String>,
    pub timestamp: String,
    pub is_retraction: bool,
    pub is_quarantined: bool,
}

/// Summary of a contradiction for the UI.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ContradictionSummary {
    pub id: usize,
    pub envelope_id: String,
    pub assertion: String,
    pub author: String,
    pub resolved: bool,
}

/// Full gossip network state snapshot.
#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct NetworkSnapshot {
    pub agents: Vec<NetworkAgent>,
    pub envelopes: Vec<EnvelopeSummary>,
    pub contradictions: Vec<ContradictionSummary>,
    pub peers: Vec<String>,
    pub local_agent: String,
    pub total_facts: u32,
}

// ── Display helpers ──

impl LogicalTerm {
    /// Human-readable rendering of a logical term.
    pub fn display(&self) -> String {
        match self.kind.as_str() {
            "constant" => self.value.clone().unwrap_or_default(),
            "number" => self.number.map(|n| format!("{}", n)).unwrap_or_default(),
            "variable" => self.value.clone().unwrap_or("?".to_string()),
            "skolem" => self.value.clone().unwrap_or("sk?".to_string()),
            "description" => format!("le_{}", self.value.as_deref().unwrap_or("?")),
            _ => format!("({})", self.kind),
        }
    }

    /// Compact textual rendering used in CLI proof traces.
    pub fn trace_display(&self) -> String {
        match self.kind.as_str() {
            "constant" => self.value.clone().unwrap_or_default(),
            "number" => match self.number {
                Some(n) if n == (n as i64) as f64 => format!("{}", n as i64),
                Some(n) => format!("{}", n),
                None => String::new(),
            },
            "variable" => format!("?{}", self.value.clone().unwrap_or_default()),
            "description" => format!("lo {}", self.value.as_deref().unwrap_or("?")),
            "unspecified" => "zo'e".to_string(),
            _ => self.display(),
        }
    }
}

impl ProofRule {
    /// Unicode icon for this proof rule type.
    pub fn icon(&self) -> &'static str {
        match self {
            Self::Conjunction => "∧",
            Self::DisjunctionCheck { .. } | Self::DisjunctionIntro { .. } => "∨",
            Self::Negation => "¬",
            Self::ModalPassthrough { .. } => "◷",
            Self::ExistsWitness { .. } | Self::ExistsFailed => "∃",
            Self::ForallVacuous
            | Self::ForallVerified { .. }
            | Self::ForallCounterexample { .. } => "∀",
            Self::CountResult { .. } => "#",
            Self::PredicateCheck { .. } | Self::ComputeCheck { .. } => "⊢",
            Self::Asserted { .. } => "▣",
            Self::Derived { .. } => "⊢",
            Self::ProofRef { .. } => "↑",
        }
    }

    /// Human-readable label describing the proof step.
    pub fn label(&self) -> String {
        match self {
            Self::Conjunction => "Conjunction".to_string(),
            Self::DisjunctionCheck { detail } => format!("Disjunction Check: {}", detail),
            Self::DisjunctionIntro { side } => format!("Disjunction Intro: {}", side),
            Self::Negation => "Negation".to_string(),
            Self::ModalPassthrough { kind } => kind.to_string(),
            Self::ExistsWitness { var, term } => format!("Witness: {} = {}", var, term.display()),
            Self::ExistsFailed => "No witness found".to_string(),
            Self::ForallVacuous => "Vacuously true".to_string(),
            Self::ForallVerified { entities } => {
                let names: Vec<String> = entities.iter().map(|t| t.display()).collect();
                format!("Verified: [{}]", names.join(", "))
            }
            Self::ForallCounterexample { entity } => {
                format!("Counterexample: {}", entity.display())
            }
            Self::CountResult { expected, actual } => {
                format!("Count: expected {}, got {}", expected, actual)
            }
            Self::PredicateCheck { method, detail } => {
                format!("Predicate ({}): {}", method, humanize_fact(detail))
            }
            Self::ComputeCheck { method, detail } => {
                format!("Compute ({}): {}", method, humanize_fact(detail))
            }
            Self::Asserted { fact } => format!("Asserted: {}", humanize_fact(fact)),
            Self::Derived { label, fact } => {
                format!("Derived ({}): {}", label, humanize_fact(fact))
            }
            Self::ProofRef { fact } => format!("(proved above): {}", humanize_fact(fact)),
        }
    }

    /// CSS class for color-coding in the UI proof tree.
    pub fn css_class(&self) -> &'static str {
        match self {
            Self::Asserted { .. } => "proof-asserted",
            Self::Derived { .. } => "proof-derived",
            Self::ProofRef { .. } => "proof-ref",
            Self::ExistsWitness { .. } | Self::ModalPassthrough { .. } => "proof-exists",
            Self::ExistsFailed | Self::ForallCounterexample { .. } => "proof-failed",
            Self::Negation => "proof-negation",
            Self::PredicateCheck { .. } | Self::ComputeCheck { .. } => "proof-check",
            Self::Conjunction => "proof-conjunction",
            Self::DisjunctionCheck { .. } | Self::DisjunctionIntro { .. } => "proof-derived",
            Self::ForallVacuous | Self::ForallVerified { .. } => "proof-exists",
            Self::CountResult { .. } => "proof-check",
        }
    }

    /// Compact textual rendering used in CLI proof traces.
    pub fn trace_display(&self, result: bool) -> String {
        let tag = if result { "TRUE" } else { "FALSE" };
        match self {
            Self::Conjunction => format!("Conjunction -> {}", tag),
            Self::DisjunctionCheck { detail } => {
                format!("Disjunction (check: {}) -> {}", detail, tag)
            }
            Self::DisjunctionIntro { side } => {
                format!("Disjunction ({}) -> {}", side, tag)
            }
            Self::Negation => format!("Negation -> {}", tag),
            Self::ModalPassthrough { kind } => format!("Modal ({}) -> {}", kind, tag),
            Self::ExistsWitness { var, term } => {
                format!("Exists: {} = {} -> {}", var, term.trace_display(), tag)
            }
            Self::ExistsFailed => format!("Exists: no witness -> {}", tag),
            Self::ForallVacuous => format!("ForAll: vacuous (empty domain) -> {}", tag),
            Self::ForallVerified { entities } => {
                let names: Vec<String> = entities.iter().map(LogicalTerm::trace_display).collect();
                format!("ForAll: verified [{}] -> {}", names.join(", "), tag)
            }
            Self::ForallCounterexample { entity } => {
                format!(
                    "ForAll: counterexample {} -> {}",
                    entity.trace_display(),
                    tag
                )
            }
            Self::CountResult { expected, actual } => {
                format!("Count: expected={}, actual={} -> {}", expected, actual, tag)
            }
            Self::PredicateCheck { method, detail } => {
                format!("{}: {} -> {}", method, humanize_fact(detail), tag)
            }
            Self::ComputeCheck { method, detail } => {
                format!("Compute ({}): {} -> {}", method, humanize_fact(detail), tag)
            }
            Self::Asserted { fact } => format!("Fact: {} -> {}", humanize_fact(fact), tag),
            Self::Derived { label, fact } => {
                format!("Rule ({}): {} -> {}", humanize_rule_label(label), humanize_fact(fact), tag)
            }
            Self::ProofRef { fact } => {
                format!("(see above): {} -> {}", humanize_fact(fact), tag)
            }
        }
    }
}

/// Humanize a rule label: collapse event decomposition predicates.
/// "gerku ∧ gerku_x1 ∧ gerku_x2 → danlu ∧ danlu_x1 ∧ danlu_x2" → "gerku → danlu"
fn humanize_rule_label(label: &str) -> String {
    if let Some((lhs, rhs)) = label.split_once(" → ") {
        let lhs_base = collapse_role_predicates(lhs);
        let rhs_base = collapse_role_predicates(rhs);
        format!("{} → {}", lhs_base, rhs_base)
    } else {
        label.to_string()
    }
}

/// Given "gerku ∧ gerku_x1 ∧ gerku_x2", return just "gerku".
/// Strips all _xN role predicates, keeping only base predicate names.
fn collapse_role_predicates(s: &str) -> String {
    let parts: Vec<&str> = s.split(" ∧ ").collect();
    let bases: Vec<&str> = parts
        .iter()
        .filter(|p| !p.contains("_x"))
        .copied()
        .collect();
    if bases.is_empty() {
        // All parts were role predicates — use the first one's base
        if let Some(first) = parts.first() {
            if let Some(underscore) = first.rfind('_') {
                return first[..underscore].to_string();
            }
        }
        s.to_string()
    } else {
        bases.join(" ∧ ")
    }
}

fn format_proof_step(trace: &ProofTrace, idx: u32, indent: usize, out: &mut String) {
    let step = &trace.steps[idx as usize];
    for _ in 0..indent {
        out.push_str("  ");
    }
    out.push_str(&step.rule.trace_display(step.holds));
    out.push('\n');
    for &child in &step.children {
        format_proof_step(trace, child, indent + 1, out);
    }
}
