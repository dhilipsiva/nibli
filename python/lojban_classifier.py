#!/usr/bin/env python3
"""
lojban_classifier.py — Deterministic Lojban sentence classifier.

Parses Lojban sentences and produces for each:
  ⊢ TYPE    FOL notation
  ⊢         Robotic English translation

No LLM. No approximation. Every translation is mechanically derived.

Usage:
    python3 python/lojban_classifier.py readme.lojban
    python3 python/lojban_classifier.py readme.lojban -o classified.txt
"""

import sys
import argparse


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  DICTIONARY
#  Each entry: (english, word_type, se_english)
#  word_type: "noun" | "adj" | "verb"
#  se_english: translation when prefixed with se (x1/x2 swap)
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

GISMU = {
    "logji":      ("logic",       "noun",  None),
    "ciste":      ("system",      "noun",  None),
    "birti":      ("certain",     "adj",   None),
    "skami":      ("computer",    "noun",  None),
    "krinu":      ("reason",      "noun",  "justified"),
    "xanri":      ("imaginary",   "adj",   None),
    "nibli":      ("derive",      "verb",  "derived"),
    "gerku":      ("dog",         "noun",  None),
    "mlatu":      ("cat",         "noun",  None),
    "cipni":      ("bird",        "noun",  None),
    "finpe":      ("fish",        "noun",  None),
    "since":      ("snake",       "noun",  None),
    "cribe":      ("bear",        "noun",  None),
    "xirma":      ("horse",       "noun",  None),
    "bakni":      ("bovine",      "noun",  None),
    "kumte":      ("camel",       "noun",  None),
    "ratcu":      ("rat",         "noun",  None),
    "mabru":      ("mammal",      "noun",  None),
    "respa":      ("reptile",     "noun",  None),
    "insekto":    ("insect",      "noun",  None),
    "danlu":      ("animal",      "noun",  None),
    "jmive":      ("alive",       "adj",   None),
    "tricu":      ("tree",        "noun",  None),
    "spati":      ("plant",       "noun",  None),
    "prenu":      ("person",      "noun",  None),
    "nanmu":      ("man",         "noun",  None),
    "ninmu":      ("woman",       "noun",  None),
    "verba":      ("child",       "noun",  None),
    "nakni":      ("male",        "noun",  None),
    "fetsi":      ("female",      "noun",  None),
    "menli":      ("mind",        "noun",  None),
    "ponse":      ("possess",     "verb",  "possessed"),
    "bangu":      ("language",    "noun",  None),
    "barda":      ("big",         "adj",   None),
    "cmalu":      ("small",       "adj",   None),
    "sutra":      ("fast",        "adj",   None),
    "masno":      ("slow",        "adj",   None),
    "ckaji":      ("property",    "noun",  "attributed"),
    "skari":      ("colour",      "noun",  None),
    "xunre":      ("red",         "adj",   None),
    "blanu":      ("blue",        "adj",   None),
    "pelxu":      ("yellow",      "adj",   None),
    "crino":      ("green",       "adj",   None),
    "grusi":      ("grey",        "adj",   None),
    "ctuca":      ("teacher",     "noun",  None),
    "mikce":      ("doctor",      "noun",  None),
    "flaselcu'u": ("lawyer",      "noun",  None),
    "zdani":      ("home",        "noun",  None),
    "dinju":      ("building",    "noun",  None),
    "briju":      ("office",      "noun",  None),
    "ckule":      ("school",      "noun",  None),
    "karce":      ("car",         "noun",  None),
    "marce":      ("vehicle",     "noun",  None),
    "trene":      ("train",       "noun",  None),
    "vinji":      ("airplane",    "noun",  None),
    "ladru":      ("milk",        "noun",  None),
    "cidja":      ("food",        "noun",  None),
    "grute":      ("fruit",       "noun",  None),
    "nanba":      ("bread",       "noun",  None),
    "rectu":      ("meat",        "noun",  None),
    "djacu":      ("water",       "noun",  None),
    "litki":      ("liquid",      "noun",  None),
    "solri":      ("sun",         "noun",  None),
    "gusni":      ("luminous",    "adj",   None),
    "fagri":      ("fire",        "noun",  None),
    "djica":      ("desire",      "verb",  "desired"),
    "tadni":      ("learn",       "verb",  None),
    "kanro":      ("healthy",     "adj",   None),
    "javni":      ("rule",        "noun",  None),
    "flalu":      ("law",         "noun",  None),
    "bilga":      ("obligate",    "verb",  "obligated"),
    "curmi":      ("permit",      "verb",  "permitted"),
    "fanta":      ("block",       "verb",  "blocked"),
    "datni":      ("data",        "noun",  None),
    "kurji":      ("care-for",    "verb",  "cared-for"),
    "zbasu":      ("build",       "verb",  "built"),
    "bitmu":      ("wall",        "noun",  None),
}

# Words whose presence (both subject and predicate) marks a rule as AXIOM
AXIOM_WORDS = frozenset(["birti", "xanri", "logji", "krinu", "nibli"])

CONVERTERS = frozenset(["se", "te", "ve", "xe"])


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  LOOKUP HELPERS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def lookup(word):
    """Look up gismu. Returns (english, type)."""
    entry = GISMU.get(word)
    if entry:
        return entry[0], entry[1]
    return word, "unknown"


def lookup_se(word):
    """Look up se + gismu translation."""
    entry = GISMU.get(word)
    if entry and entry[2]:
        return entry[2]
    en, _ = lookup(word)
    return f"inverse-{en}"


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  PARSER
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def parse_subject_tokens(tokens):
    """Parse subject tokens → (converted, words) tuple."""
    converted = None
    words = []
    for tok in tokens:
        if tok in CONVERTERS and not words:
            converted = tok
        else:
            words.append(tok)
    return converted, words


def parse_predicate_tokens(tokens):
    """Parse predicate tokens → (parts, objects, place_tags).

    parts:      list of (negated, converted, words) tuples
    objects:    list of (obj_type, negated, converted, words) tuples
    place_tags: list of (tag, words) tuples
    """
    parts = []
    objects = []
    place_tags = []

    neg = False
    conv = None
    words = []
    i = 0

    while i < len(tokens):
        tok = tokens[i]

        if tok == "fi":
            # Flush current part
            if words or conv is not None:
                parts.append((neg, conv, words))
                neg, conv, words = False, None, []
            i += 1
            # Expect: lo WORDS
            if i < len(tokens) and tokens[i] == "lo":
                i += 1
                fi_words = []
                while i < len(tokens):
                    fi_words.append(tokens[i])
                    i += 1
                place_tags.append(("fi", fi_words))
            continue

        if tok == "lo":
            # Flush current part
            if words or conv is not None:
                parts.append((neg, conv, words))
                neg, conv, words = False, None, []
            i += 1
            obj_type = "description"
            obj_neg = False
            obj_conv = None
            obj_words = []
            if i < len(tokens) and tokens[i] == "nu":
                obj_type = "nu"
                i += 1
            if i < len(tokens) and tokens[i] == "na":
                obj_neg = True
                i += 1
            if i < len(tokens) and tokens[i] in CONVERTERS:
                obj_conv = tokens[i]
                i += 1
            while i < len(tokens) and tokens[i] not in ("lo", "fi"):
                obj_words.append(tokens[i])
                i += 1
            objects.append((obj_type, obj_neg, obj_conv, obj_words))
            continue

        if tok == "na":
            if words:
                # Flush current as a part, start continuation
                parts.append((neg, conv, words))
                neg, conv, words = True, None, []
            else:
                neg = True
            i += 1
            continue

        if tok in CONVERTERS:
            if words:
                # Embedded in tanru: "menli se ponse"
                words.append(tok)
            else:
                conv = tok
            i += 1
            continue

        words.append(tok)
        i += 1

    if words or neg or conv is not None:
        parts.append((neg, conv, words))

    return parts, objects, place_tags


def parse(text):
    """Parse a Lojban sentence → structured dict.

    Returns: {
        quantifier: "ro" | None,
        gadri: "la" | "lo",
        subject: (converted, words),
        pred_parts: [(negated, converted, words), ...],
        pred_objects: [(obj_type, negated, converted, words), ...],
        pred_place_tags: [(tag, words), ...],
        raw: str,
    }
    """
    tokens = text.strip().split()
    result = {"raw": text.strip()}

    i = 0
    # Quantifier
    if tokens[i] == "ro":
        result["quantifier"] = "ro"
        i += 1
    else:
        result["quantifier"] = None

    # Gadri
    result["gadri"] = tokens[i]
    i += 1

    # Subject
    if result["gadri"] == "la":
        name = tokens[i].strip(".")
        result["subject"] = (None, [name])
        i += 1
    else:
        subj_toks = []
        while i < len(tokens) and tokens[i] != "cu":
            subj_toks.append(tokens[i])
            i += 1
        result["subject"] = parse_subject_tokens(subj_toks)

    # Skip cu
    if i >= len(tokens) or tokens[i] != "cu":
        raise ValueError(f"Expected 'cu' at position {i}, got '{tokens[i] if i < len(tokens) else 'EOF'}'")
    i += 1

    # Predicate
    pred_toks = tokens[i:]
    parts, objects, place_tags = parse_predicate_tokens(pred_toks)
    result["pred_parts"] = parts
    result["pred_objects"] = objects
    result["pred_place_tags"] = place_tags

    return result


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  CLASSIFIER
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def classify(sent):
    """Classify as GROUND, RULE, or AXIOM."""
    if sent["quantifier"] is None:
        return "GROUND"

    # Collect all content words (excluding modifiers like se/na)
    all_words = set()
    _, subj_words = sent["subject"]
    all_words.update(subj_words)
    for _, _, pwords in sent["pred_parts"]:
        for w in pwords:
            if w not in CONVERTERS:
                all_words.update([w])

    # AXIOM if all content words are in the axiom set
    if all_words and all_words <= AXIOM_WORDS:
        return "AXIOM"

    return "RULE"


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  FOL NAME HELPERS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def fol_name(converted, words):
    """Convert (converted, words) to a FOL predicate name."""
    if not words:
        return "?"

    # Embedded se in tanru: ["menli", "se", "ponse"]
    if "se" in words:
        se_idx = words.index("se")
        mods = [lookup(w)[0] for w in words[:se_idx]]
        head = words[se_idx + 1] if se_idx + 1 < len(words) else "?"
        head_en = lookup_se(head)
        rest = [lookup(w)[0] for w in words[se_idx + 2:]]
        return "-".join(mods + [head_en] + rest)

    # Converted prefix: se krinu → justified
    if converted == "se":
        if len(words) == 1:
            return lookup_se(words[0])
        first_en = lookup_se(words[0])
        rest = [lookup(w)[0] for w in words[1:]]
        return "-".join([first_en] + rest)

    return "-".join(lookup(w)[0] for w in words)


def fol_name_obj(obj_conv, obj_words):
    """FOL name for an object clause."""
    if not obj_words:
        return "?"
    if obj_conv == "se":
        if len(obj_words) == 1:
            return lookup_se(obj_words[0])
        return "-".join([lookup_se(obj_words[0])] + [lookup(w)[0] for w in obj_words[1:]])
    return "-".join(lookup(w)[0] for w in obj_words)


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  FOL GENERATOR
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def to_fol(sent):
    """Generate First-Order Logic notation."""
    subj_conv, subj_words = sent["subject"]
    # Named entities (la) keep raw name, descriptions get translated
    if sent["gadri"] == "la":
        subj = subj_words[0] if subj_words else "?"
    else:
        subj = fol_name(subj_conv, subj_words)

    # Build predicate atoms
    atoms = []
    for neg, conv, pwords in sent["pred_parts"]:
        name = fol_name(conv, pwords)
        prefix = "¬" if neg else ""
        atoms.append((prefix, name))

    # Build object strings
    obj_strs = []
    for obj_type, obj_neg, obj_conv, obj_words in sent["pred_objects"]:
        oname = fol_name_obj(obj_conv, obj_words)
        if obj_type == "nu":
            obj_strs.append(f"∃e. {oname}(e)")
        else:
            opfx = "¬" if obj_neg else ""
            obj_strs.append(f"{opfx}{oname}")

    # Place tag strings
    tag_strs = []
    for _, twords in sent["pred_place_tags"]:
        tag_strs.append("-".join(lookup(w)[0] for w in twords))

    if sent["quantifier"] == "ro":
        # Universal: ∀x. subject(x) → pred(x)
        pred_parts = []
        for i, (pfx, name) in enumerate(atoms):
            arg = "x"
            if i < len(obj_strs):
                arg = f"x, {obj_strs[i]}"
            pred_parts.append(f"{pfx}{name}({arg})")
        pred = " ∧ ".join(pred_parts)
        if tag_strs:
            pred += f" FROM {tag_strs[0]}"
        return f"∀x. {subj}(x) → {pred}"

    # Ground fact
    pred_parts = [f"{pfx}{name}" for pfx, name in atoms]
    pred = " ∧ ".join(pred_parts)
    if tag_strs:
        return f"{subj} BUILT-FROM {tag_strs[0]}"
    return f"{subj} ∈ {pred}"


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  ENGLISH HELPERS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def en_terms(converted, words, negated=False):
    """Translate (converted, words) to English phrase."""
    if not words:
        return "?"

    # Embedded se in tanru
    if "se" in words:
        se_idx = words.index("se")
        mods = [lookup(w)[0] for w in words[:se_idx]]
        head = words[se_idx + 1] if se_idx + 1 < len(words) else "?"
        head_en = lookup_se(head)
        rest = [lookup(w)[0] for w in words[se_idx + 2:]]
        en = " ".join(mods + [head_en] + rest)
    elif converted == "se":
        if len(words) == 1:
            en = lookup_se(words[0])
        else:
            en = lookup_se(words[0]) + " " + " ".join(lookup(w)[0] for w in words[1:])
    else:
        en = " ".join(lookup(w)[0] for w in words)

    if negated:
        en = f"not {en}"
    return en


def head_type(converted, words):
    """Determine the word type of the predicate head."""
    if not words:
        return "noun"
    # Embedded se or external conversion → adjective-like
    if "se" in words or converted:
        return "adj"
    _, wtype = lookup(words[-1])
    return wtype


def add_article(phrase):
    """Add a/an article."""
    if phrase and phrase[0].lower() in "aeiou":
        return f"an {phrase}"
    return f"a {phrase}"


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  ENGLISH GENERATOR
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def to_english(sent):
    """Generate robotic English translation."""
    subj_conv, subj_words = sent["subject"]
    # Named entities (la) keep raw name, descriptions get translated
    if sent["gadri"] == "la":
        subj_en = subj_words[0] if subj_words else "?"
    else:
        subj_en = en_terms(subj_conv, subj_words)

    # Subject phrase
    if sent["gadri"] == "la" and sent["quantifier"] is None:
        subj_str = subj_en.capitalize()
    elif sent["quantifier"] == "ro":
        subj_str = f"Every {subj_en}"
    else:
        subj_str = f"The {subj_en}"

    # Predicate phrases
    pred_phrases = []
    for neg, conv, pwords in sent["pred_parts"]:
        phrase = en_terms(conv, pwords, negated=neg)
        # Add article for non-negated noun predicates
        if not neg and head_type(conv, pwords) == "noun":
            phrase = add_article(phrase)
        pred_phrases.append(phrase.capitalize())

    # Object phrases
    obj_phrases = []
    for obj_type, obj_neg, obj_conv, obj_words in sent["pred_objects"]:
        obj_en = en_terms(obj_conv, obj_words, negated=obj_neg)
        if obj_type == "nu":
            obj_phrases.append(f"Event-of {obj_en}")
        else:
            obj_phrases.append(f"The {obj_en}")

    # Place tag phrases
    tag_phrases = []
    for _, twords in sent["pred_place_tags"]:
        tag_phrases.append(f"From {' '.join(lookup(w)[0] for w in twords)}")

    # Assemble: Subject. Is. Predicate. [And. Continuation.] [Object.] [Tag.]
    segments = [subj_str]
    for i, phrase in enumerate(pred_phrases):
        segments.append("Is" if i == 0 else "And")
        segments.append(phrase)
    for op in obj_phrases:
        segments.append(op)
    for tp in tag_phrases:
        segments.append(tp)

    return ". ".join(segments) + "."


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  OUTPUT FORMATTER
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def format_classified(sent):
    """Format a single classified sentence."""
    cls = classify(sent)
    fol = to_fol(sent)
    eng = to_english(sent)
    raw = sent["raw"]
    return f"{raw}\n⊢ {cls:<8}{fol}\n⊢         {eng}"


def process_lines(lines):
    """Process lines of Lojban text. Returns classified output string."""
    output = []
    for line in lines:
        stripped = line.rstrip("\n").strip()
        if not stripped:
            output.append("")
            continue
        if stripped.startswith("#"):
            header = stripped[1:].strip()
            pad = max(0, 50 - len(header))
            output.append(f"\n── {header} {'─' * pad}")
            continue
        try:
            sent = parse(stripped)
            output.append(format_classified(sent))
        except Exception as e:
            output.append(f"{stripped}\n⊢ ERROR   {e}")
    return "\n".join(output)


def process_file(input_path):
    """Process a .lojban file. Returns classified output string."""
    with open(input_path, "r", encoding="utf-8") as f:
        lines = f.readlines()
    return process_lines(lines)


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  MAIN
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def main():
    ap = argparse.ArgumentParser(description="Deterministic Lojban sentence classifier")
    ap.add_argument("input", help="Path to .lojban file")
    ap.add_argument("-o", "--output", help="Output file (default: stdout)")
    args = ap.parse_args()

    result = process_file(args.input)
    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(result + "\n")
        print(f"Written to {args.output}")
    else:
        print(result)


if __name__ == "__main__":
    main()
