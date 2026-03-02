#!/usr/bin/env python3
"""Tests for lojban_classifier.py — deterministic Lojban→English classifier."""

import os
import sys

# Ensure python/ is importable
sys.path.insert(0, os.path.dirname(__file__))
from lojban_classifier import (
    parse, classify, to_fol, to_english, format_classified,
    process_lines, lookup, lookup_se, fol_name, en_terms,
)


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  PARSE TESTS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def test_parse_named_ground():
    """la .nibli. cu logji ciste — named entity, tanru predicate."""
    s = parse("la .nibli. cu logji ciste")
    assert s["quantifier"] is None
    assert s["gadri"] == "la"
    assert s["subject"] == (None, ["nibli"])
    assert s["pred_parts"] == [(False, None, ["logji", "ciste"])]
    assert s["pred_objects"] == []
    assert s["pred_place_tags"] == []


def test_parse_simple_universal():
    """ro lo gerku cu danlu — universal rule, single words."""
    s = parse("ro lo gerku cu danlu")
    assert s["quantifier"] == "ro"
    assert s["gadri"] == "lo"
    assert s["subject"] == (None, ["gerku"])
    assert s["pred_parts"] == [(False, None, ["danlu"])]


def test_parse_converted_predicate():
    """ro lo birti cu se krinu — converted predicate."""
    s = parse("ro lo birti cu se krinu")
    assert s["subject"] == (None, ["birti"])
    assert s["pred_parts"] == [(False, "se", ["krinu"])]


def test_parse_converted_subject():
    """ro lo se krinu cu logji — converted subject."""
    s = parse("ro lo se krinu cu logji")
    assert s["subject"] == ("se", ["krinu"])
    assert s["pred_parts"] == [(False, None, ["logji"])]


def test_parse_negated_predicate():
    """ro lo logji cu na xanri — negated predicate."""
    s = parse("ro lo logji cu na xanri")
    assert s["pred_parts"] == [(True, None, ["xanri"])]


def test_parse_tanru_with_embedded_se():
    """ro lo prenu cu menli se ponse — tanru with se in middle."""
    s = parse("ro lo prenu cu menli se ponse")
    assert s["pred_parts"] == [(False, None, ["menli", "se", "ponse"])]


def test_parse_tanru_subject():
    """ro lo barda danlu cu sutra — tanru subject."""
    s = parse("ro lo barda danlu cu sutra")
    assert s["subject"] == (None, ["barda", "danlu"])
    assert s["pred_parts"] == [(False, None, ["sutra"])]


def test_parse_abstraction_object():
    """ro lo ctuca cu se djica lo nu tadni — abstraction object."""
    s = parse("ro lo ctuca cu se djica lo nu tadni")
    assert s["pred_parts"] == [(False, "se", ["djica"])]
    assert s["pred_objects"] == [("nu", False, None, ["tadni"])]


def test_parse_multi_part_predicate():
    """ro lo se bilga cu se curmi na se fanta — two predicate parts."""
    s = parse("ro lo se bilga cu se curmi na se fanta")
    assert len(s["pred_parts"]) == 2
    assert s["pred_parts"][0] == (False, "se", ["curmi"])
    assert s["pred_parts"][1] == (True, "se", ["fanta"])


def test_parse_converted_tanru_subject():
    """ro lo se ponse datni cu se kurji — converted + tanru subject."""
    s = parse("ro lo se ponse datni cu se kurji")
    assert s["subject"] == ("se", ["ponse", "datni"])
    assert s["pred_parts"] == [(False, "se", ["kurji"])]


def test_parse_negated_object():
    """ro lo se kurji datni cu se fanta lo na se curmi — negated converted object."""
    s = parse("ro lo se kurji datni cu se fanta lo na se curmi")
    assert s["pred_parts"] == [(False, "se", ["fanta"])]
    assert s["pred_objects"] == [("description", True, "se", ["curmi"])]


def test_parse_place_tag():
    """lo xanri fanta bitmu cu se zbasu fi lo logji — fi place tag."""
    s = parse("lo xanri fanta bitmu cu se zbasu fi lo logji")
    assert s["subject"] == (None, ["xanri", "fanta", "bitmu"])
    assert s["pred_parts"] == [(False, "se", ["zbasu"])]
    assert s["pred_place_tags"] == [("fi", ["logji"])]


def test_parse_negated_tanru_predicate():
    """lo xanri fanta bitmu cu na xanri ciste — negated tanru predicate."""
    s = parse("lo xanri fanta bitmu cu na xanri ciste")
    assert s["pred_parts"] == [(True, None, ["xanri", "ciste"])]


def test_parse_description_ground():
    """lo xanri fanta bitmu cu birti ciste — description ground fact."""
    s = parse("lo xanri fanta bitmu cu birti ciste")
    assert s["quantifier"] is None
    assert s["gadri"] == "lo"
    assert s["pred_parts"] == [(False, None, ["birti", "ciste"])]


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  CLASSIFY TESTS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def test_classify_ground():
    s = parse("la .nibli. cu logji ciste")
    assert classify(s) == "GROUND"


def test_classify_rule():
    s = parse("ro lo gerku cu danlu")
    assert classify(s) == "RULE"


def test_classify_axiom_birti_krinu():
    s = parse("ro lo birti cu se krinu")
    assert classify(s) == "AXIOM"


def test_classify_axiom_logji_xanri():
    s = parse("ro lo logji cu na xanri")
    assert classify(s) == "AXIOM"


def test_classify_axiom_logji_birti_nibli():
    s = parse("ro lo logji birti cu se nibli")
    assert classify(s) == "AXIOM"


def test_classify_not_axiom_mixed():
    """gerku is not in AXIOM_WORDS → RULE."""
    s = parse("ro lo gerku cu danlu")
    assert classify(s) == "RULE"


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  FOL TESTS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def test_fol_simple_universal():
    s = parse("ro lo gerku cu danlu")
    assert to_fol(s) == "∀x. dog(x) → animal(x)"


def test_fol_converted_predicate():
    s = parse("ro lo birti cu se krinu")
    assert to_fol(s) == "∀x. certain(x) → justified(x)"


def test_fol_negated_predicate():
    s = parse("ro lo logji cu na xanri")
    assert to_fol(s) == "∀x. logic(x) → ¬imaginary(x)"


def test_fol_tanru_subject():
    s = parse("ro lo barda danlu cu sutra")
    assert to_fol(s) == "∀x. big-animal(x) → fast(x)"


def test_fol_embedded_se():
    s = parse("ro lo prenu cu menli se ponse")
    assert to_fol(s) == "∀x. person(x) → mind-possessed(x)"


def test_fol_abstraction_object():
    s = parse("ro lo ctuca cu se djica lo nu tadni")
    assert to_fol(s) == "∀x. teacher(x) → desired(x, ∃e. learn(e))"


def test_fol_multi_part():
    s = parse("ro lo se bilga cu se curmi na se fanta")
    assert to_fol(s) == "∀x. obligated(x) → permitted(x) ∧ ¬blocked(x)"


def test_fol_negated_object():
    s = parse("ro lo se kurji datni cu se fanta lo na se curmi")
    assert to_fol(s) == "∀x. cared-for-data(x) → blocked(x, ¬permitted)"


def test_fol_named_ground():
    s = parse("la .nibli. cu logji ciste")
    assert to_fol(s) == "nibli ∈ logic-system"


def test_fol_place_tag():
    s = parse("lo xanri fanta bitmu cu se zbasu fi lo logji")
    assert to_fol(s) == "imaginary-block-wall BUILT-FROM logic"


def test_fol_description_ground():
    s = parse("lo xanri fanta bitmu cu birti ciste")
    assert to_fol(s) == "imaginary-block-wall ∈ certain-system"


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  ENGLISH TESTS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def test_english_simple_universal():
    s = parse("ro lo gerku cu danlu")
    assert to_english(s) == "Every dog. Is. An animal."


def test_english_adj_predicate():
    s = parse("ro lo danlu cu jmive")
    assert to_english(s) == "Every animal. Is. Alive."


def test_english_converted_predicate():
    s = parse("ro lo birti cu se krinu")
    assert to_english(s) == "Every certain. Is. Justified."


def test_english_negated_predicate():
    s = parse("ro lo logji cu na xanri")
    assert to_english(s) == "Every logic. Is. Not imaginary."


def test_english_named_ground():
    s = parse("la .nibli. cu logji ciste")
    assert to_english(s) == "Nibli. Is. A logic system."


def test_english_embedded_se():
    s = parse("ro lo prenu cu menli se ponse")
    assert to_english(s) == "Every person. Is. Mind possessed."


def test_english_multi_part():
    s = parse("ro lo se bilga cu se curmi na se fanta")
    assert to_english(s) == "Every obligated. Is. Permitted. And. Not blocked."


def test_english_abstraction_object():
    s = parse("ro lo ctuca cu se djica lo nu tadni")
    assert to_english(s) == "Every teacher. Is. Desired. Event-of learn."


def test_english_place_tag():
    s = parse("lo xanri fanta bitmu cu se zbasu fi lo logji")
    assert to_english(s) == "The imaginary block wall. Is. Built. From logic."


def test_english_negated_tanru():
    s = parse("lo xanri fanta bitmu cu na xanri ciste")
    assert to_english(s) == "The imaginary block wall. Is. Not imaginary system."


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  INTEGRATION TESTS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def test_format_classified():
    s = parse("ro lo gerku cu danlu")
    out = format_classified(s)
    assert "ro lo gerku cu danlu" in out
    assert "⊢ RULE" in out
    assert "∀x. dog(x) → animal(x)" in out
    assert "Every dog. Is. An animal." in out


def test_process_lines_with_comments():
    lines = [
        "# ni'o lo danlu klesi\n",
        "ro lo gerku cu danlu\n",
        "\n",
        "ro lo mlatu cu danlu\n",
    ]
    out = process_lines(lines)
    assert "── ni'o lo danlu klesi" in out
    assert "dog(x) → animal(x)" in out
    assert "cat(x) → animal(x)" in out


def test_process_lines_all_readme():
    """Integration: process every line of readme.lojban without errors."""
    readme_path = os.path.join(os.path.dirname(__file__), "..", "readme.lojban")
    if not os.path.exists(readme_path):
        return  # Skip if not present
    with open(readme_path, "r", encoding="utf-8") as f:
        lines = f.readlines()
    out = process_lines(lines)
    assert "ERROR" not in out, f"Parse errors found in readme.lojban:\n{out}"


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  LOOKUP TESTS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def test_lookup_known():
    assert lookup("gerku") == ("dog", "noun")


def test_lookup_unknown():
    assert lookup("zzzzz") == ("zzzzz", "unknown")


def test_lookup_se():
    assert lookup_se("krinu") == "justified"
    assert lookup_se("ponse") == "possessed"


def test_lookup_se_fallback():
    assert lookup_se("danlu") == "inverse-animal"


def test_fol_name_simple():
    assert fol_name(None, ["gerku"]) == "dog"


def test_fol_name_tanru():
    assert fol_name(None, ["logji", "ciste"]) == "logic-system"


def test_fol_name_converted():
    assert fol_name("se", ["krinu"]) == "justified"


def test_fol_name_converted_tanru():
    assert fol_name("se", ["ponse", "datni"]) == "possessed-data"


def test_fol_name_embedded_se():
    assert fol_name(None, ["menli", "se", "ponse"]) == "mind-possessed"


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  RUNNER
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

if __name__ == "__main__":
    # Simple test runner for when pytest is not available
    import inspect
    tests = [
        (name, obj) for name, obj in globals().items()
        if name.startswith("test_") and callable(obj)
    ]
    passed = 0
    failed = 0
    for name, fn in sorted(tests):
        try:
            fn()
            passed += 1
            print(f"  ✓ {name}")
        except AssertionError as e:
            failed += 1
            print(f"  ✗ {name}: {e}")
        except Exception as e:
            failed += 1
            print(f"  ✗ {name}: {type(e).__name__}: {e}")
    print(f"\n{passed} passed, {failed} failed, {passed + failed} total")
    sys.exit(1 if failed else 0)
