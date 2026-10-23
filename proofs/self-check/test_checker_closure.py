"""The criterion model cannot silently survive changes to its reviewed source."""

import unittest

import extract
from checker_closure import check_checker_closure


class CheckerClosureTests(unittest.TestCase):
    def setUp(self):
        self.source = (extract.ROOT / "nibli-verify/spec/nibli_checker.nibli").read_text()

    def test_current_checker_and_comment_only_edits(self):
        check_checker_closure(self.source)
        check_checker_closure("# neg_dep_path has a reviewed least-closure model\n" + self.source)

    def test_missing_clause_and_weakened_cycle_test_fail(self):
        for changed in (
            self.source.replace("all $a, $b: neg_dep($a, $b) -> neg_dep_path($a, $b).", ""),
            self.source.replace("neg_dep_path($p, $p) ->", "dep_path($p, $p) ->"),
            self.source.replace('derived_only("dep_path").', 'admits("dep_path").'),
        ):
            with self.assertRaisesRegex(ValueError, "closure clauses changed"):
                check_checker_closure(changed)

    def test_extra_rule_or_fact_for_a_modeled_predicate_fails(self):
        for added in (
            'all $a, $b: pos_dep($a, $b) -> neg_dep_path($a, $b).',
            'unstratifiable_cycle("injected").',
        ):
            with self.assertRaisesRegex(ValueError, "closure clauses changed"):
                check_checker_closure(self.source + "\n" + added)


if __name__ == "__main__":
    unittest.main()
