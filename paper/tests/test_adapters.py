"""Hand-derived adapter controls; no engine is its own oracle."""
import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import workloads as w


class Adapters(unittest.TestCase):
    def setUp(self):
        self.p = {"facts": [w.atom("dog", "Ada"), w.atom("cat", "Bea")],
                  "rules": [w.rule(w.atom("animal", "$x"), w.atom("dog", "$x"), w.atom("cat", "$x", neg=True))],
                  "queries": [w.atom("animal", "Ada"), w.atom("animal", "Bea")]}

    def test_three_hand_translations(self):
        self.assertEqual(w.nibli(self.p), ["all $x: dog($x) & ~cat($x) -> animal($x).", "dog(Ada).", "cat(Bea)."])
        self.assertEqual(w.clingo(self.p), 'dog("Ada").\ncat("Bea").\nanimal(X) :- dog(X), not cat(X).\nanswer(0) :- animal("Ada").\nanswer(1) :- animal("Bea").\n#show answer/1.\n')
        code, facts = w.souffle(self.p)
        self.assertIn('p_animal(X) :- p_dog(X), !p_cat(X).', code)
        self.assertIn('answer(0) :- p_animal("Ada").', code)
        self.assertNotIn('p_dog("Ada").', code)
        self.assertEqual(facts, {"p_cat": "Bea\n", "p_dog": "Ada\n"})

    def test_unsafe_rule_and_unrepresentable_input_are_refused(self):
        p = copy.deepcopy(self.p)
        p["rules"][0]["head"]["args"] = ["$y"]
        for renderer in (w.nibli, w.clingo, w.souffle):
            with self.assertRaises(ValueError):
                renderer(p)
        p = copy.deepcopy(self.p)
        p["facts"][0]["args"] = ['Ada"). animal(Bea']
        with self.assertRaises(ValueError):
            w.validate(p)

    def test_update_indices_refer_to_the_two_distinct_supports(self):
        p = w.updates(100, 11)
        req = w.request(p, mode="updates")
        self.assertEqual(req["statements"][p["updates"][0]["index"]], "prevents(Sanitizer, F0).")
        self.assertEqual(req["statements"][p["updates"][1]["index"]], "permits(Review, F0, Waiver).")
        self.assertEqual(req["statements"][p["updates"][4]["index"]], "prevents(Sanitizer, F1).")


if __name__ == "__main__":
    unittest.main()
