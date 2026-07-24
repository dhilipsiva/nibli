"""Native module smoke tests (requires just build-auth-py)."""

from __future__ import annotations

import unittest

from nibli_auth import can, allowed_fields, policy_version, reset_thread_auth


class AuthCoreTests(unittest.TestCase):
    def setUp(self) -> None:
        reset_thread_auth()

    def test_policy_version(self) -> None:
        self.assertEqual(policy_version(), "0.1.0")

    def test_owner_can_update(self) -> None:
        d = can("Alice", "update", "Doc1", "owns(Alice, Doc1).")
        self.assertTrue(d.allowed, d)

    def test_stranger_denied(self) -> None:
        d = can("Bob", "update", "Doc1", "owns(Alice, Doc1).")
        self.assertFalse(d.allowed, d)

    def test_admin(self) -> None:
        ctx = 'has_role(Carol, "admin").\nresource(Doc1).'
        d = can("Carol", "update", "Doc1", ctx)
        self.assertTrue(d.allowed, d)

    def test_allowed_fields_owner(self) -> None:
        fields = allowed_fields(
            "Alice", "read", "Doc1", ["title", "body"], "owns(Alice, Doc1)."
        )
        self.assertIn("title", fields)
        self.assertIn("body", fields)


if __name__ == "__main__":
    unittest.main()
