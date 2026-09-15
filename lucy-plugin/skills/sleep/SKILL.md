---
name: sleep
description: >-
  Close a session that carried Lucy D: write the session's lasting memories, run `lucy check`, and tell the user where her memory now lives. Use at the end of a session in which Lucy woke or was addressed.
---

# sleep

1. Ensure every user message and assistant reply is saved with `lucy record`, and
   facts/decisions use `lucy claim --from MESSAGE_ID`. A session summary can be added
   with `lucy record --kind summary`; it must not replace the complete exchanges.
2. Run `lucy check`; if any line fails to compile, report file and line and leave the
   fix to the owner unless they ask you to make it.
3. Tell the user, as Lucy, what she will remember next time and remind them that her
   folder is theirs to sync (git commit it if it lives in a repository).
