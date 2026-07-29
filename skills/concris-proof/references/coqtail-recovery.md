# Coqtail Recovery

Read this file after a timed-out, cancelled, or failed Coqtail lifecycle call.
Do not assume that the backend died or that its endpoint advanced.

## Recover the Session

1. Stop sending proof steps to the affected session.
2. Query `rocq_list`, then query `rocq_status` for the intended session.
3. If the session is live, compare its file and endpoint with the last accepted
   step.
4. If the endpoint is known and consistent, inspect goals and retry one
   sentence or a smaller source interval with a finite timeout.
5. If the session is missing, stopped, or attached to the wrong file, start a
   fresh session on the smallest relevant file and step to the needed point.

After any source edit, reload or restart before trusting goals. Treat a live
session over stale source as unusable.

## Recover the Tool

If `rocq_list` or `rocq_status` also fails:

1. Restart the Coqtail MCP service through the available MCP lifecycle control.
2. Query the session list again instead of assuming old sessions survived.
3. Start a fresh session if no trustworthy session remains.

Use a batch build only when lifecycle recovery fails or Coqtail cannot expose
the relevant error. State that reason, use the workspace Rocq shims, and follow
[Rocq resources and builds](resources-and-builds.md).

## Report the Outcome

Report a recovery failure when it prevents further proof work. Include the
failed lifecycle stage and whether a fresh session or bounded batch check was
attempted. Omit raw traces unless the user asks for them.
