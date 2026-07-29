# Rocq Resources and Builds

Read this file before a batch build, after dependency metadata becomes stale,
or when a Rocq backend is refused or killed under memory pressure.

## Read the Workspace Policy

Treat the checked-out workspace and runtime configuration as the source of
truth. Before invoking Rocq:

1. Read the applicable `AGENTS.md`, `CLAUDE.md`, and repository build
   instructions.
2. Locate the active commands with `command -v rocq coqc coqidetop`.
3. Inspect any wrapper or shim those commands resolve to, including documented
   environment overrides, admission checks, and memory limits.
4. If the workspace provides a required shim, use it for every Rocq invocation.
   Do not bypass its checks unless the user explicitly authorizes that action.

Useful runtime checks include:

```sh
env | rg '^CODEX_COQ_'
command -v rocq coqc coqidetop
rg '^MemAvailable:' /proc/meminfo
systemctl --user show rocq.slice \
  -p MemoryCurrent -p MemoryHigh -p MemoryMax -p MemorySwapMax
```

Run only the checks supported by the host. Do not assume systemd, cgroups, a
particular wrapper path, or fixed numeric limits.

## Interpret Memory Controls

- A backend memory maximum is an upper bound, not reserved memory.
- An admission refusal is a scheduling signal. Close stale Coqtail sessions,
  reduce build parallelism, or retry after memory pressure falls.
- Verify whether proof backends and agents share one aggregate memory limit
  before reasoning about total headroom.
- Do not disable workspace admission or memory checks merely to start another
  backend.

## Plan a Batch Build

1. Prefer the smallest exact `.vo` target and a focused dependency closure.
2. Follow the workspace's documented cap and parallelism policy.
3. If no policy exists, begin with one job and increase only after observing
   safe memory usage.
4. Never run an unbounded `make -j`.

In a CRIS repository, validate multiple `.vo` targets through one generated
makefile invocation:

```sh
make -f Makefile.coq -jN target1.vo target2.vo
```

Do not request several `.vo` targets from the top-level `make`; its pattern
recipes may launch independent sub-makes, duplicate dependencies, and race on
generated files.

## Repair Build Metadata

Treat `_CoqProject`, `Makefile.coq`, and similar generated files according to
the repository's tracked build rules. When the tracked `Makefile` generates
ignored metadata, regenerate it through that target, commonly:

```sh
make Makefile.coq
```

After a checkout or rebase changes the source or VFILES graph, regenerate
metadata before validating clients.

If a build reports inconsistent assumptions or a missing external/submodule
`.vo`, stop editing the client proof. Rebuild the named core importer and its
dependency closure in order, then reproduce the client error against
consistent artifacts.
