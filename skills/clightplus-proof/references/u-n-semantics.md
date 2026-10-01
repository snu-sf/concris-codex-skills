# U/N semantics and symbolic execution

## Source locations

Inspect the checked-out versions instead of assuming these APIs are unchanged:

- `ClightPlus/compiler/ClightPlusFailureMode.v`
- `ClightPlus/compiler/ClightPlusgen.v`
- `ClightPlus/compiler/ClightPlusFungen.v`
- `ClightPlus/compiler/ClightPlusExprgen.v`
- `ClightPlus/proofmode/CProofMode.v`
- `CRIS/theories/common/Events.v` or the active CRIS checkout equivalent

## Mode roles

`FailureMode.U` selects `triggerUB`, `unwrapU`, `ccallU`, and `cfunU` at
parameterized sites. `FailureMode.N` selects the NB counterparts. `compile` is
normally the U alias; `compileN` uses N. `InitI` and external-call modules also
have mode-aware constructors in compatible checkouts.

Mode selection only affects operations routed through `FailureMode`. In the
current checkout, raw `triggerUB` and U-only option notation remain in compiler
paths, and `FailureMode.fail` is not used by the compiler. Trace every reachable
failure to its definition. A source path that still executes raw `triggerUB`
does not establish the intended NB-based safety claim.

`ccallN` checks the return `Any.t` with the NB downcast, and `cfunN` checks the
argument with the NB downcast. Thus a U/N whole-program refinement can cover
typed call-boundary failure as well as failures inside a callee.

Use the exact theorem direction:

```text
refines target-with-U source-with-N
ISim.sim_fun source-with-N target-with-U ...
```

Do not reverse this because the source proof executes first in simulation
tactics.

Search for a generic U/N theorem before planning automation. In the current
checkout there is no general refinement from arbitrary `compile` output to
`compileN`, and no general U/N initializer theorem. Generated function traces
and initializer lookup obligations remain program-specific proof work.

## Classify failure sites

Before claiming a safety property, classify every relevant partial operation:

- C execution failure: use N in the source when the implementation exposes a
  mode parameter at that site.
- Memory semantic failure: use the repository's N memory module and retain its
  concrete-success relation to the U memory module.
- Typed call-boundary failure: use both `ccallN` and `cfunN` in the source.
- Malformed generated Clight, missing globals, unsupported externals, and tool
  failures: discharge as input conditions or document them; do not relabel them
  as C UB without a semantic argument.

Search for direct `triggerUB`, raw `?`/`unwrapU`, U aliases, and unmodeled
external calls reachable from the program. Mode propagation is not proof that
every ISO C UB class has been converted. Pay particular attention to
indeterminate values, pointer arithmetic bounds/liveness, signed overflow,
float-to-integer casts, shifts, volatile access, and architecture assumptions.

## Step mode-aware runtime iterators

Current `CProofMode.clight_step1` variants may match only this head:

```coq
ITree.iter (ClightPlusFungen.handle_runtime_env _ _ _ _) state
```

An N proof can instead expose:

```coq
ITree.iter
  (ClightPlusFungen.handle_runtime_env_with FailureMode.N _ _ _ _)
  state
```

First search for a public tactic supporting `_with`. If absent and local
helpers are authorized, use `cShowS`/`cShowT` to confirm this head, then mirror
only the iterator-opening step:

```coq
rewrite {1}unfold_iter
  {1}/ClightPlusFungen.handle_runtime_env_with
```

Wrap this in a proof-local source/target helper that preserves the existing
`cShow*`, `cSteps*`, `resolve_cenv`, and `cHide*` protocol. Do not copy the
interpreter, unfold all of `compileN`, or modify `CProofMode` merely for one
client proof. Stop broad unfolding if it exposes a large runtime match; advance
one statement at a time. Exact step counts and AST-specific cast reductions
belong in the client proof, not a shared tactic.

Also inspect function-start and inline wrappers. Current `clightStartFunSim` and
`clInlineS`/`clInlineT` variants may unfold U aliases such as
`function_entry_c`, `interp_runtime_env`, and `interp_function`. For mixed U/N
simulation, start with ordinary ConCRIS tactics and unfold only the
corresponding mode-generic `_with` definitions needed to reach the iterator. Do
not treat a U-only wrapper as mode-generic.

## Open one expression combinator

When ordinary stepping exposes a mode-generic expression combinator on only one
side, use the matching one-step wrapper:

- `clDerefS`/`clDerefT` for `deref_loc_c_with`
- `clCastS`/`clCastT` for `sem_cast_c_with`
- `clCmpS`/`clCmpT` for `sem_cmp_c_with`
- `clBinarithS`/`clBinarithT` for `sem_binarith_c_with`
- `clSubS`/`clSubT` for `sem_sub_c_with`

Each wrapper selects the named side with `replace_s` or `replace_t` and unfolds
only that semantic operation, including its immediate body wrapper where one
exists. It does not finish the resulting CRIS events. Follow it with the
smallest appropriate `cStepS`/`cStepT` sequence.

Before applying a wrapper, use `cShowS` or `cShowT` if the head is unclear. If
the wrapper fails, do not add it to an unconditional chain: inspect whether a
different combinator, an outer bind, or a concrete cast reduction is blocking.
Fall back to a proof-local `replace_s`/`replace_t` that unfolds one exact head
only. Stop and report an abstraction gap if progress requires a shared tactic
to capture a concrete AST temporary, a hypothesis name, or an exact step count.
