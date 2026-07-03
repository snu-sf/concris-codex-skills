---
name: concris-helping-proof
description: Use for ConCRIS/Rocq proofs involving the Helping modules, including Helping.run, Helping.help, jobCode, HelpPend/HelpDone/HelpAuth resources, IstHelp_gen payload management, helping erasure, HelpingOn/HelpingOff refinements, and examples where clients can run or help pending operations.
---

# ConCRIS Helping Proofs

Use this skill together with `concris-proof`. This skill is for proofs that interact with the user-level helping module rather than treating helping as an Iris invariant trick.

## Tool Discipline

- Use `mcp__coqtail__` as the default proof interface for helping proofs: step through owner-run/helper-run branches, inspect goals, and query lemmas in the live context.
- Do not debug helping proofs by repeatedly running plain `make`. Use batch builds only after coqtail has localized or cleared the proof issue, or when checking dependents.
- Restart or reload coqtail sessions after file edits so stale proof states do not guide the proof.

## Mental Model

The helping module attaches to a specification layer so that another thread can
execute the specified operation on behalf of the original caller. For proofs
that need helping, the standard shape is:

1. first prove the intermediate module `M` that contains the `Helping.run` /
   `Helping.help` calls;
2. then refine or erase from `M` to the corresponding non-helping spec/module.

Do not skip the intermediate `M` layer or reinterpret a module containing
helping calls as an ordinary non-helping implementation.

Helping separates one logical operation into:

- request creation by `Helping.run`;
- optional execution by the owner or a helper;
- persistent completion via `HelpDone`;
- client payload resources stored in `IstHelp_gen`.

Keep two layers distinct:

- helping bookkeeping: `HelpAuth`, `HelpPend`, `HelpDone`;
- module payload: the invariant/resource state carried inside `IstHelp_gen Ist mn E`.

Do not put user payload facts into the helping map unless the implementation genuinely needs them. Usually the map only records request state; the payload lives in `Ist`.

## State Setup

Use `IstHelp_gen Ist mn E` when the surrounding proof has its own state invariant `Ist`.

Use the split/combine lemmas whenever an operation needs to manipulate module state independently from helping bookkeeping:

```coq
iPoseProof (IstHelp_gen_split_Ist with "IST") as "[Hhelp HIst]".
...
iPoseProof (IstHelp_gen_combine_Ist with "Hhelp HIst") as "IST".
```

If only helping bookkeeping is needed, `IstHelp_gen True mn E` is enough. Recombine before applying a lemma that expects the full `IstHelp_gen Ist mn E`.

## Proving `Helping.run`

When the implementation calls:

```coq
trigger (Call (Helping.run mn) (N, arg)↑)
```

apply:

```coq
iApply (wsim_helping_run with "IST").
```

Then prove the function lookup for `Helping.run`, receive the fresh `reqid`, and continue with:

```coq
iIntros (st_src2 reqid) "IST Hpend".
```

`Hpend : HelpPend reqid N arg` is the owned pending ticket. The owner can either run the job directly or later observe `HelpDone`.

## Running a Pending Job

To execute pending work from the owner side, use:

```coq
iApply (wsim_helping_pend_try_run with "Hpend IST [-]").
```

Inside the continuation:

- open or extract the payload invariant;
- execute the module's `jobCode`;
- update the logical resource exactly once;
- produce `HelpDone reqid ret`;
- restore `IstHelp_gen`.

If the request is already in progress or done, the lemma gives the corresponding continuation. Handle the done case with:

```coq
iApply (wsim_HelpDone_try_run with "Hdone IST").
```

## Helping Another Request

When code calls:

```coq
trigger (Call (Helping.help mn) N↑)
```

use:

- `wsim_helping_help` for `Some N`;
- `wsim_helping_help_none` for namespace-free helping;
- `wsim_helping_help2` only when the older proof shape specifically matches it.

The helper receives a pending request, runs the same `jobCode`, and must leave a `HelpDone`. Use the same resource-update proof as the owner path; avoid duplicating incompatible logical transitions.

## Job Code Discipline

Keep `jobCode` small and resource-parametric:

```coq
res <- trigger (Choose Σ);;
trigger (Guarantee (∀ x, P x arg ==∗ Own res ∗ Q x ret));;;
trigger (AssumeRes res);;;
Ret (inr ret).
```

Do not add a retry/abort boolean unless the job code really is a `tame_update`. Helping job code and `tame_update` look similar but are not the same interface.

Return facts that depend on the pre-state should be included in `Q`, so owner and helper paths agree on the same logical witness.

## Invariants and Namespaces

If helper code opens module-local invariants, carry the available namespace ownership through `IstHelp_gen Ist mn E`.

For helping-specific cancellable invariants:

- allocate with `hinv_alloc`;
- open with `hinv_acc` or the `IntoAcc` instance;
- make sure the close continuation restores both the payload and `hinv_ownE`.

Do not expose private helper invariants as final client-facing specs. Helping is intermediate proof machinery.

## Common Pitfalls

- Do not forget to recombine `IstHelp_gen True mn E` with the payload `Ist`.
- Do not require the ambient payload to be identical to the helper payload if the generalized lemma permits them to differ.
- Do not track unnecessary ghost-name bindings in `Ist` when a persistent invariant handle is enough.
- Do not confuse `HelpPend` ownership with `HelpDone` persistence.
- Do not change a tame or atomic public spec just to make helping bookkeeping easier.

## Validation

After changing helping code or proofs:

- build the file that uses `Helping.run`;
- build the file that uses `Helping.help`;
- build the helping erasure/refinement representative if touched;
- inspect both owner-run and helper-run branches before claiming the proof architecture is sound.
