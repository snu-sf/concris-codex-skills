---
name: concris-proof
description: Use for ConCRIS/Rocq proof engineering tasks, including refinement proofs, Stack/Memory/Helping/Prophecy examples, tame specs, atomic specs with angelic nondeterminism, and proof debugging in CRIS repositories.
---

# ConCRIS Proof Engineering

Use this skill when working on ConCRIS/Rocq proofs. The goal is to preserve the intended proof architecture, not merely make the current goal disappear.

## Skill Maintenance

When proof work exposes a reusable mistake pattern, missing check, or better
debugging habit, propose a repo-agnostic skill update to the user. Do not edit
this skill or any other skill file unless the user explicitly approves it;
suggested additions should describe general proof roles, failure modes, or
validation habits, not branch-local names or one-off theorem names.

## Core Workflow

- Use Coqtail (`rocq_start`, `rocq_step_to`, `rocq_goals`, `rocq_query`) for
  proof inspection and debugging.
- Keep finite step/query timeouts and advance by one sentence or a small source
  interval. Use timeout `0` only for a deliberately awaited expensive command.
- Reload or restart the Coqtail session after editing before trusting its proof
  state.
- Use batch builds for final `.vo` confirmation, dependency checks, or a
  failure Coqtail cannot expose. State the reason before falling back.
- After a timeout, cancellation, or lifecycle error, read and follow
  [Coqtail recovery](references/coqtail-recovery.md) before reusing the session.
- Before a batch build, dependency-metadata repair, or memory-pressure
  diagnosis, read and follow
  [Rocq resources and builds](references/resources-and-builds.md).

## Spec Taxonomy

- **Concrete implementations** describe executable module behavior.
- **Atomic / angelic specs** use direct logical atomic updates, often via `Atomic.v`. Arbitrary `Take X` can be legitimate here when not proving a `real_mod`/prophecy-compatible layer.
- **Tame / prophecy-compatible specs** encode logical updates through `Choose`, `Guarantee`, and `AssumeRes`, usually via `TameUpdate` or `tame_triple`, so they can satisfy the `real_mod` discipline.
- **Intermediate proof machinery** includes helping modules, filters, invariants, and simulation structure. Do not mistake these for final client-facing specs.

Do not globally ban `Take`. Ban arbitrary `Take X` only when the proof depends on `real_mod`/prophecy adequacy.

For proofs against tame specifications, also use `concris-tame-proof`. For
Helping clients or erasure, also use `concris-helping-proof`. Keep
domain-specific rules in those skills.

## Tactic Map

- Setup/refinement: `cStartModSim`, `cStartFunSim`, `cInlineS`, `cInlineT`
- Calls: when both source and target are positioned at matching `Call` events, use `cCall "IST" as (ret st_src st_tgt) "IST"` rather than opening `wsim_call` directly with `iApply wsim_call; iFrame; ...`.
- Coinduction: `wsim_reset`, `cCoind`, `cByCoind`
- Scheduler/yield: `sYield`, `sYieldS`, `sYields`
- Atomic specs: `aStepS`, `aStepT`, `aUnfoldS`, `aUnfoldT`
- Tame specs: `tame_triple_src_pure`, `tame_triple_src`,
  `tame_triple_tgt`, `tame_triple_both`, `tame_update_src_commit`,
  `tame_update_tgt`, `tame_update_prepend_yield_src`,
  `tame_update_both`, `tForceT`, `tAaccIntro`
- Memory: `mLoad`, `mStore`, `mCas`, `mCmp`, `mAllocT`
- Helping: `wsim_helping_run`, `wsim_helping_pend_try_run`,
  `wsim_helping_help`, `wsim_helping_help_none`,
  `wsim_HelpDone_try_run`

Use this map to choose where to inspect next; check lemma statements before applying them.

### Function Lookup And Inlining

Try `cStartFunSim`, `cInlineS`, or `cInlineT` directly before proving a
function lookup by hand. `cInlineS`/`cInlineT` use `prove_inline_cond`, whose
lookup path is:

1. use an equality already available in the proof context;
2. derive a recursive `FnsemLookupResult` certificate from module
   construction;
3. fall back to `simpl_map`.

`cStartFunSim` resolves its source function directly by certificate and then
`simpl_map`; it does not have the initial context-equality branch. Its later
target-side condition uses `prove_inline_cond`.

The certificate path already follows supported constructors and wrappers such
as `Mod.add`, `SMod.to_mod`, `sandbox_fnsemmap`, and registered filters. Do not
make users declare manual “this module contains this function” instances or
unfold the inlining tactic merely to enable the fast path. Treat the
certificate as an optional optimization: unsupported symbolic module shapes
must still reach the `simpl_map` fallback or report that the lookup cannot be
resolved.

When diagnosing lookup performance, separate `rewrite_fnsem_lookup` from the
normalization and body-inlining phases so the profile identifies the actual
bottleneck.

### Proof Script Style

Do not start proof search by broadly rewriting definitions such as `rewrite /...`.
First look for an existing lemma, domain tactic, or local helper that exposes the
intended proof step. Use unfolding only when the current head form is genuinely
blocking those tactics, and then unfold the smallest definition needed to expose
that head form.

Avoid unfolding module aliases, whole module `t` definitions, or wrappers merely
because they appear in the goal. If repeated unfolding is needed, consider whether
a local helper lemma or tactic should capture that proof step.

Prefer compact, idiomatic Iris proof-mode scripts when they make the proof easier
to read and maintain. Before writing multi-line introductions, immediate
destructs, or manual spatial/pure decomposition, check whether standard Iris
proof-mode intro/destruct patterns can express the same step directly. Use
compact patterns to clarify the proof's logical structure, not to hide important
witnesses or invariant transitions.

When a case split has semantically distinct but syntactically opaque branches,
label the bullets with short comments such as `(* abort *)`, `(* commit *)`,
`(* help *)`, or `(* skip *)`. Do not add labels to constructor cases whose
meaning is already evident from the pattern.

After a proof first reaches `Qed`, do a cleanup pass before reporting completion:
remove redundant pure prepasses, replace manual rewrites with domain tactics
(`aUnfold*`, `cNorm*`, `sYields`, `cSimpl in H`, etc.), compact adjacent tactics that
form one logical step, and rerun Coqtail/build after the cleanup.

### Scheduler Yield Tactics

Use `sYields` only when the first source/target yield is immediately matchable
and saturation is intentional. Its first `sYield` is mandatory, so it fails
when no paired yield is available. After each matched yield it runs
`try cStepsT`, then repeats; those target steps may expose the next paired
yield. Use `sYield` when exactly one matched yield is intended. If the sequence
leaves a source-only yield, finish it with `sYieldS`.

Use `sYieldS` when only the source side has a scheduler yield and the target
side should stay put. It normalizes the source and applies the source-yield
lemma for these head forms:

- source `SB.sandbox msk_s (SModTr.trans sp_s 𝒴) >>= _`
- source `SB.sandbox msk_s (SModTr.trans sp_s 𝒴@{N}) >>= _`

### Atomic/Iterator Unfolding Tactics

Use `aUnfoldS`/`aUnfoldT` when the source/target side needs one unfolding of an
atomic or iterator combinator before ordinary simulation tactics can see the
next head event. They use `replace_s`/`replace_t` plus `cNormS`/`cNormT`, and
unfold these forms:

- `iterC body arg`
- `yield_iter body arg`
- `yield_namespace_iter N body arg`
- `ITree.iter body arg`
- `atomic_update_sem αP αQ`

Prefer them over manual rewrites such as `unfold_yield_iter`,
`unfold_yield_namespace_iter`, `unfold_iter_eq`, or
`unfold_atomic_update_sem` when working under an `isim`/`wsim` goal.
If these tactics are unavailable, import `Atomic.v` (for example,
`From CRIS Require Import Atomic.`) before falling back to manual rewrites.

### Normalization, Step, And Force Tactics

`cNormS`/`cNormT` normalize the source/target itree under an `isim`/`wsim`
goal. They are useful when the term is hidden under binds, sandboxing, or module
translation and needs to be reshaped into a canonical head form such as
`trigger ... >>= k`, `tau;; k`, or `Ret v`. Prefer them over manual rewrites
like `bind_bind`, `SRed.bind`, `SBRed.bind`, or `vis_trigger` when the goal is
already an `isim`/`wsim`.

`cStepS`/`cStepT` and `cForceS`/`cForceT` also run `cNormS`/`cNormT` around their
main action, so they often remove the need for explicit normalization.

Use Ltac profiling only when the user explicitly requests tactic-performance
or tactic-provenance analysis. Profile the smallest representative target,
remove temporary profiling or `Time` commands afterward, and rebuild the
target once without profiling before reporting the result.

Never use bare `cSimpl`: it repeatedly normalizes the whole pure context. For
argument decoding or upcast/downcast facts, orient the relevant equality if
needed and use `cSimpl in H` on that named hypothesis. Do not introduce or copy
an existing bare `cSimpl`; use a goal-local standard tactic when only the goal
needs ordinary simplification. When replacing a bare `cSimpl`, inspect which
unrelated hypotheses it also destructed or substituted, and make only genuinely
required effects explicit.

Use `cStepS` when the source side has one of these head forms:

- `tau;; _`
- `trigger (Take X) >>= _`
- `trigger (Assume P) >>= _`
- `trigger (AssumeRes r) >>= _`
- `assume _ >>= _`
- in `wsim` goals, source `trigger (SPut k v) >>= _`
- in `wsim` goals, source `trigger (SGet k) >>= _`

Use `cStepT` when the target side has one of these head forms:

- `tau;; _`
- `trigger (Choose X) >>= _`
- `trigger (Guarantee P) >>= _`
- `guarantee _ >>= _`
- in `wsim` goals, target `trigger (SPut k v) >>= _`
- in `wsim` goals, target `trigger (SGet k) >>= _`

Use `cForceS`/`cForcesS` when the source side has one of these head forms:

- `trigger (Choose X) >>= _`
- `trigger (Guarantee P) >>= _`
- `unwrapN _ >>= _`
- `guarantee _ >>= _`

Use `cForceT`/`cForcesT` when the target side has one of these head forms:

- `trigger (Take X) >>= _`
- `trigger (Assume P) >>= _`
- `trigger (AssumeRes r) >>= _`
- `assume _ >>= _`
- `unwrapU _ >>= _`

The optional argument forms `cForceS witness` and `cForceT witness` choose an
explicit witness; use them when inference would leave evars or pick the wrong
value. `cStepsS`/`cStepsT` and `cForcesS`/`cForcesT` repeat the corresponding
single-action tactic, so use them only when consuming all currently available
actions is intended.

## Client Proofs And Cancellation

For example-client proofs, first inspect an existing client/cancellation
pattern in the checked-out examples. Search for `Cancel.cancel`,
`SMod.to_mod_cancel`, and `SchA.fn_spawnable`, then read the relevant client
proof and `*All.v` composition file. Do not infer the client proof architecture
only from the module currently being edited.

Scheduler-using clients usually need the two-level specmap pattern:

```coq
Context (sp_user sp : specmap).
Context (Hclient : ClientA.sp N ⊆ sp_user).
Context (Hsch : SchA.sp sp_user (↑N) ⊆ sp).

Local Definition MA := ClientA.t N sp ★ ...
Local Definition MI := ClientI.t ★ ...
```

`sp_user` carries the user-function specs needed for `SchA.fn_spawnable`; `sp` carries the scheduler-expanded specs. Do not set the abstract client module's specmap to `∅` merely because a local producer/thread proof goes through. That loses the spawn/join specifications needed by the main proof.

For cancellation, follow the `*All.v` shape:

- define the source `SMod.t`;
- set `sp := SMod.sp_from smod_src`;
- prove any inclusions such as `ClientA.sp N ⊆ sp_user` and `SchA.sp sp_user (↑N) ⊆ sp`;
- apply `Cancel.cancel` to `SMod.to_mod_cancel (SMod.sp_from md) md`;
- expect `∅` only after cancellation, in `SMod.to_mod ∅ (SMod.cancel md)`.

Lesson learned: the empty specmap belongs to the post-cancellation executable side, not to the spec-using client abstraction. If a proof involves `Sch.spawn`/`Sch.join`, preserve the scheduler specmap chain until cancellation removes specs.

## Helping Machinery

Use `concris-helping-proof` for any proof that calls or erases Helping. Read
its current API map before editing a client; do not reconstruct the
architecture from legacy examples or unfold private Helping internals around a
missing public rule.

## Spec Change Checklist

Before changing a spec, answer:

- Is this module meant to be implementation, atomic, tame, or prophecy-compatible?
- Does the change preserve that role?
- Does it introduce arbitrary `Take X` into a `real_mod` path?
- Does it erase the distinction between two intentionally separate specs?

If the answer is unclear, continue proof exploration locally and report the exact blocker before committing to the spec change.

## Validation

For proof changes:

- Compile the edited file.
- Compile at least one dependent representative proof.
- If a tactic was changed, test it on an existing proof and a small focused use case when feasible.
- Never claim a proof is done unless the relevant `.vo` target builds.
