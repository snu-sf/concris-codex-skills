---
name: concris-tame-proof
description: Use for ConCRIS/Rocq proof engineering against tame specifications, especially modules using tame_triple, tame_update, Choose/Guarantee/AssumeRes, prophecy-compatible specs, MemT/LockT/VRegT-style layers, and proofs where direct Atomic.v-style angelic Take specs would break real_mod or prophecy compatibility.
---

# ConCRIS Tame Proofs

Use this skill together with `concris-proof`; apply its Coqtail, recovery, and
resource workflow. This skill adds only the narrow workflow for proving
against tame specs without losing the intended prophecy-compatible
architecture.

## Mental Model

Treat a tame spec as executable syntax for an Iris-style update:

```coq
res <- trigger (Choose Σ);;
trigger (Guarantee (P ==∗ Own res ∗ Q));;;
trigger (AssumeRes res);;;
...
```

The proof has two jobs:

- pick the right ghost witness for `Choose`;
- show the `Guarantee` exactly matches the resource transition you would have used in the logical atomic proof.

Do not replace a tame spec with an `Atomic.v` spec just to make a proof easier. Tame specs exist because real/proph-compatible modules cannot depend on arbitrary angelic `Take X`.

## Standard Proof Shape

Start by exposing the tame wrapper, then discharge any pure argument shape before touching resources.

```coq
cStartFunSim.
rewrite /Concrete.fn /Tame.fn.
iApply (tame_triple_src_pure expected_arg_shape); iSplitR.
{ ... prove P arg ==∗ ⌜expected_arg_shape⌝ ... }
iIntros "%Harg".
iApply tame_triple_src.
```

After `tame_triple_src`, choose:

- `R1`: the precise resource extracted from the user's precondition.
- `R2`: the residual resource needed to continue the body and prove the final postcondition.

Prefer making `R1` a precise fragment such as `stack_content s l`, `vreg_content γ d ver`, or the locked payload. Put persistent facts and bookkeeping in `R2` unless precision requires otherwise.

## Tame Update Shape

Read `tame_update P Q arg` as a retryable atomic update. Each attempt opens with
some logical witness `x` satisfying `P x arg`, and then either:

- aborts, restores `P x arg`, and retries; or
- commits with a return value `ret` and establishes `Q x ret`.

The shared index `x` threads the identity of the logical witness from the
precondition to either outcome. It does **not** say that the represented state
is unchanged: an abort preserves `P`, whereas a commit may transition from
`P x arg` to a different assertion `Q x ret`.

Preserve that identity by binding the witness in the `X` index of `P` and `Q`.

Good:

```coq
tame_update
  (λ '(γ, d, ver) arg, ...)
  (λ '(γ, d, ver) ret, ...)
```

Avoid existential postconditions that forget which pre-state produced the result. If the return value depends on the pre-state, put that return fact in the update postcondition, not only in the outer non-atomic post.

When symbolically stepping a tame update:

- abort/retry branch must preserve `P x arg`;
- success branch must produce `Q x ret`;
- if the abstract spec permits repeated aborts, model that with the retry loop instead of assuming one-shot success.

### Head-form dispatch

Normalize the simulation goal, inspect both computation heads, and use the
matching domain rule before unfolding either wrapper:

- source and target `tame_triple`: apply `tame_triple_both`; prove the pre
  consequence `Ps ==∗ Pt`, simulate the raw bodies, and return the post
  consequence `Qt ==∗ Qs` together with the original simulation relation;
- source `tame_triple`: apply `tame_triple_src_pure` when an argument-shape fact
  must be extracted; otherwise apply `tame_triple_src`;
- target `tame_triple`: run `tForceT x0 as "HR"`; prove its precondition and
  use `HR` for the outer postcondition;
- source `tame_update` commit: apply `tame_update_src_commit`; its continuation
  retains the closing source yield, so consume it with `sYieldS` only when the
  target should stay put;
- source `tame_update` abort/retry: apply a dedicated domain lemma; if none
  exists, report a missing abstraction instead of unfolding the protocol;
- target `tame_update`: run `tForceT`.

When source and target heads are the same `tame_update P Q arg`, apply
`tame_update_both`. It synchronizes the retry choice, resource witness, return
value, and closing yields. If the two updates have different preconditions or
postconditions and no relational domain lemma states how they correspond,
report the missing abstraction instead of unfolding them or prematurely
generalizing `tame_update_both`.

When the target head is a scheduler yield while the source head is
`tame_update`, use a domain rule that prepends or duplicates the update's
leading source yield while preserving the same update head. If no
yield-duplication rule exists, report that missing abstraction.

Do not unfold `tame_update` or `tame_triple` at a call site covered by this
dispatch. In particular, do not prove precision and destruct it manually to
simulate a source commit.

Use `tForceT` as the target-side dispatcher. The argument-free form opens a
bare `tame_update`. The `tForceT x0 as "HR"` form opens a `tame_triple`, names
its residual resource `HR`, and also opens the body when it is a `tame_update`.

For an accessor whose source state is a pair and whose source postcondition
follows from `emp`, use `tAaccIntro` to retain `Ist` across aborts and return it
only to the commit continuation:

```coq
tForceT x0 as "HR".
{ ... prove the outer tame-triple precondition ... }
tAaccIntro.
iExists x. iSplitL "Hpre".
{ ... prove P x arg ... }
iSplit.
{ iIntros "HP". ... restore P x arg ... }
iIntros (ret) "HQ !>".
iExists ret. iSplit; first done.
iModIntro. iIntros ([??]) "IST".
... use HR and prove the target continuation ...
```

When the update needs resources stored through `Ist`, define an
`IstInvAccess` instance for a persistent access assertion `Pinv`. Its contract
is `Pinv -∗ Ist st -∗ ∃ a, Pout a ∗ (Pclose a -∗ Ist st)`. Then call `iInv`
directly on the accessor goal:

```coq
tForceT x0 as "HR".
{ ... prove the outer tame-triple precondition ... }
iInv "Hinv" as ([[??] aux]) "Hopen" "HcloseIST".
```

Use `HcloseIST` on both accessor branches to close the invariant and reconstruct
the hidden `Ist`. Choose the update witness only after the accessor exposes the
resources that determine it. The abort branch restores `P x arg`; the commit
branch consumes `Q x ret` and advances past the update.

Treat a hypothesis named `GRT` according to the `Guarantee` currently exposed
in the proof state. Inside `tame_update_tgt`, it is the update's inner
`Guarantee`; after the accessor's commit continuation closes and advances past
the `tame_update`, a surrounding `tame_triple` may expose its post-`Guarantee`
under the same name. Pause at the use site and read `GRT`'s quantified binders
and premise in the Coqtail proof state. Instantiate the index that makes that
premise consume the resource you have. It need not be the accessor witness `x`
or the returned `ret`; never infer it from the hypothesis name or from an
informal "inner/outer" convention.

## Witness Discipline

Before forcing a `Choose`, identify the exact witness:

- `Choose Σ`: usually a resource token produced by a precise update.
- `Choose (iProp Σ)`: usually the residual `R2`.
- `Choose bool`: retry/success branch; do not choose success unless the source spec permits it.
- `Choose Any.t`: concrete return value determined by the same witness used in `Q`.

For source-side tame proofs, `cForceS` picks the abstract witness. For target-side tame proofs, `cForceT` must match what the implementation can justify.

## Resource Extraction Pattern

Use the user's precondition to extract a precise resource, then reopen invariants around the concrete implementation.

Typical sequence:

```coq
iApply tame_triple_src.
iExists R_precise, R_rest.
iSplitL "Hpre".
{ iIntros "Hpre"; iMod (...) as "[Hprecise Hrest]"; iFrame. }
iSplit.
{ iApply precise_own_or_local_precise_lemma. }
iIntros "Hprecise".
```

If the proof uses module-local invariants or local winv-like ownership, keep the persistent handle in the invariant/state and extract only the precise client-owned content.

For data-structure modules, prefer the StackT-style architecture:

- keep an authoritative allocation/domain resource in the module `Ist`;
- give clients a precise fragment for the current contents, plus at most a persistent managed-object fact;
- at the start of `tame_triple`, extract the precise fragment from the user's precondition;
- combine the user's fragment with the auth/domain resource to establish the object is managed, usually an `elem_of` fact;
- use that membership to find the invariant handle stored in `Ist`;
- open the module-local invariant through the `local_winv` also stored in `Ist`.

This is a general tame-proof pattern, not only a port from `Atomic.v`. The public tame spec should expose the precise ownership needed for the logical update, while private invariants and their namespace ownership remain in the module state.

## Common Pitfalls

- Do not let `Q` existentially choose a fresh state unrelated to `P`; bind the pre-state through the `X` parameter.
- Do not move return facts out of `Q` when the return value is determined by the pre-state.
- Do not use `tame_update` where the target-side job code is a plain `Choose/Guarantee/AssumeRes` sequence without the abort boolean.
- Do not silently add arbitrary `Take X` to a path that must satisfy `real_mod`.
- Do not expose module-private invariant handles or `local_winv` ownership as client-facing tame specs.
- Do not conclude a spec must change until the exact blocker is identified in the proof state.

## Validation

After edits:

- build the changed `.vo`;
- build at least one dependent module-refinement proof;
- if a tactic was changed, test both MemA and MemT-linked uses;
- never call a proof done unless the relevant `.vo` target builds.
