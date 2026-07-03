---
name: concris-tame-proof
description: Use for ConCRIS/Rocq proof engineering against tame specifications, especially modules using tame_triple, tame_update, Choose/Guarantee/AssumeRes, prophecy-compatible specs, MemT/LockT/VRegT-style layers, and proofs where direct Atomic.v-style angelic Take specs would break real_mod or prophecy compatibility.
---

# ConCRIS Tame Proofs

Use this skill together with `concris-proof`. This skill is the narrow workflow for proving against tame specs without losing the intended prophecy-compatible architecture.

## Tool Discipline

- Use `mcp__coqtail__` first for tame-proof work: step to the failing line, inspect goals, query local lemmas, patch, then reload the session.
- Avoid plain `make` loops during proof search. Reserve batch builds for final `.vo` confirmation or dependency checks after the coqtail-local proof is stable.
- If coqtail is unavailable or insufficient for a check, say so explicitly before using another Rocq/build path.

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

For `tame_update P Q`, preserve the identity of logical witnesses by binding them in the `X` index of `P` and `Q`.

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
