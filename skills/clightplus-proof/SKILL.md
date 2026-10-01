---
name: clightplus-proof
description: >-
  Use for ClightPlus/ConCRIS Rocq proof engineering involving generated Clight
  programs, FailureMode U/N interpretations, compile/compileN or Init U/N
  refinement, CProofMode symbolic execution, MemU/MemN memory-safety clients,
  spec cancellation, and whole-program adequacy.
---

# ClightPlus Proof Engineering

Use this skill together with `concris-proof`. Follow its Coqtail, build,
proof-script, and validation rules; this skill adds the ClightPlus-specific
semantic and proof structure.

## Route the task

- Read [u-n-semantics.md](references/u-n-semantics.md) for U/N module choice,
  refinement direction, failure classification, or mode-aware symbolic steps.
- Read [memory-client.md](references/memory-client.md) for a generated C
  function that allocates, loads, stores, frees, or otherwise calls `MemA`.
- Read [whole-program.md](references/whole-program.md) for `InitI`, specmaps,
  cancellation, target well-formedness, ghost allocation, or final adequacy.
- Read every applicable reference when proving an end-to-end C program.

## Fix the semantic boundary first

1. Inspect the generated Clight `.v`; do not infer the exact AST, temporary
   variables, chunks, casts, or control flow from the `.c` file alone.
2. Write down the concrete target, source, and each intermediate module. Change
   one layer at a time. Keep unchanged context modules identical on both sides.
3. Confirm the direction before proving: contextual refinement is written
   `ctx_refines target source`, while `ISim.sim_fun` receives source before
   target.
4. Enumerate the failure sites covered by the N interpretation. Do not call the
   theorem full ISO C definedness when direct `triggerUB` sites or unmodeled
   externals remain. A proof that reaches raw `triggerUB` on the source does not
   count as the intended safety result.

Do not change a definition, specification, mask, theorem statement, or sibling
dependency to make a proof close unless the user explicitly authorizes that
change. Proof-local helpers remain subject to repository policy.

## Prove generated functions

1. Prove the intended function exists in source and target maps. Check expected
   domains; an absent source lookup can make `ISim.sim_fun` vacuous.
2. Reuse `CProofMode` and ordinary ConCRIS tactics before unfolding interpreter
   definitions.
3. Start module simulations with `cStartModSim`. Choose one function-start
   command: use `cStartFunSim` for the generic simulation setup, or
   `clightStartFunSim` when its Clight environment and mode-aware entry
   unfolding are required. Neither command advances a Clight statement.
   Inspect both displayed heads before issuing the first runtime step.
4. Use `clStepS`/`clStepT` for one intentional Clight runtime statement, and
   use `clStepsS`/`clStepsT` only when saturation is required by the visible
   control flow. These saturation tactics can succeed after zero steps, so a
   repeated `cStepsS. cStepsT.` pair is not a progress check. Use
   `clDerefS/T`, `clCastS/T`, `clCmpS/T`, `clBinarithS/T`, or `clSubS/T` when
   exactly that expression combinator blocks one side; then return to ordinary
   `cStep*` tactics. Use `cForce*` and `cCall` for exposed CRIS events.
5. For source `HoareCall` versus target bare `Call`, prefer `cHoareCallS` when
   the checkout provides it. For supported `MemA` calls, prefer the matching
   `cMem*` wrapper. Prove the remaining operation-specific pure obligations and
   retain the returned resources for the next C statement. Use `cCall` directly
   only after both sides expose raw call events.
6. Finish the function relation, lift it to `ISim.t`, then use
   `main_adequacy` for the local contextual refinement.

If a Clight stepping tactic fails, inspect the goal head and the tactic's match
pattern before adding rewrites. In particular, check whether the goal contains
`handle_runtime_env_with` while the installed tactic only recognizes the U-mode
alias `handle_runtime_env`. Prefer an updated public tactic. If none exists,
report the missing abstraction and use a minimal proof-local mode-aware adapter
only when authorized; do not silently patch global proofmode code.

## Compose the whole program

Prove memory, program, and initializer refinements independently, then frame and
compose them. Keep source specifications present until the clients that consume
them are proved. Cancel specifications only after proving cancellability and the
entry pre/post obligations. Allocate Clight memory ghost state only at the final
adequacy boundary.

Treat an unused external module explicitly: eliminate it by a refinement rule
only after confirming the generated program cannot call it, or include a source
model with the intended U/N policy.

## Validate the claimed property

- Regenerate Clight through the repository command; never hand-edit generated
  output. Record the CompCert target architecture and relevant tool version.
- Run Coqtail to EOF after the final edit, then build the exact `.vo` through
  the workspace shim with bounded parallelism.
- Build a dependent whole-program theorem when changing a client or tactic.
- Check exact `Some` lookups for every claimed function and entry spec; do not
  accept a theorem closed through an absent-source or trivial-spec branch.
- Reject `Admitted`, `Abort`, new axioms, and bare `cSimpl`.
- Run `Print Assumptions` on the exported theorem and distinguish framework
  baseline axioms from new dependencies.
- State the proved failure classes and known semantic gaps in the handoff.
