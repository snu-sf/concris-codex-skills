# Memory client proofs

## Read the actual interface

Inspect `ClightPlus/mem/ClightPlusMemA.v` and the active U/N memory modules.
Check each `fspec` directly; resource arguments and side conditions can change.
Do not unfold sealed `pointsto`, `live`, or equivalence resources to bypass a
missing rule.

Audit the N module by body, not by name. In the current single-source layout,
the 13 registered operations live in `MemI.*_with mode`; the public `MemI.*`
names and `MemU` select `FailureMode.U`, while project `MemN` aliases the same
bodies at `FailureMode.N` and wraps every entry with `cfunN`. In particular,
`init_mem_with` selects `FailureMode.ccall mode` for its nested capture call.

Single-source packaging does not make every failure N. Shared bodies retain
classified raw U paths for framework-state downcasts, architecture or static
generated-input conditions, and internal allocation invariants. Unregistered
`loadbytes`, `storebytes`, and `realloc` remain outside this 13-operation
property. Check the current audit and body, prove reachable raw U paths
impossible for the client, and state remaining semantic gaps. Obtain approval
before changing a definition, specification, mask, or theorem statement.

For a program-layer proof, keep the memory layer identical on both sides:

```text
source = ProgramN + MemN-with-specmap
target = ProgramU + MemN-with-specmap
```

Here `ProgramN` denotes the N body with the source spec and any justified mask
construction attached; `ProgramU` is the executable U body. Do not assume the
spec-carrying source is definitionally equal to raw `compileN`.

Prove `MemU` to `MemN` separately, then frame it under the program and
initializer. This isolates the semantic change made by each theorem.

## Track the local-memory lifecycle

For stack-backed scalar or aggregate code, expect this resource flow:

1. `MemA.salloc_spec` returns a block/address, `pointsto` bytes initially
   containing `Undef`, and `live[..., Local, ...]`.
2. `MemA.store_spec` consumes writable old bytes and returns
   `encode_val chunk value`, preserving liveness.
3. `MemA.load_spec` consumes and returns the same bytes and liveness, plus a
   value related by `decode_val`.
4. `MemA.sfree_spec` consumes the final bytes and liveness.

Instantiate the exact Clight chunk, address, offset, permission fraction,
allocation metadata, and byte list. Follow each checked spec's pure obligations:

- allocation requires its size range;
- free requires byte-list length matching allocation size;
- load requires chunk length, `change_check`, supported chunk, and alignment,
  then returns a `decode_val` fact;
- store requires chunk length and alignment, then returns bytes related by
  `encode_val`.

Derive address normalization through public lemmas such as
`live_trivial_offset` and resource transport such as `equiv_point_comm` when
those names exist in the checkout.

For `Val.subl` base-address normalization, prefer public lemmas such as
`live_sub_null_r`, `live_sub_null_r_ofs`, and `points_to_sub_null_r` when
available. Keep concrete ABI reductions and byte witnesses proof-local.

Trace the generated operation before choosing a spec. Local allocation goes
through `alloc_variables_c_with`; normal return frees through
`interp_runtime_free_with`. `By_value` access normally uses load/store, while
`By_copy` may use memcpy. Do not infer the memory call from C surface syntax.

## Synchronize calls

When the checkout exports `cHoareCallS`, use it for a source
`SModTr.HoareCall` with an `fspec_simple` specification against a target bare
`Call` with the same function and argument:

```coq
cHoareCallS meta with "PRE_RESOURCES"
  as (ret st_src st_tgt) "POST" "IST".
{ (* Prove the actual fspec_simple precondition. *) }
```

This tactic resolves the specification lookup with `simpl_sp`, selects the
logical metadata and concrete call argument, executes the internal
`Choose`/`Guarantee` and `Take`/`Assume` protocol, synchronizes the raw calls,
substitutes the structural return equality, and returns the actual
postcondition as `POST`. Keep the logical metadata witness distinct from the
upcast call argument. Ensure an exact lookup or the checkout-specific equivalent
of `MemN.sp genv ⊆ whole_sp` is available.

In the current ClightPlus SV-COMP client, import
`ClightPlusSVComp.ClightPlusMemTactics` and prefer these wrappers:

```coq
cMemSalloc 4%Z
  as (m b) BLK SZ "POINTS" "LIVE" "IST".

cMemStore
  (chunk, addr, m, ofs, Local, q, value)
  old_bytes with "POINTS LIVE"
  as "POINTS" "LIVE" "IST".
{ (* Argument equality, byte length, and alignment. *) }

cMemLoad
  (chunk, addr, m, Local, q_live, ofs, q_points, bytes)
  with "LIVE POINTS"
  as (value) DECODE "POINTS" "LIVE" "IST".
{ (* Equality, length, change_check, supported chunk, and alignment. *) }

cMemLoadAuto
  (chunk, addr, m, Local, q_live, ofs, q_points, bytes)
  with "LIVE POINTS"
  as (value) DECODE "POINTS" "LIVE" "IST".

cMemSfree m bytes addr
  with "POINTS LIVE" as "IST".
{ (* Allocation metadata and byte length. *) }
```

`cMemSalloc` returns the canonical block/address resources and allocation
equalities. Store and load return the current ownership; load also returns its
`decode_val` fact. Free consumes ownership. Use only the returned ownership in
later statements.

Use `cMemLoadAuto` only when all five standard load side conditions are concrete
enough for `solve_mem_load_sideconds` to close by simplification and the final
alignment fact is divisibility by one. The wrapper preserves the same lookup,
resource flow, postcondition, and failure behavior as `cMemLoad`; it only calls
that side-condition solver. If any condition stays symbolic or the alignment is
stronger, use `cMemLoad` and prove the obligations explicitly. Do not broaden
the solver with client-specific rewrites or hypothesis names.

For a cursor that advances both the address and the tracked offset, transport
liveness through the public rules:

```coq
iPoseProof
  (live_offset_slide _ _ _ _ _ k with "LIVE") as "LIVE".
(* Later, to restore the original cursor resource: *)
iPoseProof
  (live_offset_slide_rev _ _ _ _ _ k with "LIVE") as "LIVE".
```

These lemmas relate liveness at `Val.subl vaddr (Vptrofs ofs)` to liveness at
`Val.subl (Val.addl vaddr (Vptrofs k)) (Vptrofs (Ptrofs.add ofs k))` without
unfolding `live`. Use them only after the pure pointer arithmetic has the same
`Ptrofs.add ofs k` shape. If the cursor expression differs, normalize it with a
public pointer lemma or keep a proof-local equality; do not unfold the RA.

For an unsupported specification, non-`None` call mask, or mismatched call
shape, expose `SModTr.HoareCall`, choose the specification arguments with
`cForceS`/`cForcesS`, prove its precondition, and use `cCall` only once both
sides are raw `Call` events. Destruct the postcondition immediately enough to
identify returned values and updated resources.

## Common diagnostics

- A stuck `clSteps*` goal with `_with FailureMode.N` indicates a tactic pattern
  gap, not necessarily a semantic mismatch; follow `u-n-semantics.md`.
- A store/load call that cannot instantiate its spec usually lacks a concrete
  chunk-size, alignment, pointer-offset, or encode/decode fact.
- When the source contains `HoareCall` and the target contains a bare `Call`,
  use `cHoareCallS` or a supported `cMem*` wrapper. A failed direct `cCall`
  usually means both sides have not reached raw call events.
- A load result may be described by `decode_val chunk bytes = value`; derive
  the needed equality with the public encode/decode lemmas before substitution.
- A free proof usually needs the complete current byte list and allocation
  size, not only liveness.
- LP64 simplifications such as pointer-width reductions are architecture
  assumptions. Make them explicit and keep them out of architecture-neutral
  claims.
- A final unexplained `emp` goal after applying a contextual refinement is a
  logical-unit obligation; use `iEmpIntro` instead of broad simplification.
