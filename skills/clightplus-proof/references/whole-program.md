# Initializer, cancellation, and adequacy

## Build a layer table

Name the exact modules before composing. Keep the same `genv`, `ce`, and
`public` parameters across layers. A common proof chain, listed by changed
layers instead of concrete module-addition order, is:

```text
InitU + ProgramU + MemU
InitU + ProgramU + MemN
InitU + ProgramN + MemN
InitN + ProgramN + MemN
spec-carrying N source
cancelled executable N source
```

Use `ctxr_trans` with `ctxr_frameL`/`ctxr_frameR` to change one layer at a
time. Module addition is commonly right-associative; inspect the actual goal
after `SMod.to_mod_add` before adding association rewrites. Preserve any memory
and external layers present in the target composition.

Route single and linked inputs separately. For multiple generated translation
units, establish the checkout's `Linkable` condition, use `compile_link_ref`,
and discharge identifier, domain-disjointness, and compiler side conditions
before entering the same U/N layer chain.

## Prove the initializer separately

Compare `InitI.Init_fun_with FailureMode.N` to the U initializer while keeping
the N program and memory suffix fixed. Typical obligations are:

- `GEnv.wf genv` and inclusion of the generated program environment;
- successful lookup of the `main` global and its definition;
- the memory-init spec lookup in the whole source specmap;
- the `main` spec lookup and exact `int main(void)` call shape;
- a returned `Vint` accepted by the entry implementation.

Keep three interfaces distinct: the C entry type such as `int main(void)`, the
CRIS call payload/result types used by the compiled body, and the metadata type
chosen by the logical `fspec`. Prove each lookup and conversion at its own
boundary.

Use lookup/inclusion lemmas and the specmap API. Do not unfold global resource
representations or replace typed-call failures with assumptions.

Audit the initializer body itself. In the current checkout,
`InitI.Init_fun_with FailureMode.N` changes its two calls, while global lookup,
global-definition downcast, main-type rejection, and `is_int` failure still use
U behavior. Prove these branches unreachable from generated-program facts, or
record them as uncovered. Do not infer full initializer N-lifting from the
constructor name.

Attach specs by function key. A key-insensitive update such as
`SMod.update_spec (fun _ => fsp_some spec)` overwrites every internal function
spec. It is valid only after proving the module has the intended single
function, or when every function receives that same spec. Otherwise use the
checkout's key-aware construction and prove the relevant lookups.

Build the whole source specmap from the composed spec-carrying module. Prove
exact entry and internal-function lookups and the memory-spec inclusion needed
by clients before translating it with `SMod.to_mod`.

Require an exact `entry = Some intended_spec` lookup before cancellation.
`fspec_flat None` falls back to the trivial spec, so satisfying only the
`fspec_flat` premise does not show that an entry spec exists. Apply the same
vacuity check to expected source function lookups before accepting `ISim.t` or
`ISim.sim_fun` results.

## Keep cancellation honest

`Cancel.cancel` requires a cancellable source module, an entry `fspec_flat`, a
postcondition relating abstract and concrete returns, and cancellation
resources. Compiler-generated U/N modules may carry `msk_real`, while specs
need masks admitting their logical events.

Before `Cancel.prepare`, inspect and discharge all three API premises: calls or
spawns whose target/source spec lookups differ must be excluded by each body
mask; the source specmap's logical-event flag must be true; and, when the target
flag is false, system calls must be excluded by each body mask. Do not replace
these mask/specmap facts with automation that succeeds only for one concrete
module.

`SMod.update_spec` changes specs only; it does not widen masks. Treat any mask
adapter as a separate semantic construction. Check its body, state, scope, and
mask relation instead of assuming it is normalization.

Do not silently widen a mask or alter a compiled body. First use an existing
body-preserving spec constructor or mask lemma. If none exists, report the
missing abstraction and obtain approval for a body-preserving adapter. Prove
that function bodies, scopes, specs, and initial state have the intended
relationship. Keep the source specmap nonempty until cancellation; use `∅`
only after `Cancel.prepare` and `Cancel.cancel`, in the cancelled executable
form `SMod.to_mod ∅ (SMod.cancel source_smod)`.

The reusable cancellation sequence is `SMod.to_mod sp source_smod`,
`Cancel.prepare`, the cancellation view, `Cancel.cancel`, then
`SMod.to_mod ∅ (SMod.cancel source_smod)`. Cancellation erases function specs;
it preserves function masks and U/N body choice. A cancelled module built from
widened N bodies is therefore not
definitionally the canonical raw `compileN`/`InitI.tN` composition. Claim that
connection only after a separate mask-equivalence or refinement proof.

## Close adequacy

For a generated closed target, establish the checked-out equivalents of:

- `GEnv.wf (get_genv prog)`;
- `type_cond genv`;
- `align_cond genv genv` or `mem_init_cond genv genv`;
- `Mod.wf` for initializer, U memory, external model, and compiled program.

Use `clight_solve_wf` or program-level alignment lemmas when they fit. Keep
small concrete environment computations in a separate facts module rather than
inside the semantic simulation. Do not copy a no-global-variable contradiction
argument to an input that contains initialized globals.

At the final boundary:

1. allocate CRIS/invariant resources;
2. when cancellation and final adequacy both need world invariants, use
   `winv_split_empty` before consuming either share;
3. call `clight_mem_alloc` with the concrete type and memory-init facts;
4. route `MemA.InitCond` to the memory refinement, the spare `uninit` share to
   the chosen entry precondition when required, and `Cancel.init_res` to
   cancellation;
5. retain the empty-world invariant for `refines_adequacy`, apply it using
   target `Mod.wf`, and export the resulting `refines_lmod` theorem.

`refines_lmod` is a ClightPlus/CRIS module-level result. An assembly behavior
theorem is a separate layer requiring compiler success and its checked program,
alignment, symbol-disjointness, and external-semantics conditions. State which
boundary the exported theorem reaches.

If the target contains `ExtI.Default`, either keep it with the correct source
model or eliminate it only after checking that no reachable generated call
uses it. An unsupported external call left at U is outside a claimed N-safety
property.
