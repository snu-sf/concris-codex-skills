---
name: concris-helping-proof
description: "Use for ConCRIS/Rocq proof engineering involving the resource-only Helping modules: Helping.run, reqid-only HelpingOn.try_run, Helping.help, HelpPend/HelpDone resources, cancellable hinv ownership, IstHelp and nested client invariants, HelpingOn/HelpingOff erasure, helping_main composition, and example clients whose owners or helpers execute pending jobs."
---

# ConCRIS Resource-Only Helping Proofs

Use this skill together with `concris-proof`; apply its Coqtail, recovery, and
resource workflow. Treat Helping as intermediate proof machinery that lets an
owner or another thread execute a registered job. Do not turn it into a
client-visible abstract specification.

## Find the Current API First

Inspect these files before changing a proof:

- `library/helping/HelpingOn.v`: executable `run`, reqid-only `try_run`, and `help`
- `library/helping/HelpingResource.v`: public `HelpPend` and `HelpDone`
- `library/helping/HelpingTactics.v`: client reasoning rules, `IstHelp`, and `hinv`
- `library/helping/HelpingFacts.v`: `help_alloc`, `helping_main`, and
  `helping_main_filtered`
- `library/helping/HelpingOnOffResource.v` and `HelpingOnOffproof.v`: private
  erasure protocol and soundness proof

Confirm the checked-out version instead of trusting an old proof:

```sh
rg -n "Definition (IstHelp|IstHelp_gen)|Definition try_run|Lemma wsim_helping" \
  library/helping
```

The current resource-only API uses `IstHelp`; `IstHelp_gen` is legacy. Never
recreate `IstHelp_gen`, expose `HelpingOn.v_reqs`, or give client proofs
`HelpAuth` merely to port an old script. If the checkout only contains the
legacy API, report that version mismatch before applying current snippets.

## Current Operational Model

Keep the following flow in mind:

1. `Helping.run (N, arg)` takes a fresh `reqid`, assumes
   `HelpPend reqid N arg`, yields at `N`, and calls `try_run reqid`.
2. `HelpingOn.try_run reqid` chooses either:
   - a persistent completed result, justified by
     `Guarantee (HelpDone reqid ret)`; or
   - pending work, where it chooses `N` and `arg`, justifies them with
     `Guarantee (HelpPend reqid N arg)`, runs the job, and assumes
     `HelpDone reqid ret`.
3. `Helping.help` chooses a request and job data, proves authority with the
   same `HelpPend`, runs the job, and records `HelpDone`. A `Some N` job also
   performs the scheduler namespace `Guarantee`/`Assume` handoff; a `None` job
   omits that handoff.

The reqid-only `try_run` shape is essential. The resource selects the job data
that the old private request map used to supply. Do not change it back to
`try_run reqid N arg`: clients may store `∃ N, HelpPend reqid N arg`, and a
later owner would then have no sound proof that the stored `N` equals a
syntactic argument.

## Public Resources

Use only these client-visible roles:

- `HelpPend reqid N arg`: exclusive authority to claim and execute that
  pending job.
- `HelpDone reqid ret`: persistent evidence that the request completed.
- `hinv_ownE E`: linear ownership of cancellable-invariant namespaces.
- `IstHelp Ist E st_s st_t := hinv_ownE E ∗ Ist st_s st_t`: add namespace
  ownership to an indexed client state relation.

Keep `HelpAuth` and `help_erasure_init_cond` private to HelpingOn/HelpingOff
erasure. Pass `help_init_cond` opaquely to `helping_main` or
`helping_main_filtered`; do not destruct it in client modules.

## Owner Request Rule

For a source call to `Helping.run`, apply `wsim_helping_run`. Do not pass an
`IST` resource premise:

```coq
cStepsS.
iApply wsim_helping_run; [simpl_map; simpl; f_equal|].
iIntros (reqid) "Pend".
```

The first premise is the source module's concrete `Helping.run` lookup. The
shown `simpl_map` proof is the common concrete-product case; adapt that premise
to the actual module shape rather than invoking a nonexistent generic lookup
tactic.

The continuation receives exactly:

```coq
Pend : HelpPend reqid N arg
```

Store this token in the client invariant, run the job immediately, or later
replace it with `HelpDone`. Do not add a client request map.

## Owner Executes Pending Work

Apply `wsim_helping_pend_try_run` to a pending token:

```coq
prependRetT tt.
iApply (wsim_helping_pend_try_run with "Pend [-]").
```

Prove the job simulation. The rule chooses the token's `N` and `arg` inside
`try_run`, so an existentially stored namespace is sufficient. After the job:

```coq
iIntros "Done".
```

Receive only `Done : HelpDone reqid ret`. The ambient `Ist` remains the WSim
index; the rule does not consume and return a separate `IST` resource.

If the operation already has persistent completion evidence, apply:

```coq
iApply (wsim_HelpDone_try_run with "Done").
```

`wsim_HelpDone_try_run` needs neither `N` nor `arg`, because the completed
branch of reqid-only `try_run` does not inspect them.

## Another Thread Helps

For `Helping.help mn (Some N)`, apply `wsim_helping_help` with the selected
pending token. Build the namespace-transition/job fupd required by the rule:

```coq
iApply (wsim_helping_help with "Pend").
iExists n. iModIntro.
(* open client invariants, run jobCode, close them *)
```

Distinguish:

- `N`: the helper's current namespace;
- `N2`: the pending job's namespace stored in `HelpPend`;
- `E`: the target-side WSim/fupd mask at this rule boundary.

Preserve the scheduler `winv` handoff between `N` and `N2`. Do not confuse
these masks with the separate `hinv_ownE` resource, assume the helper and job
namespaces are equal, or unfold `HelpingOn.help` to bypass a missing public
rule.

For `Helping.help mn None`, apply `wsim_helping_help_none` to
`HelpPend reqid None arg`. This rule has no scheduler namespace handoff, but
the job loop's scheduler yield remains part of the simulation. Do not coerce
the request to `Some`, force it through `wsim_helping_help`, or unfold
`HelpingOn.help`.

## Indexed Client State and Nested Modules

Use:

```coq
Definition IstFull : ist_type Σ :=
  IstProd (IstSB scopes (IstHelp Ist E)) IstR.
```

This nested placement lets ordinary module-composition lemmas continue to see
their expected `IstProd`/`IstSB` structure. A cancellable `hinv` accessor needs
outer `IstHelp`, so rewrite only around each invariant access:

```coq
iEval (rewrite /IstFull IstHelp_nested_equiv) in "IST".
iInv "Inv" with "[IST]" as "[IST HInv]" "Close"; first by iFrame.
...
iMod ("Close" with "[...] IST") as "... IST".
iEval (rewrite -IstHelp_nested_equiv) in "IST".
```

Reverse the equivalence on every non-contradictory close path before recursion,
coinduction, or return. The equivalence preserves the exact current
`st_src/st_tgt` indices; never existentially forget or reconstruct them from a
different state.

If a local recursive lemma only transports the relation, parameterize it by:

```coq
(Irun : ist_type Σ)
```

Use `Irun st_src st_tgt` unchanged in its pre/postcondition. Do not fix such a
helper to plain `IstHelp Ist E` when the actual invariant carries a nested
payload.

## Cancellable Invariants

Allocate helping-specific invariants with `hinv_alloc`. Open them with `iInv`
through the `IntoAcc` instance or directly with `hinv_acc`.

Keep these facts separate:

- `HelpPend` authorizes job execution.
- `hinv_ownE` authorizes opening the client's cancellable invariants.
- ordinary client resources stay inside `Ist`; they do not belong in the
  helping request protocol.

Opening a `hinv` changes `IstHelp Ist F` to `IstHelp Ist (F ∖ ↑N)`. Closing it
must restore both the invariant payload and the removed namespace ownership.

## Erasure and Module Composition

First prove the client against:

```coq
client-intermediate ★ HelpingOn.t mn jobCode
```

Then prove the intermediate module against the non-helping abstraction using
`HelpingOff.t`. Finally compose them with:

- `helping_main` for the ordinary unfiltered context; or
- `helping_main_filtered` when another transformation, such as prophecy,
  already reserves a nonempty function-name filter.

The first client obligation receives `hinv_ownE ⊤`; the second erasure
obligation does not. Keep unrelated linear resources in the obligation that
uses them rather than passing them through private helping authority.

Do not unfold `help_init_cond` or call the internal erasure lemma from a client
proof. If the public `helping_main*` shape cannot express the composition,
report the missing abstraction.

## Soundness and Scope Guardrails

- Require every thread that runs a job to discharge
  `Guarantee (HelpPend reqid N arg)`.
- Never treat mere possession of arbitrary client resources as job authority.
- Never manufacture equality between an existential job namespace and a
  syntactic namespace argument.
- Never expose or duplicate private `HelpAuth`.
- Do not add operational helping state to simplify a proof.
- Preserve `HelpDone` persistence and `HelpPend` exclusivity.
- Scope each independent Helping protocol with its own `helpingGS/help_name`.
  `HelpPend` is already implicitly namespaced by that ghost name, so do not add
  `mn` to its explicit key merely to support multiple Helping instances.
  Deliberately share a `helpingGS` only when the modules are meant to share one
  request protocol and compatible job semantics.

## Proof Debugging Workflow

1. Search the actual public lemma statement and the closest migrated client.
2. Open the smallest edited file through the base skill's Coqtail workflow.
3. Step through owner-pending, owner-done, and helper branches separately.
4. After editing an imported Helping file, rebuild that dependency and restart
   Coqtail; never trust a stale session.
5. If `iInv` cannot see `IstHelp`, inspect the nested relation and use
   `IstHelp_nested_equiv`.
6. If a pending owner cannot apply the rule, inspect whether the source still
   uses the obsolete `try_run reqid N arg` shape.
7. If a local helper loses state indices, generalize its transported
   `ist_type`; do not weaken the public theorem or unfold internals.
8. When porting the on/off proof to reqid-only `try_run`, make formerly
   syntactic `N`/`arg` parameters explicit at relation constructors if Coqtail
   reports shelved evars; do not change the relation merely to restore
   inference.
9. Use an exact `.vo` build only after Coqtail reaches `Qed`/EOF.

## Validation Matrix

After changing Helping itself, verify:

1. `HelpingOn.v` and `HelpingTactics.v`;
2. `HelpingOnOffproof.v`, covering pending, in-progress, and done cases;
3. one owner-run client and one helper-run client;
4. one nested-IST client;
5. `HelpingFacts.v` if `helping_main*` or init-resource flow changed.

After changing only a client, build the edited operation proof and its
top-level composition module. Never report completion from a source-level
`Qed` alone; require the relevant `.vo`.
