# Closing `glueD'_spec` — multi-session plan & handoff

**Branch:** `concat-continue`  ·  **File:** `src/FingerConcat.v`  ·  **Status:** Phase 1 done (axiom-free, builds clean).

## Progress log

- **Session A (done):** `fconsA_elemD_step` **cases 1–4 proven** (case 5, the
  recursive `More (Three ...)`, has a precise roadmap — see its comment in the
  source / `wip/step_lemma.v`). The fold helper `foldr_fcons_clairvoyant_spec`
  is **proven** (modulo step case 5). The **`glueD'_spec` `Nil` arm is closed**
  via that helper. Whole project builds; `glueD'_approx` etc. stay "Closed
  under the global context"; the only axiom introduced so far is
  `fconsA_elemD_step` (its case 5). Generalisation found necessary: the step
  lemma's consed element is upper-unconstrained (`fcons_elemD s outD ≤ e`, no
  `e ≤ exact x`) so the recursive case can feed the spine-derived `PairA`.
- **Session B (done):** `Unit/_` arms closed (reuse the `foldr` helper). Built
  the snoc duals — `fsnocA_elemD_step` (cases 1–4; case 5 admitted, mirror of
  cons) and `foldl_fsnoc_clairvoyant_spec` (generalised on the seed computation,
  since `fold_left` threads the accumulator) — plus `fsnocD'_val_thunk` /
  `foldl_fsnocD'_val_thunk` (for the `Undefined`-spine branches; `fsnocD'` isn't
  unconditionally `Thunk`) and `firstn_nth_last` (reassembly for `More/Unit`).
  **All fold arms of `glueD'_spec` are now closed**: `Nil`, `Unit/Nil`,
  `Unit/Unit`, `Unit/More`, `More/Nil`, `More/Unit`. Snoc arms each rule out the
  wrong `q1` shapes via `foldl_fsnocD'_approx`, consume the `glueA'` tick
  explicitly, and apply the `foldl` helper with seed `ret q1`.
- **Session C (done):** closed the recursive **case 5** of **both**
  `fconsA_elemD_step` and `fsnocA_elemD_step`. The recursive `More (Three…)`
  case applies the `IH` at the `Tuple` level with the spine-derived `PairA`
  element (over-approximated), so IH side-condition 2 needs transitivity — hence
  `!Transitive LDB` was added to the step lemmas + fold helpers (the global
  `Transitive_LessDefined_{DigitA,TupleA,SeqA}` instances discharge it; provide
  the `T (TupleA B)` instance explicitly to `@transitivity` to avoid a shelved
  goal). `mD = Undefined` sub-cases use `optimistic_skip`. Added
  `fconsD'_val_thunk` / `fsnocD'_val_thunk` (force the recursive spine).
  **Both step lemmas + both fold helpers are now axiom-free**, so every fold arm
  of `glueD'_spec` is axiom-free.
- **Remaining (1 admit): the deep `More/More` arm** (arm 6) of `glueD'_spec` —
  the lockstep (`IHm` + `glueA'_mon` + the `unbundle` round-trip; likely needs
  the spec-side dual of `unbundle_flat_approx`). This is the last admit in the
  whole file.

This document is the orchestration plan for finishing the concatenation
demand-correctness proof across several sessions. It is paired with the
`wip/` scratch directory (inspection harness + in-progress lemmas) and the
per-arm `admit` annotations in `src/FingerConcat.v`.

---

## 1. Where we are

`glueD'_spec` ("clairvoyant dominates demand") is the last open obligation for
concatenation. Everything else is `Qed` and **closed under the global
context** (verify any time with `Print Assumptions glueD'_approx` etc.):

- cost: `glueD'_cost`, `concatD_cost`, `concatD_cost_O_log_n`
- approximation: `glueD'_approx`, `concatD_approx`
- element-demand machinery: `fcons_elemD`/`fsnoc_elemD`, `foldr_fcons_elems`/
  `foldl_fsnoc_elems`, and their `_approx` lemmas

### Why it was admitted (the diagnosis — do not re-litigate)

The *original* `glueD'` was **cost-only**: its fold arms set
`asD = map (fun _ => Undefined) as_`, discarding the per-element demands
(`fconsD'`/`fsnocD'` compute but throw away the element demand). That makes
`glueD'_spec` **false as stated** — e.g. `glue Nil [a] Nil = Unit a` with
`outD = UnitA (Thunk a)` demands the element, but an all-`Undefined` `asD` can
only reconstruct `UnitA Undefined`. (Counterexample is machine-checkable; see
the note replacing the old `foldr_fconsA_undef_spec` in the source.)

Phase 1 fixed this: `glueD'` now records the **real** element demands in every
arm (deep arm via `unbundle`; fold arms via `foldr_fcons_elems` /
`foldl_fsnoc_elems`). The spec is now *true* and the work is to prove it.

> Note the irony vs. thesis §6.2: the deep `More/More` arm was already correct
> (its `asD` comes from `unbundle`); the **fold arms** were the broken ones.

---

## 2. The remaining work (dependency DAG)

```
fconsA_elemD_step (cases 2–5)  ──┐
                                 ├─► foldr_fcons_clairvoyant_spec ──► Nil arm, Unit/_ arm
fsnocA_elemD_step (5 cases) ─────┼─► foldl_fsnoc_clairvoyant_spec ──► Unit/Nil, More/Nil, More/Unit
                                 │
deep More/More arm  ── independent (uses the spec's own IHm + glueA'_mon + unbundle roundtrip)
```

- **`fconsA_elemD_step`** (kernel): the *extracted* element demand
  `fcons_elemD s outD` plus any spine `q ≥` the demand reconstructs `outD`
  within `Tick.cost (fconsD' x s outD)`. Mirrors the proven `fconsD'_spec`
  (`FingerCons.v`). **Case 1 proven** (`wip/step_lemma.v`); cases 2–5 follow
  the same `fcons_ind` template.
- **`fsnocA_elemD_step`** (snoc dual): near-mechanical copy of the cons side;
  adapt, don't re-derive.
- **`foldr_fcons_clairvoyant_spec`** / **`foldl_fsnoc_clairvoyant_spec`**: the
  fold-correctness helpers. Induction on `as_`, chaining the step lemma through
  `optimistic_bind` with additive cost. These *replace* the deleted (false)
  `foldr_fconsA_undef_spec`.
- **deep arm**: the lockstep against the clairvoyant — `IHm` + `glueA'_mon` +
  the `unbundle` round-trip. Highest uncertainty; likely needs a spec-side
  `unbundle` left-inverse (dual of `unbundle_flat_approx`).

---

## 3. Session plan

> Order easy/validating work first, **but spike the risky deep arm early** so a
> late surprise doesn't invalidate the cheaper work.

| Session | Goal | Closes |
|---|---|---|
| **A** | Finish `fconsA_elemD_step` (cases 2–5) + `foldr_fcons_clairvoyant_spec` + wire the **Nil arm**. Then *timebox a spike* on the deep arm: reduce `More/More` to its core obligation with `Show`, write down what infra it needs. **Don't prove it.** | Nil arm (1 admit) |
| **B** | `Unit/_` arm (foldr helper + head/tail split). | 1 arm |
| **C** | `fsnocA_elemD_step` + `foldl_fsnoc_clairvoyant_spec` (copy-adapt the cons side), then wire `Unit/Nil`, `More/Nil`, `More/Unit`. | 3 arms |
| **D+** | The deep `More/More` arm. Budget more than one session. | last arm → `Qed`, then delete `FingerConcatAlt.v` |

Rationale: Session A proves the whole reverse-execution chain (step → helper →
arm) end-to-end against the compiler, *and* de-risks the one piece with real
unknowns before sinking sessions into the mechanical parts.

---

## 4. Per-session mechanics (what works here)

1. **One lemma per scratch file in `wip/`, iterate against the prebuilt
   `.vo`:** `coqc -Q src Clairvoyance wip/foo.v` recompiles in seconds because
   it loads `FingerConcat.vo`, not the whole project. Prove there, paste into
   `src/FingerConcat.v`, then `make` once so the `.vo` refreshes and the *next*
   scratch can import the new lemma.
2. **Inspect goals, don't guess:** `match goal with |- ?g => idtac g end`
   followed by `Abort` (see `wip/inspect.v`). This is how the Nil-case goal and
   the false-helper counterexample were found — the highest-leverage habit.
3. **End every session compiling** — `admit` the unfinished, `Admitted` the
   lemma. The always-green invariant makes resume a 2-minute job.
4. **Commit at each green milestone** on `concat-continue` (one commit per
   closed arm). Cheap restore points; reviewable diffs.
5. **Re-verify axiom-freedom after each integration:** `Print Assumptions
   glueD'_approx` (etc.) must stay "Closed under the global context."

### Build / verify commands

```sh
# fast scratch iteration (needs src/*.vo already built)
~/.opam/thesis/bin/coqc -Q src Clairvoyance wip/step_lemma.v

# refresh the .vo after integrating a lemma into src/FingerConcat.v
make                      # or: coqc -Q src Clairvoyance src/FingerConcat.v

# full clean rebuild (sanity)
make clean && make

# axiom-free check
echo 'From Clairvoyance Require Import FingerConcat. Print Assumptions glueD'"'"'_approx.' \
  | ~/.opam/thesis/bin/coqtop -Q src Clairvoyance
```

---

## 5. Reusable tactic patterns (found this session)

> See also `docs/ENGINEERING_NOTES.md` — the project-wide proof-engineering
> catalogue (implicit/`@`-counting §1, `cbv zeta` §2, `simpl`/`cbn`/`change`
> §3, `Seq_ind_poly` setup §4/§8, `lia`/`nia` §5/§14, `invert_clear` §6,
> `Tick.bind` cost/val distribution §7, **`Exact` instance resolution at
> non-leaf types §11** — key for the recursive step case 5 and the deep arm,
> **IH-inside-`TR1` §10** — key for the `More/More` lockstep). Read it before
> the next proof session.

- **`invert_ld_struct`** (defined in `FingerConcat.v`): repeatedly inverts
  `less_defined` on `SeqA`/`DigitA`/`Thunk` constructors. Relax the last rule to
  `Thunk _ \`less_defined\` _` (not `Thunk _ ≤ Thunk _`) so `invert_clear` uses
  *conversion* to see through an unreduced `exact (...)` on the RHS.
- **`mgo_`** (from `FingerCore.v`) closes the optimistic `[[ ... ]]` specs and
  their reflexivity/`≤`/cost subgoals. Often it closes the whole arm — don't
  add trailing tactics after it (`No such goal` means you over-shot).
- **Optimistic combinators:** `optimistic_thunk_go` (force a `let~`),
  `optimistic_skip` (leave it `Undefined`), `optimistic_bind`/`optimistic_mon`.
  See `fconsD'_spec` in `FingerCons.v` for the canonical usage.
- **`exact` reduction:** `exact` of a digit/seq won't reduce under `cbn [exact
  Exact_Seq]` alone — needs `Exact_Digit`/`Exact_T` too, and even then the
  instance may differ from a hand-written `map exact as_`. Prefer transporting
  facts *from* an existing hypothesis over writing `exact (...)` terms by hand.
- **`firstn_all2`/rewrite targeting:** when two `firstn (length as_) _` terms
  are present, `rewrite firstn_all2` grabs the wrong one. `set` the unwanted one
  to a local name first, then rewrite.
- **`Set Implicit Arguments` is active in `FingerConcat.v`** — fixpoints take
  `(A B : Type)` but call sites use `@f A B _ ...`. Scratch files must also
  `Set Implicit Arguments.` to match.

---

## 6. Cross-session handoff protocol

Three artifacts carry state across context resets:

1. **This doc** (`docs/CONCAT_SPEC_PLAN.md`) — the plan, decisions, commands.
2. **`wip/`** — inspection harness + in-progress lemmas + tactic notes. Not in
   `_CoqProject`, so it never breaks `make`; compile manually.
3. **Per-arm `admit` annotations** in `src/FingerConcat.v` — each `admit` in
   `glueD'_spec` is tagged with its goal shape and one-line strategy.

Plus the Claude project memory (`fingerconcat-alt-proven-core-merged`), which
is loaded automatically each session.

**Definition of done, per session** (state it up front; verify at the end):
e.g. Session A = *"file compiles; Nil arm closed (1 fewer admit); deep-arm
obligation written down in `wip/`; `Print Assumptions glueD'_approx` still
clean."*

**Final done:** `glueD'_spec` is `Qed`, `Print Assumptions glueD'_spec` is
clean, then **delete `FingerConcatAlt.v`** and drop it from `_CoqProject`
(it is already a dormant backup), and update the writeup status prose (batched
separately by the author — the writeup is reference-only here).
