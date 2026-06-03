# SPLIT_NOTE.md — split & random-access sub-project

> **Pointed to from `CLAUDE.md`.** Add one line there, e.g.
> `> When working on FingerSplit.v / FingerMonoid.v, read SPLIT_NOTE.md first.`
> This is the operational companion for that work: what is being proved, the
> conventions and pitfalls of this dev, the deliberate scope, the integrity
> guardrails, and the live debugging state.

---

## 1. What `FingerSplit.v` proves (spec)

Extends the Claessen-simplified finger tree (verified in the Clairvoyance / `Tick`
demand semantics + reverse physicist's method) with **splitting** and **random
access**, at **worst-case `O(log n)`** cost — matching `concat` in `FingerConcat.v`,
not the amortized-`O(1)` deque ops in `FingerPhysicist.v`.

**Worst-case framing (do not regress).** Two facts already in the repo fix the
character of the bound:
- `debt_le_2depth` (`FingerConcat.v`): any demand's potential is `≤ 2*depth` — the
  `safe_DigitA`/`Debitable_SeqA` potential is structurally logarithmic, so there is no
  hidden `O(n)` backlog.
- `glueD'_cost`'s bound is **independent of the output demand `outD`** — that is the
  worst-case statement.

The split cost lemmas have the identical shape:
`Tick.cost (… ) ≤ split_c1 * depth t + split_c2`, `outD`-independent, then
`depth_log_size` (`FingerSize.v`) gives `O(log n)`.

**Why a new type.** `Seq`/`SeqA` caches no measure, so `splitTree` reading `‖m‖` would
be `O(size)` even with `O(1)` `⊕`. `FingerSplit.v` introduces a **measure-annotated**
tree `MSeq`/`MTuple` (cached `vm`/measures, `O(1)` reads) parameterised over a
`Monoid` (`FingerMonoid.v`). The element measure `md : A -> M` is threaded (Leroy
style). Random access = the size-monoid instance; the *same* `splitTree` gives a
priority queue (interval monoid) and an ordered sequence (last-value monoid).

**The easy half vs the hard half.**
- **Random access (`index`)** discards both halves ⇒ in the demand semantics they are
  demanded at `Undefined` ⇒ the `deepL`/`deepR` reconstruction is never forced ⇒ cost
  is the descent path only. Clean `O(log n)`, proved by a `glueD'_cost`-shaped descent
  induction. **No reconstruction analysis.**
- **Full `split`** forces the halves; its `viewL`/`viewR` cascades must be bounded. The
  tight `O(log n)` needs **one new lemma (M7)**: the reconstruction telescopes because
  `deepL`/`deepR` always refill to a near digit of size ≥ 2, so a cascade only runs
  through disjoint runs of `One`-front spine levels. Formalised with the internal
  potential `lvc`/`rvc` (one-step view cost): per-step amortised cost is constant, sum
  is `O(depth)`.

**Milestones (dependency order).**
- **M1** metrics: port `size_lower_bound`/`depth_log_size`/`size_pos` from
  `FingerSize.v` to `MSeq` (mechanical rename; tuples still hold ≥ 2 elements).
- **M2** cost-scope approx infra: `Exact`/`BottomOf`/`LessDefined` for `MTupleA`/`MSeqA`
  (the order laws / `Lub` are correctness scope — omit).
- **M3** pure ops (done in skeleton): `splitDigit`, `viewL`/`viewR`, `deepL`/`deepR`,
  `splitTree`, `index`.
- **M4** `splitDigit` facts + the near-digit-size property of `deepL`/`deepR` (empty/2/3
  residual ⇒ near digit size ≥ 2; only a singleton makes a `One`). M7 rests on this.
- **M5** demand functions: `viewLD`/`viewRD`/`deepLD`/`deepRD`, `splitTreeD`, `indexD`.
- **M6** `indexD_cost` — descent bound; **closes random access**.
- **M7** reconstruction telescoping (`lvc`/`rvc`, the per-step amortised inequality).
- **M8** `splitTreeD_cost` = M6 descent + two M7 reconstructions.
- **M9** correctness (`split_correct`, `*_approx`/`*_spec`) — admitted future work, as
  `FingerConcat.v` admits `glueD'_approx`/`glueD'_spec`. Split contract (Leroy):
  `¬ p mzero ∧ p (measureSeq md t)`.

(Full pen-and-paper proof, if kept in the repo, lives in the companion design doc.)

---

## 2. Files

| File | Role |
|------|------|
| `FingerCore.v` | `Seq`/`SeqA`, `Digit`/`DigitA`/`Tuple`/`TupleA`, approximation infra, `Debitable`/`safe_DigitA` potential, custom induction (`SeqA_ind`). |
| `FingerSize.v` | `Seq_ind_poly`, `size`/`depth`, `size_lower_bound`, `depth_log_size`. |
| `FingerCons/Snoc/Head/Tail.v` | deque ops + their demand functions/cost. |
| `FingerPhysicist.v` | amortized-`O(1)` deque result (`amortized_cost`). |
| `FingerConcat.v` | **template**: worst-case `O(log n)` `concat`; correctness admitted. |
| `FingerMonoid.v` | **new** — the `Monoid` interface (zero/add/laws) + size/interval/last-value instances. |
| `FingerSplit.v` | **new** — annotated `MSeq`, `splitTree`/`index`/`split`, demand fns, M1–M9. |

`FingerMonoid.vo` must build before `FingerSplit.v`.

---

## 3. Build & inner loop

Detect the toolchain (Rocq 9.x: `rocq compile`; older: `coqc`):
```bash
command -v rocq && rocq --version; command -v coqc && coqc --version
cat _CoqProject 2>/dev/null; ls Makefile dune-project 2>/dev/null
opam list 2>/dev/null | grep -iE 'coq|rocq|hammer|clairvoyance'
```
Whole build: `make -j` (or `dune build`, or `coq_makefile -f _CoqProject -o Makefile && make -j`).

Single-file inner loop (reuse the `-Q`/`-R` flags from `_CoqProject`):
```bash
make FingerSplit.vo 2>&1 | head -60
# or, mirroring _CoqProject's logical map (substitute coqc for 'rocq compile'):
rocq compile -Q . Clairvoyance FingerSplit.v 2>&1 | head -60
```
`sauto`/`hauto`/`qauto` (from `From Hammer Require Import Tactics`) are self-contained —
**no external ATP/`z3`/`eprover` needed**. A `Cannot find a physical path … Hammer`/`…
Clairvoyance` error is a dependency/`_CoqProject` issue, not a proof bug — surface it,
don't delete imports.

---

## 4. Conventions & known friction (this dev)

- **Polymorphic recursion.** `Seq`/`MSeq` are non-uniform (`More` embeds `Seq (Tuple A)`).
  Functions recurse `{struct …}` like `glue`; proofs use hand-written principles
  (`Seq_ind_poly`, `SeqA_ind`, `glue_ind`), **not** auto-generated `_ind`. Port the
  matching principle for `MSeq` rather than calling `induction`.
- **Implicit flags.** `Set Implicit Arguments. Set Contextual Implicit. Set Maximal
  Implicit Insertion.` These force explicit `@`/`(M := …)`/`(A := …)` at recursive calls
  and instance uses — see `Exact_Seq`, `Lub_SeqA`, `debt_SeqA_lub_subadditive`
  (`@Debitable_T _ (@Debitable_SeqA (TupleA A0))`). Expect the same in `Exact_MSeq` and
  `splitTreeD`. Adding these annotations is the *expected* kind of debug.
- **Nested-type instance ordering.** Instances for a nested approximation type must be
  declared **innermost-first**: `DigitA`/`TupleA` before `SeqA` in `FingerCore.v`. The
  `MTupleA` instances must precede the `MSeqA` ones for the same reason (see §7).
- **`Tick` monad.** `let+ x := e in k` (bind), `e >> k` (then), `Tick.tick/ret/cost/val`;
  cost = number of `Tick.tick`s. `bottom_of`/`exact`/`is_approx` from `Approx`/`ApproxM`.
- **Monoid interface.** Use `mzero`/`madd` (infix `<+>`), never raw `+`; laws live in the
  class; the element measure is the threaded `md : A -> M`.
- **Tactics:** `sauto`/`hauto`/`qauto`, `mgo_`/`keep_mgo_`/`mgo_brute_force`, `teardown`,
  `invert_clear` (all custom or from coq-hammer), `lia`/`nia` (split nonlinear: `nia`
  then `lia`). Match the nearest analogous proof's style.

---

## 5. Scope — what is *intentionally* incomplete

`FingerSplit.v` is **cost-scope**, mirroring `FingerConcat.v`. Leave these alone unless
explicitly told to close them:
- `Parameter`s: `viewLD`, `viewRD`, `deepLD`, `deepRD`.
- `Admitted` lemmas: `lvc_le_depth`, `rvc_le_depth`, `viewLD_cost`, `viewRD_cost`,
  `deepL_reconstruction_cost`, `deepR_reconstruction_cost` (**M7**), `indexD_cost`
  (**M6**), `splitTreeD_cost` (**M8**), `index_O_log_n`, `split_O_log_n`.
- The commented-out correctness block.

Everything else must genuinely elaborate: all type defs, `Monoid`/instances, every pure
`Definition`/`Fixpoint`, the `Exact`/`BottomOf`/`LessDefined` instances, and
`splitTreeD`/`indexD`.

---

## 6. Guardrails (verification integrity — non-negotiable)

A "debug" here means making the skeleton **elaborate**, with only the §5 placeholders
left. It is **not** "make `make` exit 0 by any means." Do **not**:
- weaken/generalise-away a theorem statement or add hypotheses to make it provable;
- replace a proof meant to close with `Admitted`/`admit`/`Abort`, or add any `Axiom`;
- comment out / rename-to-hide / `Parameter`-ise a lemma to dodge an error;
- change a `Definition`/`Fixpoint` so a downstream lemma becomes vacuously true;
- reintroduce amortized framing for split/concat cost (worst-case), or touch
  `safe_DigitA`/`Debitable_SeqA` without flagging;
- refactor working proofs in `FingerCore`/`FingerConcat`/`FingerPhysicist`/etc. Confine
  edits to `FingerMonoid.v`/`FingerSplit.v`; if an upstream fix is genuinely needed,
  explain why first.

If a statement looks wrong/unprovable as written, **stop and report** with the exact
error and diagnosis; do not silently change what it claims. Prefer **minimal diffs**;
recompile after each change; log fixes in §7.

---

## 7. Debug log (current → append new entries here)

### [FIXED] Error 1 — missing `LessDefined` instance for `MTupleA`
**Symptom** (compiling `FingerSplit.v`):
```
Could not find an instance for "LessDefined (T (MSeqA M (MTupleA M A)))"
```
**Cause.** Elaborating `LD_MMoreA` (constructor of `LessDefined_MSeqA`), the middle
field `T (MSeqA M (MTupleA M A))` forces resolution of `LessDefined (MSeqA M (MTupleA M
A))` → `LessDefined (MTupleA M A)`, for which **no instance exists**. `FingerSplit.v`
defines `LessDefined_MSeqA` but omits the `MTupleA` analogue. Compare `FingerCore.v`:
`LessDefined_TupleA` (with `Existing Instance` + `Hint Constructors`) is declared
**before** `LessDefined_SeqA` exactly for this chain (innermost-first, §4).

**Fix.** Add, immediately **before** `LessDefined_MSeqA`, mirroring `LessDefined_TupleA`
(pointwise; cached measure `m` shared on both sides, matching `LD_MMoreA`'s shared `vm`):
```coq
Inductive LessDefined_MTupleA {M A} `{LessDefined A} : LessDefined (MTupleA M A) :=
  | LD_MPairA (m : M) x1 x2 y1 y2 :
      x1 `less_defined` x2 -> y1 `less_defined` y2 ->
      MPairA m x1 y1 `less_defined` MPairA m x2 y2
  | LD_MTripleA (m : M) x1 x2 y1 y2 z1 z2 :
      x1 `less_defined` x2 -> y1 `less_defined` y2 -> z1 `less_defined` z2 ->
      MTripleA m x1 y1 z1 `less_defined` MTripleA m x2 y2 z2.
#[global] Existing Instance LessDefined_MTupleA.
#[global] Hint Constructors LessDefined_MTupleA : core.
```
(`x1 `less_defined` x2` at `T A` resolves via `LessDefined_T` ← `LessDefined A`, ✓.)

**Expected next.** A further `Could not find an instance for LessDefined …` is the same
class — keep mirroring the `DigitA`→`TupleA`→`SeqA` instance ordering/laws from
`FingerCore.v`.

### [FIXED] Error 2 — `splitTreeD` conflates the pure and approximation element types
**Symptom** (compiling `splitTreeD`, middle/`p vm_t` branch):
```
The term "mD" has type "T (MSeqA M (MTuple M A))"
while it is expected to have type "T (MSeqA M (MTupleA M ?A))".
```
**Cause.** `splitTreeD : (t : MSeq M A) -> SplitDmd M A -> Tick (T (MSeqA M A))` uses ONE
type parameter for both the *pure input* element and the *demand's approximation*
element. They coincide only at the leaves (via `Exact_id`). On the spine the pure
element `MTuple M A` and its approximation `MTupleA M B` differ, so the recursive call on
`m : MSeq M (MTuple M A)` returns a demand over the *pure* tuple,
`T (MSeqA M (MTuple M A))`, which cannot fill `MMoreA`'s middle slot
`T (MSeqA M (MTupleA M B))`.

**Fix.** Mirror `glueD'` (`FingerConcat.v`, `Fixpoint glueD' (A B : Type) `{Exact A B}
…`): parameterise **every demand-side definition** by the pure element `A` AND its
approximation `B`, with `Exact A B`. Input over `A`; output demand and returned demand
over `B`. The recursive call shifts both — `A := MTuple M A`, `B := MTupleA M B` (the
`Exact` lifted by `Exact_MTuple`) — giving `mD : T (MSeqA M (MTupleA M B))`, exactly
`MMoreA`'s slot. Key line:
```coq
let+ mD := splitTreeD (A := MTuple M A) (B := MTupleA M B)
             measureMTuple (MPair mzero dflt dflt) p vpr m
             (Undefined, Undefined, Undefined) in
```
Apply the dual `{A B} `{Exact A B}` to `viewLD`/`viewRD`/`deepLD`/`deepRD`,
`splitTreeD`, `indexD`, and to the cost-lemma statements (demands become `B`-typed;
`lvc`/`rvc` and all bounds are over the pure tree and unchanged). Concrete random access
instantiates `B := A` via `Exact_id`.

**Takeaway for M6/M8.** The cost-lemma *statements* must stay general in `B` even though
they elaborate at `B := A` (via `Exact_id`) without it: the inductive proofs recurse at
`B := MTupleA M B`, so the IH only applies to a `B`-general statement. This is precisely
why `glueD'_cost` is stated `(A B : Type) `{Exact A B}`. Do not specialise these
statements to a fixed `B`.