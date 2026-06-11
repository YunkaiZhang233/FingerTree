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

The split cost lemmas are `outD`-independent; `depth_log_size` (`FingerSize.v`) then
gives `O(log n)`:
- `indexD_cost`     : `Tick.cost (indexD …)     ≤ split_c1 * depth t + split_c2`;
- `splitTreeD_cost` : `Tick.cost (splitTreeD …) ≤ (split_c1 + 2) * depth t + (split_c2 + 3)`.

The `+2`/`+3` on `splitTreeD_cost` is **structural** (see §7): the top-level
reconstruction adds `lvc m + rvc m ≈ 2·depth`, so split's leading constant is strictly
larger than index's — no single constant serves both.

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
  induction. **No reconstruction analysis.** As of 2026-06-11 random access is also
  **demand-correct** (`indexD_approx`/`indexD_spec`/`index_spec`, axiom-free) — see the
  §7 entry for the `lookupTree` redefinition this required.
- **Full `split`** forces the halves; its `viewL`/`viewR` cascades must be bounded. The
  tight `O(log n)` needs **one new lemma (M7)**: the reconstruction telescopes because
  `deepL`/`deepR` always refill to a near digit of size ≥ 2, so a cascade only runs
  through disjoint runs of `One`-front spine levels. Formalised with the internal
  potential `lvc`/`rvc` (one-step view cost): per-step amortised cost is constant, sum
  is `O(depth)`. **As built (§7): the mechanized `splitTreeD` is a *cost scaffold*** — its
  recursion passes `(Undefined,Undefined,Undefined)`, flattening reconstruction to the
  top level, so this telescoping is **not** exercised; flat `deepLD_cost ≤ lvc m` /
  `deepRD_cost ≤ rvc m` close M8. The telescoping is the correct argument for the
  *faithful* demand function and is **relocated to M9**.

**Milestones (dependency order) — cost scope now complete (`Qed`); see §5.**
- **M1** metrics: ✅ ported `MSeq_ind_poly`, `MSeq_nil_dec`, `size_lower_bound`,
  `size_pos`, `depth_log_size` from `FingerSize.v` (mechanical rename; tuples still ≥ 2).
- **M2** cost-scope approx infra: ✅ `Exact`/`BottomOf`/`LessDefined` for `MTupleA`/`MSeqA`
  (innermost-first; order laws / `Lub` omitted — correctness scope).
- **M3** pure ops: ✅ `splitDigit`, `viewL`/`viewR`, `deepL`/`deepR`, `splitTree`, `index`.
- **M4** near-digit-size property: folded into `lvc`/`rvc` + `lvc/rvc_le_depth`; returns
  as an explicit obligation for M9's per-level reconstruction.
- **M5** demand functions: ✅ `viewLD`/`viewRD` (`Fixpoint`), `deepLD`/`deepRD`/`toTreeD`,
  `splitTreeD`, `indexD` — real definitions (no longer `Parameter`s), dual-typed `{A B}`.
- **M6** `indexD_cost` (+ `index_O_log_n`): ✅ descent bound; **closes random access, faithful**.
- **M7** reconstruction telescoping: **reframed** — the scaffold doesn't need it; flat
  `deepLD_cost`/`deepRD_cost` (from `viewLD_cost`/`viewRD_cost`) replace it. Telescoping → M9.
- **M8** `splitTreeD_cost` (+ `split_O_log_n`): ✅ M6 descent + flat reconstruction;
  constant `(split_c1+2)·depth t + (split_c2+3)`. **Scaffold result.**
- **M9a** (✅ 2026-06-11) — **index demand-correctness done**: `indexD_approx`,
  `indexD_spec`, `index_spec` all `Qed`, closed under the global context. Pure `index`
  redefined via the non-reconstructing `lookupTree`; `splitTreeD` threads the genuine
  pivot demand (`pivotDmd`); clairvoyant side is the pruned `lookupTreeA`. See §7.
- **M9b** correctness + faithful split — **in progress** (improvement-plan Item 4; see
  **`SPLIT_FAITHFUL_PLAN.md`** for the full design/status ledger). Done (2026-06-11, all
  `Qed`, axiom-free): **4a** the faithful `splitTreeD_f` + demand machinery
  (`viewLD_f`/`viewRD_f`/`deepLD_f`/`deepRD_f`/`pivotNodeDmd_f`, skeleton demands
  `mseqSkel`/`addSkel`); **4b** its worst-case cost via the M7 telescoping, now
  load-bearing (`splitTreeD_f_cost_pot` with the chain-potential IH;
  `splitTreeD_f_cost`, `split_f_O_log_n` — in the audit); **4c helper ladder** (15
  approximation lemmas). Remaining: 4c headline `splitTreeD_f_approx` (proof plan
  written), 4d `splitTreeD_f_spec` (designed); `split_correct` optional.

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

`FingerSplit.v` is **cost-scope**, mirroring `FingerConcat.v`. **The cost scope is now
complete — zero admits.** Every cost lemma is at `Qed`; the only remaining incomplete
item is the M9 correctness block.

- **Closed (`Qed`):** `lvc_le_depth`, `rvc_le_depth`, `viewLD_cost`, `viewRD_cost`,
  `toTreeD_cost`, `deepLD_cost`, `deepRD_cost`, `indexD_cost` (**M6**), `splitTreeD_cost`
  (**M8**), `MSeq_ind_poly`, `MSeq_nil_dec`, `size_lower_bound`, `size_pos`,
  `depth_log_size` (**M1**), `index_O_log_n`, `split_O_log_n`.
- **All demand functions are real definitions** (no longer `Parameter`s): `viewLD`/`viewRD`
  (`Fixpoint`), `deepLD`/`deepRD`/`toTreeD` (`Definition`), `splitTreeD`, `indexD`.
- **The two `deep*_reconstruction_cost` telescoping lemmas were removed** — the scaffold
  doesn't use them (§7); they return with the faithful function in M9.
- **Closed (`Qed`) as of 2026-06-11 (M9a, improvement-plan Item 3):** `indexD_approx`,
  `indexD_spec`, `index_spec`, the workhorse `lookupTreeA_spec`, helper specs
  (`measureDigitA_exact_spec`, `lookupDigitA_exact_spec`, `lookupNodeA_spec`),
  `pivotNodeDmd_approx`, `indexD_val_thunk`, `measureMTupleA_coh`, and the
  `MTupleA`/`MSeqA` order-law instances. All axiom-free.
- **Closed (`Qed`) as of 2026-06-11 (M9b stages 4a-4c-partial, improvement-plan Item 4):**
  `splitTreeD_f` and its demand machinery; `viewLD_f_cost`/`viewRD_f_cost`,
  `deepLD_f_cost_lvc`/`deepRD_f_cost_rvc`, `viewL_None`/`viewR_None`,
  `lvc_pos`/`rvc_pos`/`lvc_toTree`/`rvc_toTree`; the telescoping
  `splitTreeD_f_cost_pot` + headline `splitTreeD_f_cost`/`split_f_O_log_n` (audited);
  and the 4c approximation helper ladder (15 lemmas, from `mtupleSkel_approx` to
  `pivotNodeDmd_f_approx`). All axiom-free.
- **Still intentionally incomplete (M9b remainder):** the headline
  `splitTreeD_f_approx` (proof plan in `SPLIT_FAITHFUL_PLAN.md` §5), `splitTreeD_f_spec`
  (4d, design in §6 there), `split_correct` (optional). **Do not close without being
  asked.**

The integrity guardrails (§6) continue to apply to all M9 work: do not weaken a spec
to make it provable, and do not let the *scaffold* `splitTreeD` quietly become the
claimed faithful function — M9 means writing the faithful demand function, not relabeling
the scaffold.

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

### [DONE] M1 metrics ported to `MSeq`
`MSeq_ind_poly` (hand `fix`; motive `forall A, MSeq M A -> Prop` with `M` fixed across
the spine), `MSeq_nil_dec`, `size_lower_bound`, `size_pos`, `depth_log_size` — verbatim
port of `FingerSize.v` (tuples still ≥ 2 elements; the extra `vm` field is
size/depth-irrelevant). Unblocks `index_O_log_n`/`split_O_log_n`.

### [DONE] M5 demand functions promoted from `Parameter` to real definitions
`viewLD`/`viewRD` are `Fixpoint`s (one `Tick.tick` per visited `MMore`; recurse into the
middle on a `One` front — the cascade). `deepLD`/`deepRD`/`toTreeD` are `Definition`s,
**cost 0 when the output demand is `Undefined`** — this is what zeroes reconstruction
along the `index` descent. All dual-typed `{A B} `{Exact A B}` (Error 2) and
`simpl nomatch`. The *returned input demands* are M9 placeholders (cf. `unbundle`); only
the cost is proved here.

### [KEY FINDING] mechanized `splitTreeD` is a cost scaffold → M7 reframed, M8 constant bumped
`splitTreeD`'s middle branch recurses with `(Undefined, Undefined, Undefined)`, so the
descent demands nothing of the recursive halves and **every reconstruction below the top
level is the cost-0 branch.** Reconstruction fires only at the top call, as one
`viewLD`/`viewRD` on the *original* `m` (`deepLD md dflt [] m sf rD`, not on a
recursively-built half). Consequences:
- **M7 telescoping is not exercised.** `deepLD_cost ≤ lvc m` / `deepRD_cost ≤ rvc m` are
  flat (one view each, via `viewLD_cost`/`viewRD_cost`); the two `deep*_reconstruction_cost`
  lemmas were **removed**.
- **M8 is not an induction.** Since the recursive call *is* `indexD` on `m`,
  `splitTreeD_cost` = `indexD_cost` (descent) + `deepLD_cost` + `deepRD_cost` +
  `lvc/rvc_le_depth`, all `lia`.
- **M8's constant is strictly larger than M6's:** `(split_c1 + 2)·depth t + (split_c2 + 3)`.
  The top reconstruction pays `lvc m + rvc m ≈ 2·depth m` in full, so split's leading
  coefficient is `split_c1 + 2`. No single constant serves both index and split — the
  `+2` is structural, not a tuning artifact (raising `split_c1` scales both sides).
- **Faithfulness caveat.** The scaffold does *not* model the pure `splitTree`'s per-level
  reconstruction, so it would not satisfy `splitTreeD_spec`; full split's result is
  therefore **scaffold-level**. **Random access is unaffected and faithful** (`index`
  genuinely demands nothing of the halves), so M6 is a complete result. The §4.2
  telescoping argument is correct and **relocated to M9's faithful function**, where
  `lvc`/`rvc` finally earn their place.

Not a guardrail violation: this is a *reported* scaffold. No statement was weakened to be
vacuous — M6/M8 are honest `outD`-independent bounds; the only limitation is that M8
bounds a scaffold, and it is flagged here and in the design doc. M9 must write the
faithful function, not relabel this one.

### [FIXED] `splitTreeD_cost` `MUnit` case stuck before `lia`
**Symptom.** `S (Tick.cost (let '(_, xD, _) := outD in Tick.ret (Thunk (MUnitA xD)))) <= 27`
— opaque `outD` blocks the `let` from reducing, so `Tick.cost` stays an atom and `lia`
gives up (`27 = split_c2 + 3`, since `depth (MUnit _) = 0`).
**Fix.** Destruct the demand first: `destruct outD as [[? xD] ?]; simpl; lia` (goal
collapses to `1 <= 27`). Same root cause as the earlier `MUnitA` stuck goal — an opaque
tuple demand blocking reduction.

### [DONE] M9a — index demand-correctness (improvement-plan Item 3, 2026-06-11)

**Key finding (design-level).** The pivot-projection of `splitTree` is **not**
demand-isolated: at each recursive level the pivot's position inside the borrowed
tuple `xs` is found by `splitDigit md p (vpr <+> ‖ml‖) (tupleToDigit xs)`, where
`ml` is the recursively *reconstructed* left half. A lazy consumer of the pivot
alone therefore forces the cached-measure chain of every left half down the
descent (real forcing for the size monoid, whose `p` inspects its argument) —
and bounding that cost needs the §C.2 telescoping, i.e. faithful-split (M9b)
machinery. The fix, anticipated by the improvement plan's "pruned `indexA`"
hint: define the pure lookup as the dedicated **non-reconstructing descent
`lookupTree`** (Hinze–Paterson's `lookupTree`, cf. `Data.Sequence`), which
threads the accumulated prefix measure up through the recursion instead of
recomputing it from `ml`. `index := snd ∘ lookupTree` (no existing theorem
mentioned the old pure `index`, so nothing broke); `lookupTree`'s branch
conditions are syntactically `splitTree`'s, so both locate the same pivot and
the descent/tick structure is unchanged.

**Demand fix.** `splitTreeD`'s recursion passed `(⊥, ⊥, ⊥)`, dropping the pivot
demand — exposed by the `MUnit`-middle case, where the pivot tuple sits in the
(undemanded) unit slot rather than in an `exact`-demanded digit. Now it passes
`(⊥, pivotDmd …, ⊥)`: `pivotDmd` replays the pure `lookupTree` on the middle
(demand functions take pure inputs) and wraps `pivotNodeDmd`, which demands the
scanned tuple components in full (generic `md` forces what it measures), the
pivot slot at the incoming `xD`, and nothing beyond the pivot. Cost lemmas
survived with two one-line IH-instantiation changes (the gates `lD`/`rD` are
still `⊥` on the index path).

**Proof architecture** (all in `FingerSplit.v` §8, all `Qed`, axiom-free):
- `mseq_valid` — cache validity (`MMore` cache = middle's measure, recursively);
  the only precondition besides `t <> MNil`. Inside the descent it rules out
  `MNil` middles (`vm = mzero` + `madd_zero_r` contradicts the branch guards).
- `indexD_approx` — `MSeq_ind_poly` induction; needs `pivotNodeDmd_approx` and
  the `Reflexive` instances; no preconditions beyond `xD ⊑ exact pivot`.
- `lookupTreeA` — pruned clairvoyant lookup (no `deepLA`/`viewLA`); one `tick`
  per visited node, helpers tick-free, so its cost meets `indexD`'s budget
  exactly. Recursion via the `forcing mT (fun m => …)` guard pattern.
- `lookupTreeA_spec` — the lockstep workhorse, strengthened payload:
  `fst out = pure prefix measure` ∧ `xD ⊑ snd out` ∧
  `snd out ⊑ Thunk (exact pivot)` ∧ `cost ≤ Tick.cost (indexD …)`.
  The two-sided sandwich pins forced values to `exact` so the measure-coherence
  hypothesis (`mdB v = md x` on sandwiched `v`; `measureMTupleA_coh` at spine
  levels, trivial for the size monoid) makes the clairvoyant branch decisions
  equal the pure ones. **No monotonicity lemmas needed** — the IH applies to the
  recursive demand exactly (lockstep), unlike `glueD'_spec`'s `glueA_mon` route.
- `indexD_spec` / `index_spec` — headline wrappers (the latter at the size
  monoid, combining with `index_O_log_n` for "demand-correct AND O(log n)").

**Tactic notes.** `Arguments lookupDigit/lookupTree` must NOT be `simpl nomatch`
(the bodies expose stuck `if`s, so nomatch blocks the constructor-case reduction
the proofs need); conversely `measureDigitA`/`lookupDigitA` are `simpl never`
past their own spec lemmas so the workhorse sees folded calls. `destruct (p …)
eqn:` abstracts hypotheses too (8.19), so no `rewrite … in Hx` after it.
`Tick.val` does not reduce through folded binds — use a conversion-checked
`assert (Thunk sD = Thunk (… Tick.val (splitTreeD …) …)) by (rewrite <- HsD, <- HsD'; reflexivity)`.
`Core`'s `>>` must be re-imported after `Open Scope tick_scope` (the `fconsA'`
pattern). T-level `less_defined` inversions: use the `TThunk_inv`/
`TThunkThunk_inv` helper lemmas, not inversion patterns.

### [IN PROGRESS] M9b — faithful split (improvement-plan Item 4, 2026-06-11)

Stages 4a (faithful demand function), 4b (telescoping cost, banked
fallback checkpoint) and the 4c helper ladder are `Qed` and committed
(`daf10ee`, `7dfa3f7`, `0093a4b`); `make audit` green at 29 theorems.
**All design detail, statements, proof plans for the remaining 4c
headline + 4d, and the session's proof-engineering lessons (the
`[[`/`]]` lexer keywords, auto-implicit binders, `simpl never` vs `cbn`
whitelists and the load-bearing file ordering, the `cbn`-unfolds-
Definitions-on-constructors trap, folded-`exact` inversion recipes, the
diverging `repeat match goal` anti-pattern) live in
`SPLIT_FAITHFUL_PLAN.md` — read it before resuming.**
