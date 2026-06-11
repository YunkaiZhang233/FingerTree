# SPLIT_FAITHFUL_PLAN.md — Item 4: the faithful split (M9b)

> Design document and status ledger for improvement-plan **Item 4**
> (faithful, demand-correct split).  Companion to `SPLIT_NOTE.md` (the
> operational note for all of `FingerSplit.v`); this file carries the
> Item-4-specific design, the proof architecture that is already `Qed`,
> and the worked-out plan for the remaining stages.  Read this before
> touching any `*_f` definition or lemma.

---

## 0. Status at a glance (2026-06-11)

| Stage | Content | Status | Commit |
|-------|---------|--------|--------|
| 4a | Faithful demand machinery (`splitTreeD_f` + helpers) | ✅ `Qed`/compiled | `daf10ee` |
| 4b | Telescoping worst-case cost (`splitTreeD_f_cost_pot` → `splitTreeD_f_cost`, `split_f_O_log_n`) | ✅ `Qed`, axiom-free, in audit | `daf10ee`, `7dfa3f7` |
| 4c | Approximation — helper ladder (15 lemmas) | ✅ `Qed` | `0093a4b` |
| 4c | Approximation — headline `splitTreeD_f_approx` | ✅ `Qed`, axiom-free, in audit | `620b2c5` |
| 4d | `splitTreeD_f_spec` (clairvoyant semantics + lockstep) | ⏳ **next** — designed only (§6) | — |

`FingerSplit.v`: 64 `Qed`, 0 admits.  `make audit`: green, 30 theorems,
all new results *Closed under the global context*.  Nothing pushed to
any remote.  The plan's **4b fallback checkpoint is banked**: even if
4d stalls, the audit line for split has already improved from "cost
proved against a simplified demand function" to "cost AND demand
approximation proved against the faithful demand function".

File layout of the new material (all in `src/FingerSplit.v`):

- **Section 9** — definitions: 9a skeletons/merges, 9b reassembly,
  9c cascades (`viewLD_f`/`viewRD_f`), 9d reconstruction
  (`deepLD_f`/`deepRD_f`), 9e pivot (`pivotNodeDmd_f`) + `splitTreeD_f`.
- **Section 10** — cost: cascade costs, pure chain-potential facts,
  `viewL_None`/`viewR_None`, the per-level telescoping facts, the 4c
  approx **helper ladder** (deliberately placed *before* the
  `simpl never` block — see §7), the `Arguments … simpl never` blocks,
  then `splitTreeD_f_cost_pot` / `splitTreeD_f_cost` /
  `split_f_O_log_n`.

---

## 1. Design decision: coexist, don't replace

The scaffold `splitTreeD` (Section 5) and every Section-5–8 result is
untouched; the faithful function `splitTreeD_f` lives alongside it.
This preserves all Item-3 theorems (`indexD_*`) verbatim and keeps the
diff reviewable.  The guardrail from SPLIT_NOTE §6 is honoured: M9b is
a *new* faithful function, not a relabelled scaffold.

What "faithful" adds over the scaffold: the scaffold's recursion passes
`(⊥, pivotDmd …, ⊥)`, so reconstruction below the top level is never
demanded.  `splitTreeD_f` unbundles the caller's demands on the two
result halves through `deepRD_f`/`deepLD_f` (and, when a residual digit
is empty, through the cascades `viewRD_f`/`viewLD_f`) into genuine
demands `(mlD, xsD, mrD)` on the recursive halves, and threads them
through the recursive call.

## 2. Demand conventions (load-bearing)

1. **Generic-measure forcing.**  Computing `md x` of a leaf element
   demands `x` in full (`Thunk (exact x)`).  At spine levels the
   measure is `measureMTuple`, which reads a *strict* cache field, so
   it demands only the tuple's root constructor.
2. **Skeleton demands.**  Building `mdeep pr m sf` computes the cache
   `‖m‖ = measureSeq measureMTuple m`, which forces: `m`'s root, its
   digit roots, and the cached measures (= roots) of those digits'
   tuples.  This is the demand `mseqSkel m` (with `mtupleSkel`,
   `digitSkel`).  Merging a skeleton into a caller demand is *shallow*
   (depth ≤ 2: root, digit roots, tuple roots) because any `Thunk`
   tuple demand already contains its strict cache — `addSkel`/
   `addDigitSkel`/`addTupleSkel` do this merge, which is why **no
   general `Lub` instance is needed**.
3. **Visited digits at `exact`.**  The descent computes `vpr`, measuring
   the front digit in full; the rear digit is over-demanded at `exact`
   for uniformity with the scaffold (sound: over-demand only).
4. **The `‖ml‖` chain is finally accounted.**  Locating the pivot inside
   the borrowed tuple scans at base `vpr <+> ‖ml‖` (`ml` = recursively
   *reconstructed* left half) — the very chain that made the
   pivot-projection of `splitTree` non-demand-isolated (Item-3 finding,
   Section 2b of the file).  Hence `mlD := addSkel ml mlD0` **always**
   contains `mseqSkel ml`, even when the caller's left demand is `⊥`.
   It costs no ticks (measure reads are free) — it matters for
   approx/spec fidelity, not for the cost bound.

## 3. The definitions (Section 9) — quick reference

| Definition | Type (essentials) | Role |
|---|---|---|
| `mtupleSkel t` | `MTuple M A → MTupleA M B` | tuple root + strict cache, contents `⊥` |
| `digitSkel d` | `Digit (MTuple M A) → DigitA (MTupleA M B)` | digit of tuple skeletons |
| `mseqSkel m` | `MSeq M (MTuple M A) → MSeqA M (MTupleA M B)` | what one cache computation forces |
| `addTupleSkel/addDigitSkel/addSkel` | merge skeleton into a demand | shallow lub-substitute |
| `tupleDmdOfDigitDmd t1 dD` | digit demand → borrowed-tuple demand | `tupleToDigit` inverse; `⊥ ↦ Thunk (mtupleSkel t1)` (the borrow forces the root) |
| `toTreeDmd d tD` | demand on `toTree md (digitToList d)` → digit demand | empty-middle rebuild; `toTree` caches are `mzero`, so only element slots |
| `borrowDmdL t1 m' outD` | node demand → `(t1D, m'D, sfD)` | unbundles `mdeep md (tupleToDigit t1) m' sf`; `m'D = addSkel m' mD` |
| `borrowDmdR m' t1 outD` | node demand → `(prD, m'D, t1D)` | mirror |
| `viewLD_f dflt t xD tD` | `Tick (T (MSeqA M B))` | one-uncons demand; 1 tick/visited node; recurses on `One` front; `Some`-case via `borrowDmdL`, `None`-case via `toTreeDmd` |
| `viewRD_f` | mirror (rear) | |
| `deepLD_f dflt r m sf outD` | `Tick (list (T B) × T (MSeqA M (MTupleA M B)) × T (DigitA B))` | unbundle `deepL`'s output demand; gates on `outD = ⊥` (cost 0); `r = []` → cascade |
| `deepRD_f dflt pr m l outD` | `Tick (T (DigitA B) × … × list (T B))` | mirror |
| `pivotNodeDmd_f md p b xs xD rEl` | `MTupleA M B` | `pivotNodeDmd` + after-pivot slots fed from the right half's unbundled element demands `rEl` |
| `splitTreeD_f md dflt p i t outD` | `Tick (T (MSeqA M B))` | the faithful demand function; branch/tick structure of the scaffold; recursion gets `(addSkel ml mlD0, Thunk (pivotNodeDmd_f …), mrD)` |

Data flow in branch 2 (the only recursive branch): recompute pure
`(ml, xs, mr) = splitTree … m` and `(l, x, r) = splitDigit … (tupleToDigit xs)`
at base `b = vpr <+> ‖ml‖`; `deepRD_f dflt pr ml l lD ⇒ (_, mlD0, _)`;
`deepLD_f dflt r mr sf rD ⇒ (rEl, mrD, _)`; recurse with
`(addSkel ml mlD0, Thunk (pivotNodeDmd_f md p b xs xD rEl), mrD)`.
Discarded components (`prD`, `lEl`, `sfD`) are covered by `exact
pr`/`exact sf`/the scan-exact slots of `pivotNodeDmd_f`.

## 4. Stage 4b — the telescoping cost proof (done)

**Statement** (equation form, deliberately — see §7.3):

```coq
Theorem splitTreeD_f_cost_pot :
  splitTree md dflt p i t = (l, x, r) ->
  Tick.cost (splitTreeD_f md dflt p i t outD) + rvc l + lvc r
    <= split_f_c1 * depth t + split_f_c2.    (* c1 = 5, c2 = 3 *)
```

The naive recurrence pays `rvc ml + lvc mr` per level (two cascades on
the recursive halves) → O(depth²).  The IH instead **carries the chain
potential of the pure result halves**: at each level the per-level
facts

```coq
deepLD_f_cost_lvc : cost (deepLD_f dflt r m sf outD) + lvc (deepL md dflt r m sf) <= lvc m + 2
deepRD_f_cost_rvc : cost (deepRD_f dflt pr m l outD) + rvc (deepR md dflt pr m l) <= rvc m + 2
```

trade the credit supplied by the recursive IH (`rvc ml + lvc mr`) for
this level's cascade cost plus the credit owed upward (`rvc l + lvc r`).
The three residual shapes are §C.2's E/O/M types: empty residual — pay
the cascade, the refilled digit has size ≥ 2 so the chain resets (≤ 2);
one element — pay nothing, chain grows by 1 (the credit carries);
two/three elements — pay nothing, chain resets to 1.  Branch 2 then
closes by one `lia` from the IH + the two facts; A ≥ 5 absorbs the
constants.  Supporting facts: `lvc_pos`/`rvc_pos` (≥ 1),
`lvc_toTree`/`rvc_toTree` (≤ 2), `viewL_None`/`viewR_None`
(`None ⇒ MNil`), `viewLD_f_cost ≤ lvc t` / `viewRD_f_cost ≤ rvc t`.

Headline corollaries: `splitTreeD_f_cost` (drops the potentials;
`outD`-independent = worst-case) and `split_f_O_log_n` (via
`depth_log_size`).  All in `src/Audit.v`.

This was the plan's "one new proof idea" — it worked exactly as
predicted (improvement-plan Item 4, stage 4b), with **no** extra side
condition discovered mid-proof.

## 5. Stage 4c — approximation: DONE (ladder + headline)

> **Status update (`620b2c5`).**  The headline `splitTreeD_f_approx` is
> `Qed`, axiom-free, and in the audit.  The proof plan below worked
> verbatim, with ONE correction discovered while typing it in: the
> auto-implicit detection keeps `md dflt r sf` (resp. `md dflt pr l`)
> of `deepLD_f_approx` (resp. `deepRD_f_approx`) **explicit** — consume
> them as `deepLD_f_approx md dflt r1 sf HvL Hr` /
> `deepRD_f_approx md dflt pr l1 HvR Hl`, not by proof terms alone.
> (When in doubt, `About lemma` shows the `Arguments` line; only `m`,
> `outD` and the result components are implicit.)  Everything else —
> the never-block extension, the plain-`cbn` reductions, the
> destruct-eqn/injection skeleton mirrored from the cost theorem, the
> `eapply pivotNodeDmd_f_approx` and IH-specialization recipes, the
> `constructor. constructor; [reflexivity | … | reflexivity]`
> conclusion — went through exactly as planned, first compile after
> that fix.

**Done (15 `Qed` lemmas, commit `0093a4b`)**, in file order:
`mtupleSkel_approx`, `digitSkel_approx`, `mseqSkel_approx`,
`addTupleSkel_approx`, `addDigitSkel_approx`, `addSkel_approx`,
`tupleDmdOfDigitDmd_approx`, `toTreeDmd_approx`, `borrowDmdL_approx`,
`borrowDmdR_approx`, `viewLD_f_approx`, `viewRD_f_approx`,
`deepLD_f_approx`, `deepRD_f_approx`, `pivotNodeDmd_f_approx`.

Shapes worth knowing when consuming them:

- `viewLD_f_approx` (by `MSeq_ind_poly`; statement-quantified, so its
  arguments are *explicit*… except auto-implicits, see §7.2):
  `viewL md dflt t = Some (x0, t') → xD ⊑ exact x0 → tD ⊑ exact t' →
   Tick.val (viewLD_f dflt t xD tD) ⊑ exact t`.
- `deepLD_f_approx` (equation form):
  `Tick.val (deepLD_f dflt r m sf outD) = (rEl, mD, sfD) →
   outD ⊑ exact (deepL md dflt r m sf) →
   (∀ k, nth k rEl ⊥ ⊑ exact (nth k r dflt)) ∧ mD ⊑ exact m`.
  The slot fact is stated with `nth`-defaults precisely so that an
  empty `rEl` (undemanded half) gives `⊥ ⊑ …` for every k — this is
  what `pivotNodeDmd_f_approx` consumes.
- `deepRD_f_approx`: only the middle fact (its `prD`/`lEl` components
  are discarded by the caller — covered by `exact pr` / scan-exact).
- `pivotNodeDmd_f_approx` (equation form on `splitDigit`):
  `splitDigit md p b (tupleToDigit xs) = (l1, x1, r1) → xD ⊑ exact x1 →
   (∀ k, nth k rEl ⊥ ⊑ exact (nth k r1 dflt)) →
   pivotNodeDmd_f md p b xs xD rEl ⊑ exact xs`.

**Remaining: the headline theorem.**  Statement (component-wise +
equation hypothesis, mirroring the cost theorem; there are no plain
`(a*b)` `LessDefined`/`Exact` instances, so do NOT state it through a
triple-level `is_approx` — that was the `glueD'_approx` lesson too):

```coq
Theorem splitTreeD_f_approx {M} `{Monoid M} :
  forall (A : Type) (t : MSeq M A),
  forall (B : Type) (LDB : LessDefined B)
         (RLDB : Reflexive (less_defined (a := B))) (EAB : Exact A B)
         (md : A -> M) (dflt : A) (p : M -> bool) (i : M)
         (lD : T (MSeqA M B)) (xD : T B) (rD : T (MSeqA M B))
         (l : MSeq M A) (x : A) (r : MSeq M A),
    splitTree md dflt p i t = (l, x, r) ->
    lD `is_approx` l -> xD `is_approx` x -> rD `is_approx` r ->
    Tick.val (splitTreeD_f md dflt p i t (lD, xD, rD)) `is_approx` t.
```

Proof plan (drafted in-session, not yet typed in):

0. **First extend the `simpl never` block** (the one before
   `splitTreeD_f_cost_pot`) with the helpers that occur *directly* in
   `splitTreeD_f`'s body or its reduced goal forms: `addSkel` at
   minimum (it appears in the recursive demand triple; full `cbn` would
   unfold it to a stuck match and break lemma linking); marking
   `mtupleSkel digitSkel mseqSkel addTupleSkel addDigitSkel
   tupleDmdOfDigitDmd toTreeDmd borrowDmdL borrowDmdR` as well is
   harmless and defensive.  (`pivotNodeDmd_f` is `simpl never`
   already.)
1. `MSeq_ind_poly` with the statement as motive (the `indexD_approx`
   pattern).  MNil: `Tick.val = ⊥`, `constructor`.  MUnit: `cbn in
   Hsp`, `injection`, result `Thunk (MUnitA xD)`, `repeat constructor;
   exact Hx`.
2. MMore: `cbn in Hsp. cbn.` (plain `cbn` is safe *because of* the
   never-marks: `splitTreeD_f`/`splitTree` unfold on the constructor,
   `measureDigit`/`splitDigit`/`deepL`/`deepR`/`toTree`/the `_f`
   helpers stay folded), then `destruct (p (i <+> measureDigit md pr))
   eqn:Hp1` (reduces goal and `Hsp` simultaneously — 8.19 `destruct`
   abstracts hypotheses).
3. Branch 1: `destruct (splitDigit md p i pr) as [ [l1 x1] r1] eqn:Hsd`;
   `injection Hsp as ? ? ?; subst`; `cbn`; `destruct (Tick.val
   (deepLD_f (B := B) dflt r1 m sf rD)) as [ [rEl mD] sfD1] eqn:HvL`;
   `cbn`; `pose proof (deepLD_f_approx HvL Hr) as (Hslots & HmD)`
   (application is just the two proof terms — value binders are
   auto-implicit, §7.2); conclude
   `constructor. constructor; [ reflexivity | exact HmD | reflexivity ]`.
4. Branch 2: destruct `splitTree … m` (`eqn:Hst`) and the inner
   `splitDigit` (`eqn:Hsd`); `injection Hsp; subst`; `cbn`; destruct
   the two `Tick.val (deep…)` projections (`eqn:HvR`, `eqn:HvL`) with a
   `cbn` after each (iota through the pattern-lets); facts
   `HmlD0 := deepRD_f_approx HvR Hl` and
   `(Hslots & HmrD) := deepLD_f_approx HvL Hr`; assemble the IH's three
   demand facts:
   `addSkel_approx HmlD0 : addSkel ml mlD0 ⊑ exact ml`,
   `constructor; pivotNodeDmd_f_approx Hsd Hx Hslots : Thunk (pivotNodeDmd_f …) ⊑ exact xs`,
   `HmrD`; specialize the IH (`indexD_approx` style:
   `specialize (IH (MTupleA M B) _ _ _ measureMTuple (MPair mzero dflt
   dflt) p (i <+> measureDigit md pr) _ _ _ ml xs mr Hst Hml' Hxs'
   HmrD)` — the `_ _ _` demand slots are inferred from the fact types);
   conclude as in branch 1 with `exact IH` in the middle slot.
5. Branch 3: `deepRD_f_approx HvR Hl` for the middle; conclude as in
   branch 1.

Watch out for: the `reflexivity` side goals need the `Reflexive`
instances (`#[local] Existing Instance Reflexive_LessDefined_T` is
already active file-wide from Section 8d; digit reflexivity resolves
via the `LessDefined_DigitA_refl` hint as in `indexD_approx`).

After it's `Qed`: add `splitTreeD_f_approx` to `src/Audit.v`, run
`make audit`, commit.

## 6. Stage 4d — `splitTreeD_f_spec` (design sketch, multi-pass)

Pass 1 — **clairvoyant semantics** (new Section, after the Core
re-import so `Core.M`'s `>>`/`let!` are in scope; remember `Core.M` vs
the monoid carrier `M` — qualify):

- `mdeepA : T (DigitA B) → T (MSeqA M (MTupleA M B)) → T (DigitA B) → Core.M (MSeqA M B)`
  must compute the strict cache by forcing exactly the skeleton:
  `measureSeqA` forces the middle's root, digit roots, tuple roots
  (`measureMTupleA` on each) — this is BY CONSTRUCTION aligned with
  `mseqSkel`, which is what makes the spec provable.  Keep helpers
  tick-free (the Item-3 accounting: one `tick` per visited tree node
  only).
- `toTreeA`, `viewLA`/`viewRA` (tick per visited node, recursion via
  the `forcing mT (fun m => …)` guard pattern), `deepLA`/`deepRA`
  (tick-free wrappers choosing residual vs borrow), `splitTreeA`
  (tick per node, three-way branch via `measureDigitA`, returns the
  triple of `T`-values; the halves built with `thunk (mdeepA …)` so
  cost is only paid when demanded).

Pass 2 — **helper specs** (sandwich style, reusing Item-3 infra:
`TThunk_inv`/`TThunkThunk_inv`, `measureMTupleA_coh`, `mseq_valid`,
`measureDigitA_exact_spec`/`lookupDigitA_exact_spec` analogues for the
view/deep path; mark each helper `simpl never` after its spec).  The
preconditions to expect: `mseq_valid t` and the measure-coherence
sandwich `(∀ x v, exact x ⊑ v → v ⊑ exact x → mdB v = md x)`, exactly
as in `lookupTreeA_spec`.

Pass 3 — **the lockstep theorem**.  Statement shape: run `splitTreeA`
on `Tick.val (splitTreeD_f … (lD, xD, rD))`; payload: the three outputs
are sandwiched (`lD ⊑ lOut ⊑ Thunk (exact l)` etc.) and
`cost ≤ Tick.cost (splitTreeD_f …)`.  Try the **strengthened-payload
lockstep first** (the Item-3 discovery): the recursive demand is passed
*exactly*, so the IH may apply directly and the plan's budgeted
"largest monotonicity case matrix" may again be unnecessary.  The viewL
chain in the demand function corresponds step-for-step to forced thunks
in `viewLA`, so the witness construction follows the cascade.  Only if
the sandwich breaks (the halves are *constructed* outputs, not
projections of the input — the reconstruction may genuinely need
`optimistic_mon` + monotonicity lemmas for `mdeepA`/`viewLA`) fall back
to the `glueD'_spec` route.  Budget accordingly; checkpoint after
Pass 2 is a safe landing (helpers reusable, audit unchanged).

`split_correct` (the pure Leroy contract `¬p mzero ∧ p ‖t‖ → …`) is
mentioned in SPLIT_NOTE M9b but is NOT part of the improvement plan's
Item 4 stages; treat as optional follow-up.

## 7. Proof-engineering lessons (this session — read before resuming)

1. **`[[` and `]]` are lexer keywords** after `From Clairvoyance Require
   Import Core` (the optimistic-spec notation `u [[ r ]]`).  Every
   nested intropattern must be spaced: `as [ [a b] | ]`, `[|x [|y ws] ]`.
   This bites anywhere after line ~1037 of `FingerSplit.v`.
2. **Auto-implicit binders.**  `Set Implicit Arguments` + `Set
   Contextual Implicit` make *lemma* binders written before the colon
   implicit whenever inferable (from other binder types or the
   statement).  Consequences: apply helper lemmas by their proof
   arguments only (`deepLD_f_approx HvL Hr`, `borrowDmdL_approx Hb Ho`,
   `splitTreeD_f_cost_pot _ md dflt p i t outD Hsp` — the `_` is the
   `Exact` instance, which stays explicit because `Exact A B ≡ A → B`
   can swallow `md` if given positionally!).  Statement-quantified
   lemmas (`viewLD_f_approx` style, binders after the colon) also get
   auto-implicits — typically everything except `Reflexive` binders;
   use bare `eapply lemma; [ typeclasses eauto | …proof terms… ]`.
3. **Equation-form statements beat projection/let forms.**
   `splitTree … = (l, x, r) → P l r` proved far more robust than
   `P (fst (fst …)) (snd …)`: `destruct … eqn:` + `injection … ; subst`
   keeps both the demand side and the pure side reducing in lockstep,
   and the lemma is easier to consume downstream.
4. **`simpl never` vs `cbn` whitelists.**  `cbn [f]` does NOT override
   `Arguments f : simpl never` (tested explicitly).  Hence the file
   ordering is load-bearing: helper-level lemmas that must unfold their
   subjects live BEFORE the `simpl never` block; main theorems after.
   If a new lemma needs to unfold a never-marked constant, use
   `unfold` (unaffected by simpl flags) or move the lemma before the
   block.
5. **`cbn` eagerly unfolds Definitions applied to constructors.**
   `borrowDmdL t1 m' (Thunk out)` reduces to its match under
   `cbn in H` — after which `destruct (borrowDmdL …) eqn:` no longer
   rewrites that hypothesis.  Either invert the demand hypothesis FIRST
   (pinning `out = MMoreA …`, after which the match reduces and the
   component facts come out directly), or destruct before any cbn.
6. **Folded `exact` in inverted hypotheses.**  After
   `invert_clear Ho as [ | | vm0 prD prE mD0 mE sfD0 sfE Hpr Hm Hsf ]`,
   slot facts look like `prD ⊑ exact (One b)` (instance application,
   NOT syntactically `Thunk (OneA _)`), so `match goal` patterns on the
   unfolded form fail.  Recipe: name the inversion hypotheses via `as`,
   then `destruct prD as [dd|]; [ apply TThunkThunk_inv in Hpr;
   invert_clear Hpr | ]` — unification sees through the `exact`
   instances even when the printer keeps them folded.
7. **Never write `repeat match goal … destruct ?x …` where `?x` can
   match a constructor term** — `destruct (Thunk dd)` "succeeds"
   without progress and the loop diverges (this hung two coqc processes
   at 99% CPU; the fix was explicit per-case inversion).  Related:
   `lia` "Cannot find witness" usually means a stuck
   pattern-let/`match` atom is still in the goal — destruct the
   scrutinee, don't fight the arithmetic.
8. **Tick plumbing.**  `Tick.cost`/`Tick.val` of a folded `let+` chain
   need alternating `simpl Tick.cost` (or `cbn`) and
   `destruct (Tick.val (helper …)) eqn:` — each destruct only rewrites
   occurrences already exposed.  `let xD := match …` (simple let) zeta-
   reduces on its own; `let '(a,b,c) := …` (pattern let) does not —
   destruct its scrutinee.
9. **Hypothesis-name hygiene**: `pose proof … as H0` collides with
   auto-named instance binders (`H0 : Exact A B`); use prefixed names
   (`Hr0`, `Hr1`).
10. The `viewL_None`/`viewR_None` inversions exist (Section 10); plain
    `discriminate` does not close `viewL m = None` goals for `MMore`
    (the inner match needs destructing) — use the lemmas.

## 8. Resume checklist (next session)

1. `git -C FingerTree log --oneline -5` → expect `620b2c5` (4c
   headline), `8a031c0`, `0093a4b`, `7dfa3f7`, `daf10ee`; working tree
   clean; `make audit` green (30 theorems).
2. Stage 4d per §6, one pass at a time, committing at every pass
   boundary (Pass 2 is the safe landing).  Iterate with the
   truncated-copy trick (`head -N src/FingerSplit.v >
   src/FingerSplitT.v && coqc -Q src Clairvoyance src/FingerSplitT.v`;
   delete `src/FingerSplitT.*` afterwards).
3. New headline theorems go into `src/Audit.v` as they land.
4. Writeup sync (abstract, §3.3, §6.3.3, §7.2, §7.4, §8.2, Appendix A,
   `docs/REFERENCE.md`) only after the code stages land, per the
   improvement plan's Item-4 writing notes — the user batches this.
