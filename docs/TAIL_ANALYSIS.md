# TAIL_ANALYSIS.md — Feasibility & Design Blueprint

## Goal

Verify that `tail : Seq A → Seq A` has **O(1) amortised cost** in the bidirectional demand semantics framework, following Claessen's simplified finger tree design. Full scope — including the cascading One-front case.

## Why pen-and-paper first?

Mechanizing demand-semantics proofs is expensive. Before committing the engineering effort, we want concrete confidence that:

1. The pure operation has the right structure for a constant-cost demand function.
2. The potential function we already have (safe-convention) correctly amortises the cascade.
3. The non-recursive Triple-head case actually preserves potential under demand back-propagation.

Lorenzen 2025 (the credit-monad paper) already validated this for the persistent setting using QuickCheck-based credit passing. That's strong evidence, but it doesn't tell us whether the **demand semantics encoding** factors cleanly — that's what this analysis confirms.

## Pure `tail` in Coq

We inline `deep0` (Lorenzen's factoring) into `tail` directly. The pure function has nine effective cases:

```coq
Fixpoint tail (A : Type) (s : Seq A) : Seq A :=
  match s with
  | Nil => Nil
  | Unit _ => Nil
  | More (Three _ x y) m r => More (Two x y) m r
  | More (Two _ x) m r => More (One x) m r
  | More (One _) m r =>
      match m with
      | Nil =>
          match r with
          | One y => Unit y
          | Two y z => More (One y) Nil (One z)
          | Three y z w => More (One y) Nil (Two z w)
          end
      | _ =>
          match head m with
          | Some (Pair x y) => More (Two x y) (tail m) r       (* recurse *)
          | Some (Triple x _ _) => More (One x) (map1 chop_triple m) r
          | None => Nil  (* unreachable *)
          end
      end
  end.
```

`tail Nil = Nil` makes the function total (Claessen leaves it undefined; making it total simplifies Coq).

Termination: the recursive call `tail m` is on `m : Seq (Tuple A)`. Same polymorphic-recursion pattern as `fcons`. Coq's structural checker should accept it directly.

## Potential function recap

Under the **safe convention** (already in `Finger.v`):

- `safe_DigitA` = 0 for `One`/`Three`, 1 for `Two`.
- `safe_T` = `safe_DigitA d` if `Thunk d`, else 1 (Undefined contributes 1 by default).
- `Debitable_SeqA (MoreA fD mD rD)` = `safe_T fD + Debitable_T mD + safe_T rD`.
- `NilA`, `UnitA` have potential 0.

Intuition: a safe digit (`Two`) has potential 1 — it's "ready to absorb work" via the next operation. Dangerous digits (`One`/`Three`) have potential 0 — they will pay off once they get touched.

## Cost equation we want to prove

For all `s`, `outD`:

```
debt (Tick.val (tailD' s outD)) + Tick.cost (tailD' s outD)  ≤  K + debt outD
```

For some constant `K` (the budget). We'll show `K = 2` suffices, and the framework's full statement needs `K = 3` to cover the `outD = Undefined` case (analogous to `fconsD'_cost_bottom`).

## Case-by-case potential accounting

Below, we work out the potential transfer for each input shape of `s`, assuming `outD` is structured to match `tail s`. We compute `debt(input demand)` and check the inequality.

### Case 1: `s = Nil`

`tail Nil = Nil`. `tailD' Nil outD = bottom` (no work). Cost 0. Input demand: 0. Output demand: ≤ debt NilA = 0. **K ≥ 0.** ✓

### Case 2: `s = Unit x`

`tail (Unit x) = Nil`. `outD ≤ NilA`. Input demand back: `Thunk (UnitA Undefined)` (forced UnitA's constructor, didn't peek at `x`). Cost: 1 (top tick).

- Potential input: `Debitable_SeqA (UnitA Undefined) = 0`.
- Potential output: 0.
- `0 + 1 ≤ K + 0` → **K ≥ 1**.

### Case 3: `s = More (Three _ x y) m r`

`tail s = More (Two x y) m r`. Output: `MoreA (Thunk (TwoA xD yD)) mD' rD'`. Input demand back: `Thunk (MoreA (Thunk (ThreeA Undefined xD yD)) mD' rD')`. Cost: 1.

- Potential input: `safe_T (Thunk ThreeA) + debt mD' + safe_T rD' = 0 + debt mD' + safe_T rD'`.
- Potential output: `safe_T (Thunk TwoA) + debt mD' + safe_T rD' = 1 + debt mD' + safe_T rD'`.
- Diff (input − output) = −1.
- `(debt mD' + safe_T rD') + 1 ≤ K + (1 + debt mD' + safe_T rD')` → **K ≥ 0**. ✓

The Three → Two transition **gains** potential on the output side, paying for the cost.

### Case 4: `s = More (Two _ x) m r`

`tail s = More (One x) m r`. Output: `MoreA (Thunk (OneA xD)) mD' rD'`. Input demand back: `Thunk (MoreA (Thunk (TwoA Undefined xD)) mD' rD')`. Cost: 1.

- Potential input: `1 + debt mD' + safe_T rD'`.
- Potential output: `0 + debt mD' + safe_T rD'`.
- `(1 + debt mD' + safe_T rD') + 1 ≤ K + (debt mD' + safe_T rD')` → **K ≥ 2**.

The Two → One transition **loses** potential — but we extract that credit to pay for the cost. **This is the tightest non-recursive case.**

### Case 5: `s = More (One _) m r` — the cascade

#### 5a: `m = Nil`, `r = One y`

`tail s = Unit y`. Input demand: `Thunk (MoreA (Thunk (OneA Undefined)) (Thunk NilA) (Thunk (OneA yD)))`. Output: `Thunk (UnitA yD)`. Cost: 1.

- Potential input: `0 + 0 + 0 = 0` (all One digits, NilA spine).
- Potential output: 0.
- `0 + 1 ≤ K + 0` → **K ≥ 1**. ✓

#### 5b: `m = Nil`, `r = Two y z`

`tail s = More (One y) Nil (One z)`. Input: `Thunk (MoreA (Thunk (OneA Undefined)) (Thunk NilA) (Thunk (TwoA yD zD)))`. Output: `Thunk (MoreA (Thunk (OneA yD)) (Thunk NilA) (Thunk (OneA zD)))`. Cost: 1.

- Potential input: `0 + 0 + 1 = 1`.
- Potential output: `0 + 0 + 0 = 0`.
- `1 + 1 ≤ K + 0` → **K ≥ 2**.

#### 5c: `m = Nil`, `r = Three y z w`

`tail s = More (One y) Nil (Two z w)`. Input: `Thunk (MoreA (Thunk (OneA Undefined)) (Thunk NilA) (Thunk (ThreeA yD zD wD)))`. Output: `Thunk (MoreA (Thunk (OneA yD)) (Thunk NilA) (Thunk (TwoA zD wD)))`. Cost: 1.

- Potential input: `0 + 0 + 0 = 0`.
- Potential output: `0 + 0 + 1 = 1`.
- `0 + 1 ≤ K + 1` → **K ≥ 0**. ✓

The Three → Two transition on the rear gains potential, paying for the operation.

#### 5d: `m` non-empty, `head m = Pair x y` — **the recursive case**

`tail s = More (Two x y) (tail m) r`. Output: `outD = MoreA (Thunk (TwoA xD yD)) mD_out rD_out`.

Input demand back:
- Front: `Thunk (OneA Undefined)` (forced constructor only; the popped element is discarded).
- Spine: result of `tailD' m (force mD_out)`, augmented at the head with `Thunk (PairA xD yD)`. Call this `mD_in`.
- Rear: `rD_out`.
- So input: `Thunk (MoreA (Thunk (OneA Undefined)) mD_in rD_out)`.

Cost: `1 (top tick) + cost(tailD' m (force mD_out))` = `1 + cost_rec`.

- Potential input: `0 + debt mD_in + safe_T rD_out`.
- Potential output: `1 + debt mD_out + safe_T rD_out`.

The desired inequality:
```
(debt mD_in + safe_T rD_out) + (1 + cost_rec)  ≤  K + (1 + debt mD_out + safe_T rD_out)
```
Cancel:
```
debt mD_in + cost_rec  ≤  K + debt mD_out
```

**This is exactly the IH at one level deeper.** ✓ Transparent recursion.

#### 5e: `m` non-empty, `head m = Triple x _ _` — **the non-recursive case**

`tail s = More (One x) (map1 chop_triple m) r`. Output: `outD = MoreA (Thunk (OneA xD)) mD_out rD_out`.

`mD_out` is a demand on `map1 chop_triple m`. The chop replaced the head `Triple x y z` with `Pair y z`. To get the demand back on `m`, we need to **invert chop**:

- The head element in `m` is `Triple x y z`.
- In `mD_out`, the head element's demand might be `Thunk (PairA yD zD)` (if Pair-head was demanded) or `Undefined`.
- To reconstruct `m`'s demand: replace the head element with `Thunk (TripleA xD yD' zD')` where `yD', zD'` come from `mD_out`'s Pair-head if present, else `Undefined`.

Call this transformation `inverse_chop_demand mD_out xD`. The structural shape (outer constructors, spine depth, digit constructors) of `mD_out` is preserved — only the head element type changes from PairA to TripleA.

Input demand back:
- Front: `Thunk (OneA Undefined)`.
- Spine: `inverse_chop_demand mD_out xD`.
- Rear: `rD_out`.

Cost: 1 (top tick, no recursion).

**Key observation**: The potential of `inverse_chop_demand mD_out xD` equals the potential of `mD_out`. The reason: `safe_T` and `Debitable_T` only inspect **digit constructors** and the **outer `T` of the spine**, not the head element's type (Pair vs Triple). Specifically, `safe_DigitA` is constructor-driven (`OneA`/`TwoA`/`ThreeA`) and doesn't look inside the `T A` fields. `Debitable_T` is a one-level match on `T`. So changing `PairA` ↔ `TripleA` deep inside is invisible to the potential calculation.

**Lemma (potential preservation under chop inverse):**
```
debt (inverse_chop_demand mD xD) = debt mD
```

Given this:
- Potential input: `0 + debt mD_out + safe_T rD_out`.
- Potential output: `0 + debt mD_out + safe_T rD_out`.
- `(debt mD_out + safe_T rD_out) + 1 ≤ K + (debt mD_out + safe_T rD_out)` → **K ≥ 1**. ✓

The Triple-head case is free (cost 1, no potential transfer) thanks to the chop trick.

## Summary table

| Case | Need K ≥ |
|---|---|
| 1: Nil | 0 |
| 2: Unit | 1 |
| 3: Three-front | 0 |
| 4: Two-front | **2** |
| 5a: One-front, m=Nil, r=One | 1 |
| 5b: One-front, m=Nil, r=Two | **2** |
| 5c: One-front, m=Nil, r=Three | 0 |
| 5d: One-front, Pair-head, recursive | K (transparent via IH) |
| 5e: One-front, Triple-head | 1 |

**Max: K = 2.** Tightness binds in the Two-front non-recursive case and the One-Nil-Two case.

## The `outD = Undefined` case (framework requirement)

For `physicist's_argumentD`, the demand instance computes `tailD' s (forceD (bottom_of (exact (tail s))) outD)`. When `outD = Undefined`, this uses `bottom_of (exact (tail s))` as the default — a structurally-bottom `SeqA A`.

For `s = More (Two _ _) m r`, `tail s = More (One _) m r`, and `bottom_of (exact (More (One _) m r)) = MoreA Undefined Undefined Undefined`. Running `tailD'` on this gives an input demand of `Thunk (MoreA (Thunk (TwoA Undefined Undefined)) Undefined Undefined)`. Its potential: `1 + 0 + 1 = 2`. Plus cost 1 = 3. With `potential Undefined = 0` on the output side, **K = 3** is needed.

This matches FCons's analysis — same +1 from the Undefined rear digit's default of 1.

## Conclusion: K = 3 (budget = 3)

`tail` fits in the existing budget framework with budget 3, same as `Empty`, `FCons`, `Head`. The analysis confirms full O(1) amortised cost in the persistent setting.

This is consistent with Lorenzen's credit-monad analysis (cost 2 per `tail`, after splitting credits between the top thunk and the spine). The +1 in our K = 3 vs Lorenzen's 2 is from the framework's `Undefined`-default-of-1 convention, not a real cost difference.

## Implementation blueprint

### Phase A: pure definitions (1 day)

1. Define `tail` in Coq exactly as above. Verify with `Compute` on the worked examples in `CLAESSEN_REFERENCE.md`.
2. Define `chop_triple`. Confirm `map1` is already in `Finger.v`; if not, add it.
3. Add small sanity lemmas: `tail_Nil = Nil`, `tail (Unit x) = Nil`, etc.

### Phase B: induction principle (1 day)

Define `tail_ind`:

```coq
Lemma tail_ind :
  forall (P : forall A, Seq A -> Seq A -> Prop),
    (forall A, P A Nil Nil) ->
    (forall A x, P A (Unit x) Nil) ->
    (forall A a x y m r, P A (More (Three a x y) m r) (More (Two x y) m r)) ->
    (forall A a x m r, P A (More (Two a x) m r) (More (One x) m r)) ->
    (forall A a y, P A (More (One a) Nil (One y)) (Unit y)) ->
    (forall A a y z, P A (More (One a) Nil (Two y z))
                           (More (One y) Nil (One z))) ->
    (forall A a y z w, P A (More (One a) Nil (Three y z w))
                            (More (One y) Nil (Two z w))) ->
    (forall A a x y m r,
        P (Tuple A) m (tail m) ->
        head m = Some (Pair x y) ->
        P A (More (One a) m r) (More (Two x y) (tail m) r)) ->
    (forall A a x y z m r,
        head m = Some (Triple x y z) ->
        P A (More (One a) m r) (More (One x) (map1 chop_triple m) r)) ->
    forall A s, P A s (tail s).
```

Proof: `fix SELF 2; destruct s` then dispatch each constructor case. The Pair-head case applies `SELF` recursively to `m` at type `Tuple A`. Mirrors `fcons_ind`'s structure.

### Phase C: clairvoyant tail (1 day)

```coq
Fixpoint tailA' (A : Type) (s : SeqA A) : M (SeqA A) :=
  tick >>
  match s with
  | NilA => ret NilA
  | UnitA _ => ret NilA
  | MoreA fD mD rD =>
      forcing fD (fun f =>
        match f with
        | ThreeA _ xD yD => ret (MoreA (Thunk (TwoA xD yD)) mD rD)
        | TwoA _ xD => ret (MoreA (Thunk (OneA xD)) mD rD)
        | OneA _ =>
            forcing mD (fun m =>
              match m with
              | NilA =>
                  forcing rD (fun r =>
                    match r with
                    | OneA yD => ret (UnitA yD)
                    | TwoA yD zD => ret (MoreA (Thunk (OneA yD))
                                                 (Thunk NilA)
                                                 (Thunk (OneA zD)))
                    | ThreeA yD zD wD => ret (MoreA (Thunk (OneA yD))
                                                       (Thunk NilA)
                                                       (Thunk (TwoA zD wD)))
                    end)
              | UnitA t =>
                  forcing t (fun tup =>
                    match tup with
                    | PairA xD yD => ret (MoreA (Thunk (TwoA xD yD))
                                                  (Thunk NilA)
                                                  rD)
                    | TripleA xD yD zD =>
                        ret (MoreA (Thunk (OneA xD))
                                    (Thunk (UnitA (Thunk (PairA yD zD))))
                                    rD)
                    end)
              | MoreA fD_m mD_m rD_m =>
                  forcing fD_m (fun fm =>
                    match fm with
                    | OneA t =>
                        forcing t (fun tup =>
                          match tup with
                          | PairA xD yD =>
                              let~ rec := tailA' (MoreA fD_m mD_m rD_m) in
                              ret (MoreA (Thunk (TwoA xD yD)) rec rD)
                          | TripleA xD yD zD =>
                              ret (MoreA (Thunk (OneA xD))
                                          (Thunk (MoreA (Thunk (OneA (Thunk (PairA yD zD))))
                                                          mD_m rD_m))
                                          rD)
                          end)
                    | TwoA t _ => (* analogous *)
                    | ThreeA t _ _ => (* analogous *)
                    end)
              end)
        end)
  end.

Definition tailA (A : Type) (q : T (SeqA A)) : M (SeqA A) :=
  forcing q tailA'.

Lemma tailA_mon ... (* mirror fconsA_mon's structure *)
```

Note: this is getting nested. We may want a helper `tailA_cascade : SeqA (TupleA A) -> DigitA A -> M (SeqA A)` for the One-front case — keep this as a top-level definition to avoid massive nesting. Cleaner alternative: define `deep0A` (over a `SeqA (TupleA A)` and `DigitA A`), even though we said no `deep0` at the pure level — at the clairvoyant level, having it as a helper keeps `tailA'` short.

### Phase D: demand function (2 days)

The hardest part. Two helpers needed:

```coq
Definition add_pair_to_head_demand {A B} `{Exact A B}
    (mD : T (SeqA (TupleA B))) (xD yD : T B) : T (SeqA (TupleA B)).

Definition inverse_chop_demand {A B} `{Exact A B}
    (mD : T (SeqA (TupleA B))) (xD : T B) : T (SeqA (TupleA B)).
```

Both walk the outer structure of `mD` once and rewrite the head Pair/Triple. Small inductive case-splits.

Then `tailD'` follows the case structure of `tail` with the demand-back logic per case. Inline the One-front cascade rather than factoring through `deep0D'` to match the pure-level inlining.

Small lemmas needed:
- `debt (inverse_chop_demand mD xD) = debt mD` (potential preservation).
- `debt (add_pair_to_head_demand mD xD yD) ≤ debt mD + 0` (no potential increase).

### Phase E: big proofs (2–3 days)

- `tailD'_approx`: routine, mirror `fconsD'_approx`. Use `tail_ind`.
- `tailD'_spec`: clairvoyance equivalence. Mirror `fconsD'_spec`'s structure case-by-case. The cascading case applies the IH from `tail_ind`.
- `tailD'_cost`: the meat. Each case's arithmetic should match this analysis document. The recursive case applies the IH directly. The Triple-head case uses the `debt (inverse_chop_demand _ _) = debt _` lemma.

### Phase F: extend the operation algebra (1 day)

Update `op = Empty | FCons A | Head | Tail`. Update:
- `eval` (add `Tail [q] = [tail q]`).
- `exec` (add `Tail [qD] = let! _ := tailA qD in ret []` or with output if we keep the result).
- `demand` (add `Tail [q] [outD] = let+ qD := tailD q (forceD ...) in Tick.ret [qD]`).
- `wf_eval`, `monotonic_exec`, `pd`, `cd`, `physicist's_argumentD` — extend each with the `Tail` case.
- `budget Tail = 3`.

The `physicist's_argumentD` Tail case will likely need the same `outD = Thunk outA` / `outD = Undefined` split as FCons, since the safe-convention budget of 3 handles the Undefined case via the same `forceD` mechanism.

## Risk register

- **`tail_ind` may need `head m = Some _` as a side condition** in the Pair/Triple cases, complicating the recursion. Mitigation: state `tail_ind` carefully; if it doesn't work, fall back to direct `fix SELF` proofs without an induction principle.
- **Nested `forcing`s in `tailA'`** could make `tailA_mon` painful. Mitigation: factor `tailA_cascade` (or `deep0A` at the clairvoyant level) as a helper.
- **`inverse_chop_demand`'s structure may interact badly with `mgo_`** in spec proofs. Mitigation: prove it preserves `is_approx` separately, use as a black-box rewrite.
- **Time**: 7–8 days is the optimistic estimate. With slack for unknowns, plan for 10 days. If overrunning by mid-week, drop to reduced scope (Cases 1–4 + Case 5a only) and document the rest as future work.

## What does success look like?

After Phase F:

```
Theorem amortized_cost : ∀ trace, well_formed trace →
  cost (exec trace) ≤ 3 * length trace.
```

with `trace` allowed to include `Tail` operations. This is the headline thesis result: O(1) amortised cost for `cons` and `tail` on Claessen's simplified finger tree, mechanically verified in Coq using bidirectional demand semantics. Symmetric `snoc`/`init` follow by inspection of the (symmetric) code structure; this is documented in the thesis without re-verification.
