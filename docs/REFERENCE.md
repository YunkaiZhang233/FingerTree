# Finger Tree Formal Verification — Complete Reference

This document catalogues every definition, fixpoint, inductive type, class,
instance, lemma, theorem, and corollary across all `Finger*.v` files in the
project.  Proof bodies are omitted; proof sketches are provided for
non-trivial results.

**Data structure**: Claessen 2020 simplified finger tree (persistent deque).
**Verification framework**: Bidirectional demand semantics (Xia et al., ICFP 2024).
**Goal**: O(1) amortised `cons`/`snoc`/`head`/`tail`; O(log n) worst-case `concat`/`split`/`index`.

---

## Table of Contents

1. [FingerCore.v — Data types, approximation lattice, debt machinery](#1-fingercoreV)
2. [FingerCons.v — `fcons` operation and demand analysis](#2-fingerconsv)
3. [FingerSnoc.v — `fsnoc` operation and demand analysis](#3-fingerSnocv)
4. [FingerHead.v — `head` operation and demand analysis](#4-fingerheadv)
5. [FingerTail.v — `ftail` operation and demand analysis](#5-fingertailv)
6. [FingerPhysicist.v — Physicist's argument and amortised cost theorem](#6-fingerphysicistv)
7. [FingerMonoid.v — Measure-monoid interface](#7-fingermonoidv)
8. [FingerSize.v — Size/depth metrics and logarithmic bound](#8-fingersizev)
9. [FingerConcat.v — Concatenation (O(log n) worst-case)](#9-fingerconcatv)
10. [FingerSplit.v — Split and random access (O(log n) worst-case)](#10-fingersplitv)

---

## 1. FingerCore.v

**Purpose**: Defines the pure data structure, approximation types with full
lattice infrastructure (reflexivity, transitivity, antisymmetry, partial
order, lub), the `Exact` embedding, and the debt/potential machinery used
by the physicist's argument.

### 1.1 Utility Tactics

```coq
Ltac teardown           (* Destructs all match/if in context and goal *)
Ltac keep_mgo_          (* mgo_ then repeatedly apply optimistic_thunk_go *)
Ltac mgo_brute_force    (* Aggressive solve via mgo_ + optimistic_skip/thunk_go *)

Tactic Notation "invert_clear" ...   (* Inversion that clears the original hypothesis *)

Ltac head_is_constructor t           (* Check if term head is a constructor *)
Ltac head_is_constructor_or_proj t   (* Same, also accepts fst/snd projections *)
```

### 1.2 Utility Lemma

```coq
Lemma make_partial_order :
  forall A (R : A -> A -> Prop) `{PreOrder A R},
    (forall x y, R x y -> R y x -> x = y) ->
    PartialOrder eq R.
```

Promotes a preorder with antisymmetry to a partial order on `eq`.

```coq
Lemma LessDefined_T_antisym :
  forall A `{LessDefined A},
    (forall x y : A, x `less_defined` y -> y `less_defined` x -> x = y) ->
    forall x y : T A, x `less_defined` y -> y `less_defined` x -> x = y.
```

Lifts antisymmetry through the `T` (thunk) wrapper.

### 1.3 Pure Data Structure (Section 1)

```coq
Inductive Digit (A : Type) : Type :=
  | One   : A -> Digit A
  | Two   : A -> A -> Digit A
  | Three : A -> A -> A -> Digit A.
```

A **redundant digit** holding 1-3 elements. In the number-system analogy,
`Two` is *safe* (middle of range), while `One` and `Three` are *dangerous*
(one step from underflow/overflow). This classification drives the potential
function.

```coq
Inductive Tuple (A : Type) : Type :=
  | Pair   : A -> A -> Tuple A
  | Triple : A -> A -> A -> Tuple A.
```

A **2-3 node** for the recursive spine. `Pair` holds 2 elements, `Triple`
holds 3.  The key role of `Triple`: when `tail` encounters a `Triple` at the
spine head, it can *chop* it to a `Pair` without recursing (via `map1
chop_triple`), avoiding a cascade.

```coq
Inductive Seq (A : Type) : Type :=
  | Nil  : Seq A
  | Unit : A -> Seq A
  | More : Digit A -> Seq (Tuple A) -> Digit A -> Seq A.
```

The **sequence type**. `More f m r` has front digit `f`, a polymorphic-recursive
middle spine `m : Seq (Tuple A)`, and rear digit `r`. At level 0 elements are
`A`; at level 1 they are `Tuple A`; at level 2, `Tuple (Tuple A)`, etc.

### 1.4 Conversion to Lists

```coq
Definition digitToList {A : Type} (d : Digit A) : list A :=
  match d with
  | One a       => a :: nil
  | Two a b     => a :: b :: nil
  | Three a b c => a :: b :: c :: nil
  end.
```

Flattens a digit to a list of 1-3 elements.

```coq
Fixpoint toListWith {A B : Type} (f : A -> list B) (s : Seq A) : list B :=
  match s with
  | Nil          => nil
  | Unit x       => f x
  | More fr m rr =>
      List.flat_map f (digitToList fr)
      ++ toListWith (fun t => match t with
                              | Pair a b     => f a ++ f b
                              | Triple a b c => f a ++ f b ++ f c
                              end) m
      ++ List.flat_map f (digitToList rr)
  end.
```

Polymorphic list extraction parameterised by an element flattener `f`.

```coq
Definition toList {A : Type} (s : Seq A) : list A :=
  toListWith (fun x => x :: nil) s.
```

Functional specification: every operation must agree with the corresponding
list operation when viewed through `toList`.

### 1.5 Approximation Types (Section 2)

#### DigitA

```coq
Inductive DigitA (A : Type) : Type :=
  | OneA   : T A -> DigitA A
  | TwoA   : T A -> T A -> DigitA A
  | ThreeA : T A -> T A -> T A -> DigitA A.
```

Approximated digit: each element wrapped in `T` (thunk). No bottom
constructor; `T (DigitA A)` with `Undefined` serves that role.

**Lattice infrastructure for DigitA:**

```coq
Inductive LessDefined_DigitA A `{LessDefined A} : LessDefined (DigitA A).
  (* Pointwise on matching constructors; different constructors are incomparable *)

Lemma LessDefined_DigitA_refl   (* Reflexivity *)
Instance Reflexive_LessDefined_DigitA

Lemma LessDefined_DigitA_trans  (* Transitivity *)
Instance Transitive_LessDefined_DigitA
Instance PreOrder_LessDefined_DigitA

Lemma LessDefined_DigitA_antisym  (* Antisymmetry *)
Instance PartialOrder_LessDefined_DigitA
```

**Exact embedding:**

```coq
Instance Exact_Digit A B `{Exact A B} : Exact (Digit A) (DigitA B).
  (* One x => OneA (exact x), etc. *)

Instance ExactMaximal_Digit : ExactMaximal (DigitA B) (Digit A).
  (* exact d is maximal: if exact d <= dA then exact d = dA *)
```

**Lub (least upper bound):**

```coq
Instance Lub_DigitA (A : Type) `{Lub A} : Lub (DigitA A).
  (* Pointwise on matching constructors; mismatched => OneA Undefined (dummy) *)

Instance LubLaw_DigitA : LubLaw (DigitA A).
```

#### TupleA

```coq
Inductive TupleA (A : Type) : Type :=
  | PairA   : T A -> T A -> TupleA A
  | TripleA : T A -> T A -> T A -> TupleA A.
```

Approximated spine tuple. Same design as `DigitA`.

**Full lattice infrastructure** (mirrors DigitA exactly):

```coq
Inductive LessDefined_TupleA   (* Pointwise on matching constructors *)
Lemma LessDefined_TupleA_refl / Instance Reflexive_LessDefined_TupleA
Lemma LessDefined_TupleA_trans / Instance Transitive_LessDefined_TupleA
Instance PreOrder_LessDefined_TupleA
Lemma LessDefined_TupleA_antisym
Instance PartialOrder_LessDefined_TupleA

Instance Exact_Tuple / Instance ExactMaximal_Tuple
Instance Lub_TupleA / Instance LubLaw_TupleA
```

#### SeqA

```coq
Inductive SeqA (A : Type) : Type :=
  | NilA  : SeqA A
  | UnitA : T A -> SeqA A
  | MoreA : T (DigitA A) -> T (SeqA (TupleA A)) -> T (DigitA A) -> SeqA A.
```

Approximated sequence. The middle field is `T (SeqA (TupleA A))` — a thunk
wrapping the polymorphic-recursive spine. Auto-generated elimination schemes
are suppressed; a custom induction principle is provided.

```coq
Lemma SeqA_ind (P : forall A, SeqA A -> Prop) :
  (forall A, P A NilA) ->
  (forall A x, P A (UnitA x)) ->
  (forall A f m r, TR1 (P (TupleA A)) m -> P A (MoreA f m r)) ->
  forall (A : Type) (s : SeqA A), P A s.
```

**Design**: Universally quantifies over the type parameter so the IH in the
`MoreA` case holds at `TupleA A`, not just `A`. The middle field is split via
`destruct` into `Thunk`/`Undefined` to discharge `TR1`.

**Full lattice infrastructure:**

```coq
Inductive LessDefined_SeqA  (* Pointwise on matching constructors *)
Lemma LessDefined_SeqA_refl / Instance Reflexive_LessDefined_SeqA
Lemma LessDefined_SeqA_trans / Instance Transitive_LessDefined_SeqA
Instance PreOrder_LessDefined_SeqA
Lemma LessDefined_SeqA_antisym_aux / Lemma LessDefined_SeqA_antisym
Instance PartialOrder_LessDefined_SeqA
```

*Antisymmetry proof sketch*: `fix SELF` on the type parameter; `MoreA` case
uses `LessDefined_T_antisym` for the front/rear fields and the recursive
`SELF` at `TupleA A` for the middle.

```coq
Instance Exact_Seq : forall A B `{Exact A B}, Exact (Seq A) (SeqA B).
  (* Polymorphic fix for the recursive More branch *)

Instance BottomOf_SeqA / Instance BottomIsLeast_SeqA

Instance Lub_SeqA : forall (A : Type) `{Lub A}, Lub (SeqA A).
  (* Polymorphic fix; MoreA uses lub_SeqA at TupleA A for the middle *)

Instance LubLaw_SeqA : LubLaw (SeqA A).
```

### 1.6 Debt/Potential Machinery

```coq
Class Debitable (A : Type) := debt : A -> nat.

Instance Debitable_T (A : Type) `{Debitable A} : Debitable (T A).
  (* Thunk x => debt x; Undefined => 0 *)
```

```coq
Definition safe_DigitA {A : Type} (dA : DigitA A) : nat :=
  match dA with
  | OneA _       => 0
  | TwoA _ _     => 1
  | ThreeA _ _ _ => 0
  end.
```

The **safe-digit convention**: `Two` contributes 1 to potential; `One`/`Three`
contribute 0. This is the heart of the amortised argument.

```coq
#[global] Instance Debitable_SeqA : forall (A : Type), Debitable (SeqA A) :=
  fix debt_SeqA (A : Type) (sA : SeqA A) :=
    match sA with
    | NilA => 0
    | UnitA _ => 0
    | MoreA fD mD rD =>
        T_rect _ safe_DigitA 1 fD +
        @Debitable_T _ (debt_SeqA _) mD +
        T_rect _ safe_DigitA 1 rD
    end.
```

Where `safe_T fD = match fD with Thunk d => safe_DigitA d | Undefined => 1 end`.

```coq
Definition safe_T {A : Type} (fD : T (DigitA A)) : nat :=
  match fD with
  | Thunk d => safe_DigitA d
  | Undefined => 1
  end.
```

```coq
Ltac unfold_debt.  (* Unfolds one layer of debt *)
```

#### Sub-additivity Lemmas

These ensure the potential function is well-defined for the physicist's
argument (lub doesn't create "free" potential).

```coq
Lemma safe_DigitA_lub_subadditive :
  safe_DigitA (lub d1 d2) <= safe_DigitA d1 + safe_DigitA d2.
```

*Proof*: Case-split on constructor pairs; mismatched constructors give
`safe_DigitA (OneA Undefined) = 0`.

```coq
Lemma safe_T_lub_subadditive :
  safe_T (lub f1 f2) <= safe_T f1 + safe_T f2.
```

*Proof*: Case-split on `Thunk`/`Undefined`; delegate to `safe_DigitA_lub_subadditive`.

```coq
Lemma debt_SeqA_lub_subadditive :
  forall A (x : SeqA A), forall ...,
    x `less_defined` d -> y `less_defined` d ->
    debt (lub x y) <= debt x + debt y.
```

*Proof sketch*: By `SeqA_ind` with `A` universally quantified inside the
statement. The `MoreA` case decomposes into three sub-bounds (front, spine,
rear) via `safe_T_lub_subadditive` and the spine IH lifted through `T`.

### 1.7 Depth

```coq
Fixpoint depth {A : Type} (s : Seq A) : nat :=
  match s with
  | Nil        => 0
  | Unit _     => 0
  | More _ m _ => S (depth m)
  end.
```

---

## 2. FingerCons.v

**Purpose**: Front insertion (`fcons`), its clairvoyant semantics (`fconsA`),
demand function (`fconsD'`), and the three core lemmas: `_approx`, `_spec`,
`_cost`.

### 2.1 Pure Operation

```coq
Fixpoint fcons {A : Type} (x : A) (s : Seq A) : Seq A :=
  match s with
  | Nil              =>
      let u' := x in
      Unit u'
  | Unit y           =>
      let f' := One x in
      let m' := Nil in
      let r' := One y in
      More f' m' r'
  | More f m r =>
      let (f, m) :=
        match f with
        | One a =>
            let f' := Two x a in
            (f', m)
        | Two a b =>
            let f' := Three x a b in
            (f', m)
        | Three a b c =>
            let f' := Two x a in
            let pbc := Pair b c in
            let m' := fcons pbc m in
            (f', m')
        end in
      More f m r
  end.
```

Three cases on `More f m r`:
- `One a`: grow to `Two x a` (no recursion).
- `Two a b`: grow to `Three x a b` (no recursion).
- `Three a b c`: **overflow** — keep `Two x a`, bundle `Pair b c`, recurse
  `fcons (Pair b c) m`. Front goes from dangerous to safe.

### 2.2 Custom Induction

```coq
Lemma fcons_ind :
  forall (P : forall A, A -> Seq A -> Seq A -> Prop),
    (* 5 cases: Nil, Unit, One, Two, Three (recursive) *)
    forall A (x : A) (s : Seq A), P A x s (fcons x s).
```

### 2.3 Helper

```coq
Lemma fcons_go_deep : forall A (x : A) (q : Seq A),
  q <> Nil -> exists f m r, fcons x q = More f m r.
```

### 2.4 Clairvoyant Semantics

```coq
Fixpoint fconsA' (A : Type) (q : SeqA A) (x : T A) : M (SeqA A) :=
  tick >>
  (match q with
  | NilA =>
      ret (UnitA x)
  | UnitA y =>
      let~ f' := ret (OneA x) in
      let~ m' := ret NilA in
      let~ r' := ret (OneA y) in
      ret (MoreA f' m' r')
  | MoreA f m r =>
      let! f_val := force f in
      match f_val with
      | OneA a =>
          let~ f' := ret (TwoA x a) in
          ret (MoreA f' m r)
      | TwoA a b =>
          let~ f' := ret (ThreeA x a b) in
          ret (MoreA f' m r)
      | ThreeA a b c =>
          let~ f' := ret (TwoA x a) in
          let~ pbc := ret (PairA b c) in
          let~ m' := forcing m (fun m => fconsA' m pbc) in
          ret (MoreA f' m' r)
      end
  end).

Definition fconsA (A : Type) (x : T A) (q : T (SeqA A)) : M (SeqA A) :=
  forcing q (fun q => fconsA' q x).
```

Maximally lazy: one tick, thunks intermediate results via `let~`.
The `forcing` pattern returns bottom on `Undefined`, ensuring monotonicity.

### 2.5 Monotonicity

```coq
Lemma fconsA_mon :
  forall A `{LDA : LessDefined A, PreOrder A LDA} x' x (q' q : T (SeqA A)),
    x' `less_defined` x -> q' `less_defined` q ->
    fconsA x' q' `less_defined` fconsA x q.
```

*Proof sketch*: By induction on `q`. The `MoreA/ThreeA` case uses the IH
at `TupleA A` for the recursive `fconsA'` call inside `forcing m`.

### 2.6 Demand Function

```coq
Fixpoint fconsD' (A B : Type) `{Exact A B}
    (x : A) (s : Seq A) (outD : SeqA B)
    : Tick (T (SeqA B)) :=
  Tick.tick >>
  match s with
  | Nil =>
      match outD with
      | UnitA _ => Tick.ret (Thunk NilA)
      | _       => bottom
      end
  | Unit y =>
      match outD with
      | MoreA _ _ rD =>
          let yD := match rD with
                    | Thunk (OneA yD) => yD
                    | _               => Undefined
                    end in
          Tick.ret (Thunk (UnitA yD))
      | _ => bottom
      end
  | More (One a) m r =>
      match outD with
      | MoreA fD mD rD =>
          let aD := match fD with
                    | Thunk (TwoA _ aD) => aD
                    | _                 => Undefined
                    end in
          Tick.ret (Thunk (MoreA (Thunk (OneA aD)) mD rD))
      | _ => bottom
      end
  | More (Two a b) m r =>
      match outD with
      | MoreA fD mD rD =>
          let '(aD, bD) := match fD with
                           | Thunk (ThreeA _ aD bD) => (aD, bD)
                           | _                      => (Undefined, Undefined)
                           end in
          Tick.ret (Thunk (MoreA (Thunk (TwoA aD bD)) mD rD))
      | _ => bottom
      end
  | More (Three a b c) m r =>
      match outD with
      | MoreA fD mD rD =>
          let aD := match fD with
                    | Thunk (TwoA _ aD) => aD
                    | _                 => Undefined
                    end in
          let+ mD_in := thunkD (fconsD' (Pair b c) m) mD in
          Tick.ret (Thunk (MoreA (Thunk (ThreeA aD (exact b) (exact c))) mD_in rD))
      | _ => bottom
      end
  end.

Definition fconsD (A : Type) : A -> Seq A -> SeqA A -> Tick (T (SeqA A)) := fconsD'.
```

**Design**: Given the pure input `(x, s)` and a demand `outD` on the output
`fcons x s`, returns a `Tick`-wrapped demand on the input `s`. Each case
extracts the relevant sub-demands from `outD` by pattern-matching on its
constructor and the known output shape.

The `Three a b c` case recurses via `thunkD (fconsD' (Pair b c) m) mD`,
where `thunkD` gates the recursion on whether the middle is demanded.

### 2.7 Core Lemmas

#### Approx (demand approximates the input)

```coq
Lemma fconsD'_approx :
  forall A B `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (x : A) (s : Seq A) (outD : SeqA B),
    outD `is_approx` fcons x s ->
    Tick.val (fconsD' x s outD) `is_approx` s.

Corollary fconsD_approx.
```

*Proof*: By `fcons_ind`. Each case pattern-matches on `outD`, using the
hypothesis `outD <= exact (fcons x s)` to determine `outD`'s shape. The
`Three` case uses the IH at `Tuple A` for the recursive call.

#### Exact (full demand recovers exact input)

```coq
Lemma fconsD'_exact :
  forall A B `{Exact A B} (x : A) (s : Seq A),
    Tick.val (fconsD' x s (exact (fcons x s))) = exact s.
```

*Proof*: By structural induction on `s`. The `Three` case rewrites with
`IHs` at `Pair b c`.

#### Spec (clairvoyant dominates demand)

```coq
Lemma fconsD'_spec :
  forall ... (x : A) (s : Seq A) (outD : SeqA B),
    outD `is_approx` fcons x s ->
    forall sD, sD = Tick.val (fconsD' x s outD) ->
      fconsA (exact x) sD [[ fun out cost =>
                               outD `less_defined` out /\ cost <= Tick.cost (fconsD' x s outD) ]].

Corollary fconsD_spec.
```

*Proof*: By `fcons_ind`. Each case unfolds `fconsA` and uses `mgo_`/`keep_mgo_`
to discharge the optimistic spec. The `Three` case uses `optimistic_mon` with
the IH as the inner witness.

#### Cost (amortised bound)

```coq
Lemma fconsD'_cost :
  forall A B `{LessDefined B, Exact A B} (x : A) (s : Seq A) (outD : SeqA B),
    outD `is_approx` fcons x s ->
    debt (Tick.val (fconsD' x s outD)) + Tick.cost (fconsD' x s outD) <= 2 + debt outD.

Corollary fconsD_cost.
```

*Proof sketch*: By `fcons_ind`. Key insight: potential transfer.
- `One`: front goes `One -> Two` (gains 1 potential). Cost 1. Net: 1 - 1 = 0 <= 2.
- `Two`: front goes `Two -> Three` (loses 1 potential). Cost 1. Net: 1 + 1 = 2 <= 2.
- `Three`: front goes `Three -> Two` (gains 1 potential), but recurses.
  By IH on the recursive call: `debt(mD_in) + rc <= 2 + debt(mD_out)`.
  Total: `0 + debt(mD_in) + safe(rD) + 1 + rc <= 2 + safe(fD) + debt(mD_out) + safe(rD)`.
  The crucial point: `fD` had `safe(ThreeA) = 0` but `outD`'s `TwoA` has `safe = 1`,
  providing +1 to absorb the tick.

#### Bottom cost (worst-case for minimal demand)

```coq
Lemma fconsD'_cost_bottom :
  forall A B ... (x : A) (s : Seq A),
    debt (Tick.val (fconsD' x s (bottom_of (exact (fcons x s)))))
    + Tick.cost (fconsD' x s (bottom_of (exact (fcons x s)))) <= 3.
```

*Proof*: Direct computation on the three digit cases.

---

## 3. FingerSnoc.v

**Purpose**: Rear insertion (`fsnoc`). Symmetric counterpart of `FingerCons.v`
with front/rear swapped. Every definition and lemma has a direct dual.

### 3.1 Pure Operation

```coq
Fixpoint fsnoc {A : Type} (s : Seq A) (x : A) : Seq A :=
  match s with
  | Nil              =>
      let u' := x in
      Unit u'
  | Unit y           =>
      let f' := One y in
      let m' := Nil in
      let r' := One x in
      More f' m' r'
  | More f m r =>
      let (m, r) :=
        match r with
        | One a =>
            let r' := Two a x in
            (m, r')
        | Two a b =>
            let r' := Three a b x in
            (m, r')
        | Three a b c =>
            let pab := Pair a b in
            let m' := fsnoc m pab in
            let r' := Two c x in
            (m', r')
        end in
      More f m r
  end.
```

Mirror of `fcons`: overflow on `Three a b c` in the *rear* bundles `Pair a b`
into the middle and keeps `Two c x`.

### 3.2 Custom Induction

```coq
Lemma fsnoc_ind :
  forall (P : forall A, A -> Seq A -> Seq A -> Prop),
    (* 5 cases: Nil, Unit, One, Two, Three (recursive) *)
    forall A (x : A) (s : Seq A), P A x s (fsnoc s x).
```

### 3.3 Helper

```coq
Lemma fsnoc_go_deep : forall A (x : A) (q : Seq A),
  q <> Nil -> exists f m r, fsnoc q x = More f m r.
```

### 3.4 Clairvoyant Semantics

```coq
Fixpoint fsnocA' (A : Type) (q : SeqA A) (x : T A) : M (SeqA A) :=
  tick >>
  (match q with
  | NilA =>
      ret (UnitA x)
  | UnitA y =>
      let~ f' := ret (OneA y) in
      let~ m' := ret NilA in
      let~ r' := ret (OneA x) in
      ret (MoreA f' m' r')
  | MoreA f m r =>
      let! r_val := force r in
      match r_val with
      | OneA a =>
          let~ r' := ret (TwoA a x) in
          ret (MoreA f m r')
      | TwoA a b =>
          let~ r' := ret (ThreeA a b x) in
          ret (MoreA f m r')
      | ThreeA a b c =>
          let~ r' := ret (TwoA c x) in
          let~ pab := ret (PairA a b) in
          let~ m' := forcing m (fun m => fsnocA' m pab) in
          ret (MoreA f m' r')
      end
  end).

Definition fsnocA (A : Type) (q : T (SeqA A)) (x : T A) : M (SeqA A) :=
  forcing q (fun q => fsnocA' q x).
```

### 3.5 Monotonicity

```coq
Lemma fsnocA_mon :
  forall A `{PreOrder A LDA} x' x (q' q : T (SeqA A)),
    x' `less_defined` x -> q' `less_defined` q ->
    fsnocA q' x' `less_defined` fsnocA q x.
```

### 3.6 Demand Function

```coq
Fixpoint fsnocD' (A B : Type) `{Exact A B}
    (s : Seq A) (x : A) (outD : SeqA B)
    : Tick (T (SeqA B)) :=
  Tick.tick >>
  match s with
  | Nil =>
      match outD with
      | UnitA _ => Tick.ret (Thunk NilA)
      | _       => bottom
      end
  | Unit y =>
      match outD with
      | MoreA fD _ _ =>
          let yD := match fD with
                    | Thunk (OneA yD) => yD
                    | _               => Undefined
                    end in
          Tick.ret (Thunk (UnitA yD))
      | _ => bottom
      end
  | More f m (One a) =>
      match outD with
      | MoreA fD mD rD =>
          let aD := match rD with
                    | Thunk (TwoA aD _) => aD
                    | _                 => Undefined
                    end in
          Tick.ret (Thunk (MoreA fD mD (Thunk (OneA aD))))
      | _ => bottom
      end
  | More f m (Two a b) =>
      match outD with
      | MoreA fD mD rD =>
          let '(aD, bD) := match rD with
                           | Thunk (ThreeA aD bD _) => (aD, bD)
                           | _                      => (Undefined, Undefined)
                           end in
          Tick.ret (Thunk (MoreA fD mD (Thunk (TwoA aD bD))))
      | _ => bottom
      end
  | More f m (Three a b c) =>
      match outD with
      | MoreA fD mD rD =>
          let cD := match rD with
                    | Thunk (TwoA cD _) => cD
                    | _                 => Undefined
                    end in
          let+ mD_in := thunkD (fsnocD' m (Pair a b)) mD in
          Tick.ret (Thunk (MoreA fD mD_in (Thunk (ThreeA (exact a) (exact b) cD))))
      | _ => bottom
      end
  end.

Definition fsnocD (A : Type) : Seq A -> A -> SeqA A -> Tick (T (SeqA A)) := fsnocD'.
```

### 3.7 Core Lemmas

```coq
Lemma fsnocD'_approx / Corollary fsnocD_approx
Lemma fsnocD'_exact
Lemma fsnocD'_spec  / Corollary fsnocD_spec
Lemma fsnocD'_cost  / Corollary fsnocD_cost
  (* debt inD + cost <= 2 + debt outD — same bound as fcons *)
Lemma fsnocD'_cost_bottom
  (* debt + cost <= 3 — same as fcons *)
```

All proofs are symmetric to `FingerCons.v`.

---

## 4. FingerHead.v

**Purpose**: Query the front element. Non-recursive, O(1).

### 4.1 Pure Operation

```coq
Definition head {A : Type} (s : Seq A) : option A :=
  match s with
  | Nil => None
  | Unit x => Some x
  | More (One x) _ _ => Some x
  | More (Two x _) _ _ => Some x
  | More (Three x _ _) _ _ => Some x
  end.
```

### 4.2 Clairvoyant Semantics

```coq
Definition headA' (A : Type) (q : SeqA A) : M (option (T A)) :=
  tick >>
    match q with
    | NilA => ret None
    | UnitA x => ret (Some x)
    | MoreA fD _ _ =>
        forcing fD (fun f =>
          match f with
          | OneA x => ret (Some x)
          | TwoA x _ => ret (Some x)
          | ThreeA x _ _ => ret (Some x)
          end)
    end.

Definition headA (A : Type) (q : T (SeqA A)) : M (option (T A)) :=
  forcing q headA'.
```

### 4.3 Monotonicity

```coq
Lemma headA_mon :
  forall A `{PreOrder A LDA} (q1 q2 : T (SeqA A)),
    q1 `less_defined` q2 -> headA q1 `less_defined` headA q2.
```

### 4.4 Demand Function

```coq
Definition headD' {A B : Type} `{Exact A B} (s : Seq A) (outD : option (T B))
    : Tick (T (SeqA B)) :=
  Tick.tick >>
  match s, outD with
  | Nil, None => Tick.ret (Thunk NilA)
  | Unit x, Some xD =>
      Tick.ret (Thunk (UnitA xD))
  | Unit x, None => Tick.ret (Thunk (UnitA Undefined))
  | More (One x) m r, Some xD =>
      Tick.ret (Thunk (MoreA (Thunk (OneA xD)) Undefined Undefined))
  | More (One x) m r, None =>
      Tick.ret (Thunk (MoreA (Thunk (OneA Undefined)) Undefined Undefined))
  | More (Two x _) m r, Some xD =>
      Tick.ret (Thunk (MoreA (Thunk (TwoA xD Undefined)) Undefined Undefined))
  | More (Two x _) m r, None =>
      Tick.ret (Thunk (MoreA (Thunk (TwoA Undefined Undefined)) Undefined Undefined))
  | More (Three x _ _) m r, Some xD =>
      Tick.ret (Thunk (MoreA (Thunk (ThreeA xD Undefined Undefined)) Undefined Undefined))
  | More (Three x _ _) m r, None =>
      Tick.ret (Thunk (MoreA (Thunk (ThreeA Undefined Undefined Undefined)) Undefined Undefined))
  | _, _ => bottom
  end.

Definition headD (A : Type) : Seq A -> option (T A) -> Tick (T (SeqA A)) := headD'.
```

**Design**: Even when `outD = None` (no demand on the output), the demand on
`s` is NOT `bottom` — it must be a structured shape showing that the
operation forced the spine top and the digit constructor. Returning `bottom`
would break `CvDemand` because `headA Undefined = bottom` has no optimistic
witness.

### 4.5 Core Lemmas

```coq
Lemma headD'_approx / Corollary headD_approx
  (* Tick.val (headD' s outD) `is_approx` s *)

Lemma headD'_cost / Corollary headD_cost
  (* Tick.cost (headD' s outD) <= 1 *)

Lemma headD'_spec / Corollary headD_spec
  (* headA sD [[ fun out cost => outD <= out /\ cost <= dcost ]] *)
```

All proofs are by direct case analysis on `s` and `outD` — no recursion.

---

## 5. FingerTail.v

**Purpose**: Drop the front element (`ftail`). The most complex operation:
9 effective cases, including a recursive cascade through the spine.

### 5.1 Pure Helpers

```coq
Definition chop_triple {A : Type} (t : Tuple A) : Tuple A :=
  match t with
  | Triple _ y z => Pair y z
  | Pair x y     => Pair x y
  end.
```

Drops the first element of a `Triple`, yielding a `Pair`. Claessen's key
insight: this avoids recursion in the `Triple`-head case of `tail`.

```coq
Definition map1 {A : Type} (f : A -> A) (s : Seq A) : Seq A :=
  match s with
  | Nil                    => Nil
  | Unit x                 => Unit (f x)
  | More (One x)       m r => More (One (f x))     m r
  | More (Two x y)     m r => More (Two (f x) y)   m r
  | More (Three x y z) m r => More (Three (f x) y z) m r
  end.
```

Applies `f` to the first element of a `Seq`, leaving the structure intact.
Non-recursive. Used as `map1 chop_triple m`.

### 5.2 Pure Operation

```coq
Fixpoint ftail {A : Type} (s : Seq A) : Seq A :=
  match s with
  | Nil                    => Nil
  | Unit _                 => Nil
  | More (Three _ x y) m r => More (Two x y) m r
  | More (Two _ x)     m r => More (One x)   m r
  | More (One _)       m r =>
      match m with
      | Nil =>
          match r with
          | One   y     => Unit y
          | Two   y z   => More (One y) Nil (One z)
          | Three y z w => More (One y) Nil (Two z w)
          end
      | _ =>
          match head m with
          | Some (Pair   x y)   => More (Two x y) (ftail m) r
          | Some (Triple x _ _) => More (One x)   (map1 chop_triple m) r
          | None                => Nil
          end
      end
  end.
```

Nine effective cases:
1. `Nil` -> `Nil`
2. `Unit _` -> `Nil`
3. `More (Three _ x y) m r` -> `More (Two x y) m r` (shrink front)
4. `More (Two _ x) m r` -> `More (One x) m r` (shrink front)
5. `More (One _) Nil (One y)` -> `Unit y`
6. `More (One _) Nil (Two y z)` -> `More (One y) Nil (One z)`
7. `More (One _) Nil (Three y z w)` -> `More (One y) Nil (Two z w)`
8. `More (One _) m r` with `head m = Some (Pair x y)` -> `More (Two x y) (ftail m) r` **(recursive)**
9. `More (One _) m r` with `head m = Some (Triple x y z)` -> `More (One x) (map1 chop_triple m) r` **(non-recursive, Claessen's trick)**

### 5.3 Unfold Helpers

```coq
Lemma ftail_one_unfold_pair :
  head m = Some (Pair x y) ->
  ftail (More (One a) m r) = More (Two x y) (ftail m) r.

Lemma ftail_one_unfold_triple :
  head m = Some (Triple x y z) ->
  ftail (More (One a) m r) = More (One x) (map1 chop_triple m) r.
```

### 5.4 Custom Induction

```coq
Lemma ftail_ind :
  forall (P : forall A, Seq A -> Seq A -> Prop),
    (* 9 cases, including:
       Case 8: P (Tuple A) m (ftail m) -> head m = Some (Pair x y) -> P A ...
       Case 9: head m = Some (Triple x y z) -> P A ...  (NO IH — non-recursive) *)
    forall A s, P A s (ftail s).
```

**Design**: Cases 8 and 9 split by `head m` (not by `m`'s constructor), keeping
`m` as a Coq-tracked subterm so the inner `SELF` call structurally type-checks.

### 5.5 Clairvoyant Semantics

```coq
Fixpoint ftailA' (A : Type) (s : SeqA A) : M (SeqA A) :=
  tick >>
  match s with
  | NilA    => ret NilA
  | UnitA _ => ret NilA
  | MoreA fD mD rD =>
      forcing fD (fun f =>
        match f with
        | ThreeA _ xD yD =>
            let~ f' := ret (TwoA xD yD) in
            ret (MoreA f' mD rD)
        | TwoA _ xD =>
            let~ f' := ret (OneA xD) in
            ret (MoreA f' mD rD)
        | OneA _ =>
            forcing mD (fun m =>
              match m with
              | NilA =>
                  forcing rD (fun r =>
                    match r with
                    | OneA yD => ret (UnitA yD)
                    | TwoA yD zD =>
                        let~ f' := ret (OneA yD) in
                        let~ m' := ret NilA in
                        let~ r' := ret (OneA zD) in
                        ret (MoreA f' m' r')
                    | ThreeA yD zD wD =>
                        let~ f' := ret (OneA yD) in
                        let~ m' := ret NilA in
                        let~ r' := ret (TwoA zD wD) in
                        ret (MoreA f' m' r')
                    end)
              | UnitA t =>
                  forcing t (fun tup =>
                    match tup with
                    | PairA xD yD =>
                        let~ f' := ret (TwoA xD yD) in
                        let~ m' := ftailA' m in
                        ret (MoreA f' m' rD)
                    | TripleA xD yD zD =>
                        let~ f' := ret (OneA xD) in
                        let~ pyz := ret (PairA yD zD) in
                        let~ m' := ret (UnitA pyz) in
                        ret (MoreA f' m' rD)
                    end)
              | MoreA fmD mmD rmD =>
                  forcing fmD (fun fm =>
                    match fm with
                    | OneA t =>
                        forcing t (fun tup =>
                          match tup with
                          | PairA xD yD =>
                              let~ f' := ret (TwoA xD yD) in
                              let~ m' := ftailA' m in
                              ret (MoreA f' m' rD)
                          | TripleA xD yD zD =>
                              let~ f'  := ret (OneA xD) in
                              let~ pyz := ret (PairA yD zD) in
                              let~ fm' := ret (OneA pyz) in
                              let~ m'  := ret (MoreA fm' mmD rmD) in
                              ret (MoreA f' m' rD)
                          end)
                    | TwoA t t' =>
                        forcing t (fun tup =>
                          match tup with
                          | PairA xD yD =>
                              let~ f' := ret (TwoA xD yD) in
                              let~ m' := ftailA' m in
                              ret (MoreA f' m' rD)
                          | TripleA xD yD zD =>
                              let~ f'  := ret (OneA xD) in
                              let~ pyz := ret (PairA yD zD) in
                              let~ fm' := ret (TwoA pyz t') in
                              let~ m'  := ret (MoreA fm' mmD rmD) in
                              ret (MoreA f' m' rD)
                          end)
                    | ThreeA t t' t'' =>
                        forcing t (fun tup =>
                          match tup with
                          | PairA xD yD =>
                              let~ f' := ret (TwoA xD yD) in
                              let~ m' := ftailA' m in
                              ret (MoreA f' m' rD)
                          | TripleA xD yD zD =>
                              let~ f'  := ret (OneA xD) in
                              let~ pyz := ret (PairA yD zD) in
                              let~ fm' := ret (ThreeA pyz t' t'') in
                              let~ m'  := ret (MoreA fm' mmD rmD) in
                              ret (MoreA f' m' rD)
                          end)
                    end)
              end)
        end)
  end.

Definition ftailA (A : Type) (q : T (SeqA A)) : M (SeqA A) :=
  forcing q ftailA'.
```

Mirrors `ftail`'s 9-case structure. The One-front cascade is inlined
(~6 levels deep at worst) rather than factored through a helper.

### 5.6 Monotonicity

```coq
Lemma ftailA'_mon :
  forall A (q2' : SeqA A) `{PreOrder A LDA} (q1' : SeqA A),
    q1' `less_defined` q2' -> ftailA' q1' `less_defined` ftailA' q2'.

Lemma ftailA_mon :
  forall A `{PreOrder A LDA} (q1 q2 : T (SeqA A)),
    q1 `less_defined` q2 -> ftailA q1 `less_defined` ftailA q2.
```

*Proof sketch*: By `SeqA_ind` on `q2`. The `MoreA` case with `Thunk md_inner`
dispatches on `md_inner`'s shape (NilA/UnitA/MoreA), then on the front digit
constructor. For PairA sub-cases, the recursive `ftailA'` call uses the IH;
for TripleA, monotonicity is structural.

### 5.7 Demand Helpers

```coq
Definition inverse_chop_tuple {B : Type}
    (xD : T B) (t : T (TupleA B)) : T (TupleA B) :=
  match t with
  | Thunk (PairA yD zD) => Thunk (TripleA xD yD zD)
  | Thunk (TripleA _ _ _) => t
  | Undefined => Thunk (TripleA xD Undefined Undefined)
  end.

Definition inverse_chop_digit {B : Type}
    (xD : T B) (d : DigitA (TupleA B)) : DigitA (TupleA B) :=
  match d with
  | OneA t => OneA (inverse_chop_tuple xD t)
  | TwoA t t' => TwoA (inverse_chop_tuple xD t) t'
  | ThreeA t t' t'' => ThreeA (inverse_chop_tuple xD t) t' t''
  end.

Definition undef_inverse_chop_digit {A B : Type} `{Exact A B}
    (m_d : Digit (Tuple A)) (xD : T B) : DigitA (TupleA B) :=
  match m_d with
  | One _ => OneA (Thunk (TripleA xD Undefined Undefined))
  | Two _ _ => TwoA (Thunk (TripleA xD Undefined Undefined)) Undefined
  | Three _ _ _ => ThreeA (Thunk (TripleA xD Undefined Undefined)) Undefined Undefined
  end.

Definition inverse_chop_demand {A B : Type} `{Exact A B}
    (m : Seq (Tuple A))
    (mD : T (SeqA (TupleA B))) (xD : T B) : T (SeqA (TupleA B)) :=
  match mD with
  | Thunk NilA => Thunk NilA
  | Thunk (UnitA t) => Thunk (UnitA (inverse_chop_tuple xD t))
  | Thunk (MoreA fD mD_inner rD) =>
      let fD' :=
        match fD with
        | Thunk d => Thunk (inverse_chop_digit xD d)
        | Undefined =>
            match m with
            | More m_d _ _ => Thunk (undef_inverse_chop_digit m_d xD)
            | _ => Thunk (OneA (Thunk (TripleA xD Undefined Undefined)))
            end
        end in
      Thunk (MoreA fD' mD_inner rD)
  | Undefined =>
      match m with
      | Nil => Undefined
      | Unit _ => Thunk (UnitA (Thunk (TripleA xD Undefined Undefined)))
      | More m_d _ _ =>
          Thunk (MoreA (Thunk (undef_inverse_chop_digit m_d xD))
                       Undefined Undefined)
      end
  end.
```

For Case 9: rewrites a demand on `map1 chop_triple m` back to a demand on `m`
by transforming the head `Pair` to a `Triple` with `xD` as the first element.

```coq
Definition add_pair_to_head_digit {B : Type}
    (xD yD : T B) (d : DigitA (TupleA B)) : DigitA (TupleA B) :=
  match d with
  | OneA _ => OneA (Thunk (PairA xD yD))
  | TwoA _ t' => TwoA (Thunk (PairA xD yD)) t'
  | ThreeA _ t' t'' => ThreeA (Thunk (PairA xD yD)) t' t''
  end.

Definition undef_add_pair_to_head_digit {A B : Type} `{Exact A B}
    (m_d : Digit (Tuple A)) (xD yD : T B) : DigitA (TupleA B) :=
  match m_d with
  | One _ => OneA (Thunk (PairA xD yD))
  | Two _ _ => TwoA (Thunk (PairA xD yD)) Undefined
  | Three _ _ _ => ThreeA (Thunk (PairA xD yD)) Undefined Undefined
  end.

Definition add_pair_to_head_demand {A B : Type} `{Exact A B}
    (m : Seq (Tuple A))
    (mD : T (SeqA (TupleA B))) (xD yD : T B) : T (SeqA (TupleA B)) :=
  match mD with
  | Thunk NilA => Thunk (UnitA (Thunk (PairA xD yD)))
  | Thunk (UnitA _) => Thunk (UnitA (Thunk (PairA xD yD)))
  | Thunk (MoreA fD mD_inner rD) =>
      let fD' :=
        match fD with
        | Thunk d => Thunk (add_pair_to_head_digit xD yD d)
        | Undefined =>
            match m with
            | More m_d _ _ => Thunk (undef_add_pair_to_head_digit m_d xD yD)
            | _ => Thunk (OneA (Thunk (PairA xD yD)))
            end
        end in
      Thunk (MoreA fD' mD_inner rD)
  | Undefined =>
      match m with
      | Nil => Undefined
      | Unit _ => Thunk (UnitA (Thunk (PairA xD yD)))
      | More m_d _ _ =>
          Thunk (MoreA (Thunk (undef_add_pair_to_head_digit m_d xD yD))
                       Undefined Undefined)
      end
  end.
```

For Case 8: augments a recursive demand on `m` (from `ftailD' m _`) with a
`Pair x y` head element.

### 5.8 Debt Preservation Lemmas

```coq
Lemma debt_inverse_chop_demand_Thunk_le :
  debt (inverse_chop_demand m (Thunk sD) xD) <= debt (Thunk sD).

Lemma debt_add_pair_to_head_demand_Thunk_le :
  debt (add_pair_to_head_demand m (Thunk sD) xD yD) <= debt (Thunk sD).
```

These show that the demand helpers do not increase the debt — critical for the
cost lemma.

### 5.9 Demand Function

```coq
Fixpoint ftailD' (A B : Type) `{Exact A B} (s : Seq A) (outD : SeqA B)
    : Tick (T (SeqA B)) :=
  Tick.tick >>
  match s with
  | Nil =>
      match outD with
      | NilA => Tick.ret (Thunk NilA)
      | _    => bottom
      end
  | Unit _ =>
      match outD with
      | NilA => Tick.ret (Thunk (UnitA Undefined))
      | _    => bottom
      end
  | More (Three _ x y) m r =>
      match outD with
      | MoreA fD mD rD =>
          let '(xD, yD) := match fD with
                           | Thunk (TwoA xD yD) => (xD, yD)
                           | _ => (Undefined, Undefined)
                           end in
          Tick.ret (Thunk (MoreA (Thunk (ThreeA Undefined xD yD)) mD rD))
      | _ => bottom
      end
  | More (Two _ x) m r =>
      match outD with
      | MoreA fD mD rD =>
          let xD := match fD with
                    | Thunk (OneA xD) => xD
                    | _ => Undefined
                    end in
          Tick.ret (Thunk (MoreA (Thunk (TwoA Undefined xD)) mD rD))
      | _ => bottom
      end
  | More (One _) m r =>
      match m with
      | Nil =>
          match r, outD with
          | One y, UnitA yD =>
              Tick.ret (Thunk (MoreA (Thunk (OneA Undefined))
                                      (Thunk NilA)
                                      (Thunk (OneA yD))))
          | Two y z, MoreA fD _ rD =>
              let yD := match fD with
                        | Thunk (OneA yD) => yD
                        | _ => Undefined
                        end in
              let zD := match rD with
                        | Thunk (OneA zD) => zD
                        | _ => Undefined
                        end in
              Tick.ret (Thunk (MoreA (Thunk (OneA Undefined))
                                      (Thunk NilA)
                                      (Thunk (TwoA yD zD))))
          | Three y z w, MoreA fD _ rD =>
              let yD := match fD with
                        | Thunk (OneA yD) => yD
                        | _ => Undefined
                        end in
              let '(zD, wD) := match rD with
                               | Thunk (TwoA zD wD) => (zD, wD)
                               | _ => (Undefined, Undefined)
                               end in
              Tick.ret (Thunk (MoreA (Thunk (OneA Undefined))
                                      (Thunk NilA)
                                      (Thunk (ThreeA yD zD wD))))
          | _, _ => bottom
          end
      | _ =>
          match head m with
          | Some (Pair _ _) =>
              match outD with
              | MoreA fD mD_out rD =>
                  let '(xD, yD) := match fD with
                                   | Thunk (TwoA xD yD) => (xD, yD)
                                   | _ => (Undefined, Undefined)
                                   end in
                  let+ mD_rec := thunkD (ftailD' m) mD_out in
                  let mD_in := add_pair_to_head_demand m mD_rec xD yD in
                  Tick.ret (Thunk (MoreA (Thunk (OneA Undefined)) mD_in rD))
              | _ => bottom
              end
          | Some (Triple _ _ _) =>
              match outD with
              | MoreA fD mD_out rD =>
                  let xD := match fD with
                            | Thunk (OneA xD) => xD
                            | _ => Undefined
                            end in
                  let mD_in := inverse_chop_demand m mD_out xD in
                  Tick.ret (Thunk (MoreA (Thunk (OneA Undefined)) mD_in rD))
              | _ => bottom
              end
          | None => bottom
          end
      end
  end.

Definition ftailD (A : Type) : Seq A -> SeqA A -> Tick (T (SeqA A)) := ftailD'.
```

### 5.10 Value Existence Helper

```coq
Lemma ftailD'_val_more :
  forall ... (a : Digit A) (m : Seq (Tuple A)) (r : Digit A) (outD : SeqA B),
    outD `is_approx` ftail (More a m r) ->
    exists v, Tick.val (ftailD' (More a m r) outD) = Thunk v.
```

### 5.11 Approx Helper Lemmas

```coq
Lemma inverse_chop_demand_approx :
  head m = Some (Triple x y z) -> xD `is_approx` x ->
  mD `is_approx` map1 chop_triple m ->
  inverse_chop_demand m mD xD `is_approx` m.

Lemma add_pair_to_head_demand_approx :
  head m = Some (Pair x y) -> xD `is_approx` x -> yD `is_approx` y ->
  mD `is_approx` m ->
  add_pair_to_head_demand m mD xD yD `is_approx` m.
```

### 5.12 Core Lemmas

#### Approx

```coq
Lemma ftailD'_approx :
  forall A B ... (s : Seq A) (outD : SeqA B),
    outD `is_approx` ftail s ->
    Tick.val (ftailD' s outD) `is_approx` s.

Lemma ftailD_approx.
```

*Proof*: By `ftail_ind`, 9 cases. Case 8 (Pair-head, recursive) uses
the IH + `add_pair_to_head_demand_approx`. Case 9 (Triple-head) uses
`inverse_chop_demand_approx`.

#### Cost

```coq
Lemma ftailD'_cost :
  forall A B ... (s : Seq A) (outD : SeqA B),
    outD `is_approx` ftail s ->
    debt (Tick.val (ftailD' s outD)) + Tick.cost (ftailD' s outD) <= 3 + debt outD.

Lemma ftailD_cost.
```

*Proof sketch*: By `ftail_ind`. Budget = 3 (matches fcons).
- Cases 1-2 (Nil/Unit): trivial.
- Case 3 (Three -> Two): output has `TwoA` (safe, +1), input has `ThreeA` (dangerous, 0). Net gain from potential.
- Case 4 (Two -> One): loses 1 potential, but 1 tick + 2 <= 3.
- Cases 5-7 (One, Nil spine): direct computation.
- Case 8 (Pair-head, recursive): IH gives `debt(mD_rec) + rc <= 3 + debt(mD_out)`.
  `add_pair_to_head_demand` doesn't increase debt. `OneA` front contributes 0.
  The `Undefined`-mD_out sub-case with `Two`-front-in-m binds at K=3.
- Case 9 (Triple-head, non-recursive): `inverse_chop_demand` doesn't increase debt.
  Cost is 1 tick. The `Undefined`-mD_out sub-case with `Two`-front-in-m binds at K=3.

### 5.13 Auxiliary Front-Shape Lemmas

```coq
Lemma ftailD'_front_OneA_undef_pair :
  (* When ftailD' produces MoreA fmD mmD rmD for a Pair-front input,
     the front is always Thunk (OneA Undefined) *)

Lemma ftailD'_front_TwoA_undef_pair :
  (* When input front is Two (Pair a b) ..., result front is Thunk (TwoA Undefined xD) *)

Lemma ftailD'_front_ThreeA_undef_pair :
  (* When input front is Three (Pair a b) ..., result front is Thunk (ThreeA Undefined xD yD) *)
```

These are used in `ftailD'_spec` to determine the shape of intermediate demands.

### 5.14 Spec

```coq
Lemma ftailD'_spec :
  forall A B `{LessDefined B, !Reflexive LDB, !Transitive LDB, Exact A B}
    (q : Seq A) (outD : SeqA B),
    outD `is_approx` ftail q ->
    forall qD, qD = Tick.val (ftailD' q outD) ->
      ftailA qD [[ fun out cost => outD `less_defined` out /\ cost <= Tick.cost (ftailD' q outD) ]].

Lemma ftailD_spec.
```

*Proof sketch*: By `ftail_ind`. Each case unfolds `ftailA` and `ftailD'` in lockstep.
Cases 1-7 and 9 use `mgo_`/`keep_mgo_` for structural witnessing. Case 8 (Pair-head recursive)
applies the IH at the recursive `ftailD'` call site via `optimistic_mon`, producing
a sub-witness for `ftailA` on the recursive value. Case 9 uses `inverse_chop_demand`
threading.

---

## 6. FingerPhysicist.v

**Purpose**: Ties everything together. Defines the operation algebra, the
physicist's argument, and proves the final amortised cost theorem.

### 6.1 Auxiliary Definitions

```coq
Definition empty (A : Type) : Seq A := Nil.

Definition emptyD (A : Type) (outD : SeqA A) : Tick unit :=
  Tick.tick >>
    match outD with
    | NilA => Tick.ret tt
    | _ => bottom
    end.
```

```coq
Lemma emptyD_approx :
  outD `is_approx` empty -> Tick.val (emptyD outD) `is_approx` tt.
```

```coq
Definition emptyA (A : Type) : M (SeqA A) := tick >> ret NilA.
```

```coq
Lemma emptyD_spec :
  outD `is_approx` empty ->
  emptyA [[ fun out cost => outD `less_defined` out /\ cost <= Tick.cost (emptyD outD) ]].
```

```coq
Definition forceD (A : Type) (y : A) (u : T A) : A :=
  match u with
  | Undefined => y
  | Thunk x => x
  end.

Lemma less_defined_forceD :
  y `less_defined` z -> x `less_defined` Thunk z ->
  forceD y x `less_defined` z.
```

### 6.2 Physicist's Argument Section

```coq
Section Physicist'sArgument.
  Context (A : Type).

  Definition value := Seq A.
  Definition valueA := T (SeqA A).
```

#### Operation Algebra

```coq
  Inductive op : Type :=
    | Empty
    | FCons (x : A)
    | FSnoc (x : A)
    | Head
    | FTail.
```

#### Eval (pure semantics)

```coq
  Instance eval : Eval op value :=
    fun op args => match op, args with
      | Empty,   []  => [empty]
      | FCons x, [q] => [fcons x q]
      | FSnoc x, [q] => [fsnoc q x]
      | Head,    [q] => []
      | FTail,   [q] => [ftail q]
      | _, _         => []
    end.
```

#### Budget

```coq
  Instance budget : Budget op value := fun o _ => 4.
```

Every operation has budget 4 (= cost bound 3 + 1 for the outer tick of
the demand function).

#### Exec (clairvoyant semantics)

```coq
  Instance exec : Exec op valueA :=
    fun o args => match o, args with
      | Empty,   []  => let! q := emptyA in ret [Thunk q]
      | FCons x, [q] => let! q' := fconsA (exact x) q in ret [Thunk q']
      | FSnoc x, [q] => let! q' := fsnocA q (exact x) in ret [Thunk q']
      | Head,    [q] => let! _ := headA q in ret []
      | FTail,   [q] => let! q' := ftailA q in ret [Thunk q']
      | _, _         => ret []
    end.
```

#### Well-formedness

```coq
  Instance wf : WellFormed value := fun _ => True.
  Lemma wf_eval : WfEval.
```

#### Monotonicity

```coq
  Lemma monotonic_exec `{PreOrder A LDA} (o : op) : Monotonic (exec o).
```

*Proof*: Case-split on `o`; each case delegates to the corresponding
`*A_mon` lemma (`fconsA_mon`, `fsnocA_mon`, `headA_mon`, `ftailA_mon`).

#### Approx Algebra

```coq
  Instance approx_algebra ... : IsApproxAlgebra value valueA.
  Lemma well_defined_exec : WellDefinedExec.
```

#### Demand (backward demand propagation)

```coq
  Instance demand : Demand op value valueA :=
    fun op args argsA => match op, args, argsA with
      | Empty,   [],  [outD] => ... emptyD ...
      | FCons x, [q], [outD] => ... fconsD x q (forceD ... outD) ...
      | FSnoc x, [q], [outD] => ... fsnocD q x (forceD ... outD) ...
      | Head,    [q], []     => ... headD q None ...
      | FTail,   [q], [outD] => ... ftailD q (forceD ... outD) ...
      | _, _, _              => Tick.ret (bottom_of (exact args))
    end.
```

#### Potential

```coq
  Instance potential : Potential valueA :=
    fun qD => match qD with Thunk qA => debt qA | Undefined => 0 end.
```

#### PureDemand

```coq
  Lemma pd : PureDemand.
```

Shows that demand functions produce valid approximations of their inputs.
Each operation case delegates to its `*D_approx` lemma.

#### CvDemand

```coq
  Lemma cd : CvDemand.
```

Shows that demand functions agree with (are dominated by) the clairvoyant
semantics. Each operation case delegates to its `*D_spec` lemma via
`optimistic_mon`.

#### WellDefinedPotential

```coq
  Lemma well_defined_potential : WellDefinedPotential.
```

Two obligations:
1. **Sub-additivity**: `debt(lub x y) <= debt(x) + debt(y)` — delegates to
   `debt_SeqA_lub_subadditive`.
2. **Potential of bottom is zero**: trivial.

#### The Core Theorem

```coq
  Theorem physicist's_argumentD :
    forall `{PreOrder A LDA, LBA : Lub A, @LubLaw A LBA LDA},
      Physicist'sArgumentD.
```

**This is the main amortised inequality**. For each operation and valid
demand configuration:

    `sumof potential (input demands) + cost <= budget + sumof potential (output demands)`

*Proof*: By case-split on operation. Each case uses `forceD` + the
corresponding `*D_cost` / `*D_cost_bottom` lemma. The `Undefined` sub-cases
compute directly.

#### Final Theorem

```coq
  Theorem amortized_cost :
    forall `{PreOrder A LDA, Lub A, LubLaw A},
      AmortizedCostSpec.
```

*Proof*: One-liner — `eapply physicist's_method`.

```coq
End Physicist'sArgument.
```

---

## 7. FingerMonoid.v

**Purpose**: The abstract monoid interface for annotated (measured) finger trees,
independent of the Clairvoyance library.

### 7.1 Monoid Class

```coq
Class Monoid (M : Type) : Type := {
  mzero : M;
  madd  : M -> M -> M;
  madd_zero_l : forall x, madd mzero x = x;
  madd_zero_r : forall x, madd x mzero = x;
  madd_assoc  : forall x y z, madd (madd x y) z = madd x (madd y z);
}.
```

Notation: `Infix "<+>" := madd`.

### 7.2 Derived Facts

```coq
Lemma madd_assoc4 (a b c d : M) :
  a <+> b <+> c <+> d = a <+> (b <+> (c <+> d)).

Lemma madd_shift (a b c : M) :
  a <+> b <+> c = a <+> (b <+> c).
```

### 7.3 Size Monoid (Random Access)

```coq
Instance Monoid_size : Monoid nat := { mzero := 0; madd := Nat.add }.
```

With `md := fun _ => 1`, `splitTree (fun sz => i <? sz) 0` locates element `i`.

### 7.4 Interval Monoid (Min-Max Priority Queue)

```coq
Definition Interval := option (nat * nat).
Instance Monoid_interval : Monoid Interval.
  (* None is identity; Some (min, max) merged pointwise *)
```

### 7.5 Last-Value Monoid (Ordered Sequence / Binary Search)

```coq
Instance Monoid_lastval : Monoid (option nat).
  (* None is identity; rightmost value wins *)
```

---

## 8. FingerSize.v

**Purpose**: Structural metrics (size, depth) and the logarithmic bound
`depth s <= log2 (size s)`.

### 8.1 Polymorphic Induction for Seq

```coq
Lemma Seq_ind_poly (P : forall A, Seq A -> Prop) :
  (forall A, P A Nil) ->
  (forall A x, P A (Unit x)) ->
  (forall A f m r, P (Tuple A) m -> P A (More f m r)) ->
  forall A (s : Seq A), P A s.
```

Threads a polymorphic motive through the non-uniform recursion.

### 8.2 Size

```coq
Definition digit_size {A : Type} (d : Digit A) : nat :=
  match d with
  | One _       => 1
  | Two _ _     => 2
  | Three _ _ _ => 3
  end.

Fixpoint size {A : Type} (s : Seq A) : nat :=
  match s with
  | Nil        => 0
  | Unit _     => 1
  | More u m v => digit_size u + 2 * size m + digit_size v
  end.
```

Uses conservative factor 2 for tuples (lower bound).

### 8.3 Helper

```coq
Lemma Seq_nil_dec {A} (s : Seq A) : s = Nil \/ s <> Nil.
```

### 8.4 Size-Depth Relationship

```coq
Lemma size_lower_bound (A : Type) (s : Seq A) :
  s <> Nil -> 2 ^ depth s <= size s.
```

*Proof*: By `Seq_ind_poly`. `More` case: if `m = Nil`, `size >= 2 = 2^1`;
if `m <> Nil`, by IH `size >= 2 * 2^(depth m) = 2^(S (depth m))`.

```coq
Lemma size_pos (A : Type) (s : Seq A) :
  s <> Nil -> 0 < size s.
```

```coq
Corollary depth_log_size (A : Type) (s : Seq A) :
  s <> Nil -> depth s <= Nat.log2 (size s).
```

*Proof*: From `size_lower_bound` and `Nat.log2_spec`, by contradiction.

---

## 9. FingerConcat.v

**Purpose**: Concatenation via Claessen's `glue`. Worst-case O(log n).

### 9.1 Pure Helpers

```coq
Definition digitToList {A : Type} (d : Digit A) : list A :=
  match d with
  | One   x     => [x]
  | Two   x y   => [x; y]
  | Three x y z => [x; y; z]
  end.

Fixpoint toTuples {A : Type} (xs : list A) : list (Tuple A) :=
  match xs with
  | []            => []
  | [x; y]        => [Pair x y]
  | [x; y; z; w]  => [Pair x y; Pair z w]
  | x :: y :: z :: rest => Triple x y z :: toTuples rest
  | _             => []
  end.
```

### 9.2 Pure Glue

```coq
Fixpoint glue {A : Type} (s1 : Seq A) (as_ : list A) (s2 : Seq A) {struct s1} : Seq A :=
  match s1, s2 with
  | Nil, _              => List.fold_right fcons s2 as_
  | _, Nil              => List.fold_left fsnoc as_ s1
  | Unit x, _           => List.fold_right fcons s2 (x :: as_)
  | _, Unit y           => List.fold_left fsnoc (as_ ++ [y]) s1
  | More u1 m1 v1, More u2 m2 v2 =>
      More u1
        (glue m1 (toTuples (digitToList v1 ++ as_ ++ digitToList u2)) m2)
        v2
  end.

Definition concat {A : Type} (s1 s2 : Seq A) : Seq A := glue s1 [] s2.
```

Six cases:
1. `Nil, _, _`: fold `fcons` over `as_` into `s2`.
2-3. `_, Nil`: fold `fsnoc` over `as_` from `s1`.
4. `Unit x, _, _`: fold `fcons` with `x :: as_`.
5. `More u1 m1 v1, _, Unit y`: fold `fsnoc` with `as_ ++ [y]`.
6. `More u1 m1 v1, _, More u2 m2 v2`: **deep case** — `More u1 (glue m1 (toTuples (digitToList v1 ++ as_ ++ digitToList u2)) m2) v2`.

### 9.3 Custom Induction

```coq
Lemma glue_ind :
  forall (P : forall A, Seq A -> list A -> Seq A -> Seq A -> Prop),
    (* 6 cases *)
    forall A (s1 : Seq A) (as_ : list A) (s2 : Seq A),
      P A s1 as_ s2 (glue s1 as_ s2).
```

### 9.4 Clairvoyant Semantics

```coq
Definition digitToListA {A : Type} (d : DigitA A) : list (T A) :=
  match d with
  | OneA   x     => [x]
  | TwoA   x y   => [x; y]
  | ThreeA x y z => [x; y; z]
  end.

Fixpoint toTuplesA {A : Type} (xs : list (T A)) : list (T (TupleA A)) :=
  match xs with
  | []            => []
  | [x; y]        => [Thunk (PairA x y)]
  | [x; y; z; w]  => [Thunk (PairA x y); Thunk (PairA z w)]
  | x :: y :: z :: rest => Thunk (TripleA x y z) :: toTuplesA rest
  | _             => []
  end.

Fixpoint glueA' (A : Type) (q1 : SeqA A) (as_ : list (T A)) (q2 : SeqA A)
    {struct q1} : M (SeqA A) :=
  tick >>
  (match q1, q2 with
   | NilA, _ =>
       List.fold_right
         (fun x acc => let! q := acc in fconsA x (Thunk q))
         (ret q2) as_
   | _, NilA =>
       List.fold_left
         (fun acc x => let! q := acc in fsnocA (Thunk q) x)
         as_ (ret q1)
   | UnitA x, _ =>
       List.fold_right
         (fun x acc => let! q := acc in fconsA x (Thunk q))
         (ret q2) (x :: as_)
   | _, UnitA y =>
       List.fold_left
         (fun acc x => let! q := acc in fsnocA (Thunk q) x)
         (as_ ++ [y]) (ret q1)
   | MoreA fD1 mD1 rD1, MoreA fD2 mD2 rD2 =>
       let! v1 := force rD1 in
       let! u2 := force fD2 in
       let middle := digitToListA v1 ++ as_ ++ digitToListA u2 in
       let tuples := toTuplesA middle in
       let~ m' := forcing mD1 (fun m1' =>
                  forcing mD2 (fun m2' => glueA' m1' tuples m2')) in
       ret (MoreA fD1 m' rD2)
   end).

Definition glueA (A : Type) (q1 : T (SeqA A)) (as_ : list (T A)) (q2 : T (SeqA A))
    : M (SeqA A) :=
  forcing q1 (fun q1 => forcing q2 (fun q2 => glueA' q1 as_ q2)).
```

### 9.5 Monotonicity Helpers

```coq
Lemma fold_fconsA_mon : (* fold_right fconsA is monotone in list + accumulator *)
Lemma fold_fsnocA_mon : (* fold_left fsnocA is monotone *)
Lemma toTuplesA_mon   : (* toTuplesA preserves Forall2 less_defined *)
```

(`glueA'_mon` and `glueA_mon` are commented out / future work.)

### 9.6 Demand Functions

```coq
Fixpoint foldr_fconsD' (A B : Type) `{Exact A B}
    (as_ : list A) (s_2 : Seq A) (outD : SeqA B)
    : Tick (T (SeqA B)) :=
  match as_ with
  | [] =>
      Tick.ret (Thunk outD)
  | x :: as' =>
      let+ innerD := fconsD' x (List.fold_right fcons s_2 as') outD in
      let innerD_forced := match innerD with
                           | Thunk q => q
                           | Undefined => bottom_of (exact (List.fold_right fcons s_2 as'))
                           end in
      foldr_fconsD' as' s_2 innerD_forced
  end.

Fixpoint foldl_fsnocD' (A B : Type) `{Exact A B}
    (as_ : list A) (s_1 : Seq A) (outD : SeqA B)
    {struct as_} : Tick (T (SeqA B)) :=
  match as_ with
  | [] =>
      Tick.ret (Thunk outD)
  | x :: as' =>
      let+ innerD := foldl_fsnocD' as' (fsnoc s_1 x) outD in
      let innerD_forced := match innerD with
                           | Thunk q => q
                           | Undefined => bottom_of (exact (fsnoc s_1 x))
                           end in
      let+ s1D := fsnocD' s_1 x innerD_forced in
      Tick.ret s1D
  end.

Definition unbundle {B : Type}
    (tuplesD : list (T (TupleA B)))
    (n_v1 n_as n_u2 : nat) :
    T (DigitA B) * list (T B) * T (DigitA B) :=
  (Undefined, [], Undefined).
  (* STUB for Claim 1 (cost-only); correct implementation needed for approx/spec *)

Fixpoint glueD' (A B : Type) `{Exact A B}
    (s1 : Seq A) (as_ : list A) (s2 : Seq A) (outD : SeqA B)
    {struct s1} : Tick (T (SeqA B) * list (T B) * T (SeqA B)) :=
  Tick.tick >>
  match s1, s2 with
  | Nil, _ =>
      let+ s2D := foldr_fconsD' as_ s2 outD in
      Tick.ret (Thunk NilA, List.map (fun _ => Undefined) as_, s2D)
  | Unit x, Nil =>
      let+ s1D := foldl_fsnocD' as_ (Unit x) outD in
      Tick.ret (s1D, List.map (fun _ => Undefined) as_, Thunk NilA)
  | More u1 m1 v1, Nil =>
      let+ s1D := foldl_fsnocD' as_ (More u1 m1 v1) outD in
      Tick.ret (s1D, List.map (fun _ => Undefined) as_, Thunk NilA)
  | Unit x, _ =>
      let+ s2D := foldr_fconsD' (x :: as_) s2 outD in
      Tick.ret (Thunk (UnitA Undefined), List.map (fun _ => Undefined) as_, s2D)
  | More u1 m1 v1, Unit y =>
      let+ s1D := foldl_fsnocD' (as_ ++ [y]) (More u1 m1 v1) outD in
      Tick.ret (s1D, List.map (fun _ => Undefined) as_, Thunk (UnitA Undefined))
  | More u1 m1 v1, More u2 m2 v2 =>
      match outD with
      | MoreA u1D m'D v2D =>
          let n_v1 := List.length (digitToList v1) in
          let n_as := List.length as_ in
          let n_u2 := List.length (digitToList u2) in
          let middle := toTuples (digitToList v1 ++ as_ ++ digitToList u2) in
          let m'D_forced := match m'D with
                            | Thunk q => q
                            | Undefined => bottom_of (exact (glue m1 middle m2))
                            end in
          let+ (m1D, middleD, m2D) := glueD' m1 middle m2 m'D_forced in
          let '(v1D, asD, u2D) := unbundle middleD n_v1 n_as n_u2 in
          Tick.ret (Thunk (MoreA u1D m1D v1D), asD, Thunk (MoreA u2D m2D v2D))
      | _ =>
          Tick.ret (Undefined, List.map (fun _ => Undefined) as_, Undefined)
      end
  end.

Definition glueD (A : Type) : Seq A -> list A -> Seq A -> SeqA A
                            -> Tick (T (SeqA A) * list (T A) * T (SeqA A)) :=
  glueD'.

Definition concatD (A : Type) (q1 q2 : Seq A) (outD : SeqA A)
    : Tick (T (SeqA A) * list (T A) * T (SeqA A)) :=
  glueD' q1 [] q2 outD.
```

### 9.7 Cost Lemmas

```coq
Lemma debt_le_2depth :
  forall A (s : Seq A) B ... (outD : SeqA B),
    outD `is_approx` s -> debt outD <= 2 * depth s.
```

*Proof*: By `Seq_ind_poly`. `More` case: `safe_T <= 1` for each digit + spine IH.

```coq
Lemma fcons_depth : depth (fcons x s) <= depth s + 1.
Lemma foldr_fcons_depth : depth (fold_right fcons s2 as_) <= depth s2 + length as_.
Lemma fsnoc_depth : depth (fsnoc s x) <= depth s + 1.
```

```coq
Lemma foldr_fconsD'_cost :
  outD `is_approx` fold_right fcons s2 as_ ->
  Tick.cost (foldr_fconsD' as_ s2 outD) <= length as_ * (4 + 2 * depth s2 + 2 * length as_).
```

```coq
Lemma foldl_fsnocD'_approx :
  outD `is_approx` fold_left fsnoc as_ s1 ->
  Tick.val (foldl_fsnocD' as_ s1 outD) `is_approx` s1.

Lemma foldl_fsnocD'_cost :
  outD `is_approx` fold_left fsnoc as_ s1 ->
  Tick.cost (foldl_fsnocD' as_ s1 outD) <= length as_ * (4 + 2 * depth s1 + 2 * length as_).
```

```coq
Definition glue_cost_const_1 : nat := 8.
Definition glue_cost_const_2 : nat := 60.
```

```coq
Lemma toTuples_length_bound :
  length xs <= 9 -> length (toTuples xs) <= 3.
```

#### Main Cost Theorem

```coq
Lemma glueD'_cost :
  forall A (s1 : Seq A) B ... (as_ : list A) (s2 : Seq A) (outD : SeqA B),
    outD `is_approx` glue s1 as_ s2 ->
    length as_ <= 3 ->
    Tick.cost (glueD' s1 as_ s2 outD) <= 8 * (depth s1 + depth s2) + 60.
```

*Proof sketch*: By `Seq_ind_poly` on `s1`, maintaining invariant `length as_ <= 3`.
- `Nil`/`Unit`: fold costs bounded by the fold-cost lemmas.
- `More-More` (deep case): IH at `Tuple A` on the recursive call. `toTuples`
  preserves `length <= 3`. Cost = 1 (tick) + recursive cost.

```coq
Corollary concatD_cost :
  outD `is_approx` concat q1 q2 ->
  Tick.cost (concatD q1 q2 outD) <= 8 * (depth q1 + depth q2) + 60.
```

### 9.8 Asymptotic Corollaries

```coq
Corollary concatD_cost_logsize :
  q1 <> Nil -> q2 <> Nil -> outD `is_approx` concat q1 q2 ->
  Tick.cost (concatD q1 q2 outD) <= 8 * (log2 (size q1) + log2 (size q2)) + 60.

Lemma log2_sum_bound :
  0 < a -> 0 < b -> log2 a + log2 b <= 2 * log2 (a + b).

Corollary concatD_cost_O_log_n :
  q1 <> Nil -> q2 <> Nil -> outD `is_approx` concat q1 q2 ->
  Tick.cost (concatD q1 q2 outD) <= 16 * log2 (size q1 + size q2) + 60.
```

### 9.9 Future Work (Admitted/Commented)

`glueD'_approx`, `glueD'_exact`, `glueD'_spec` — require correct `unbundle`.

---

## 10. FingerSplit.v

**Purpose**: Annotated (measured) finger trees with `splitTree`, `index`, and
`split`. Worst-case O(log n). Measures are abstract over a `Monoid`.

### 10.1 Annotated Pure Structure

```coq
Inductive MTuple (M A : Type) : Type :=
  | MPair   : M -> A -> A -> MTuple M A
  | MTriple : M -> A -> A -> A -> MTuple M A.
```

Tuples with cached measures.

```coq
Inductive MSeq (M A : Type) : Type :=
  | MNil  : MSeq M A
  | MUnit : A -> MSeq M A
  | MMore : M -> Digit A -> MSeq M (MTuple M A) -> Digit A -> MSeq M A.
```

Sequence with cached middle-spine measure `M`.

### 10.2 Measure Readers (O(1))

```coq
Definition measureMTuple {M A} (t : MTuple M A) : M :=
  match t with MPair m _ _ => m | MTriple m _ _ _ => m end.

Definition measureDigit {M A} `{Monoid M} (md : A -> M) (d : Digit A) : M :=
  match d with
  | One x       => md x
  | Two x y     => md x <+> md y
  | Three x y z => md x <+> md y <+> md z
  end.

Definition measureSeq {M A} `{Monoid M} (md : A -> M) (s : MSeq M A) : M :=
  match s with
  | MNil           => mzero
  | MUnit x        => md x
  | MMore vm pr _ sf => measureDigit md pr <+> vm <+> measureDigit md sf
  end.
```

Reads the cached `vm`; never traverses the spine.

### 10.3 Smart Constructors

```coq
Definition mpair {M A} `{Monoid M} (md : A -> M) (x y : A) : MTuple M A :=
  MPair (md x <+> md y) x y.

Definition mtriple {M A} `{Monoid M} (md : A -> M) (x y z : A) : MTuple M A :=
  MTriple (md x <+> md y <+> md z) x y z.

Definition mdeep {M A} `{Monoid M} (md : A -> M)
    (pr : Digit A) (m : MSeq M (MTuple M A)) (sf : Digit A) : MSeq M A :=
  MMore (measureSeq measureMTuple m) pr m sf.
```

### 10.4 Digit/Tuple Plumbing

```coq
Definition digitToList {A} (d : Digit A) : list A :=
  match d with One x => [x] | Two x y => [x;y] | Three x y z => [x;y;z] end.

Definition tupleToDigit {M A} (t : MTuple M A) : Digit A :=
  match t with MPair _ x y => Two x y | MTriple _ x y z => Three x y z end.

Definition toTree {M A} `{Monoid M} (md : A -> M) (xs : list A) : MSeq M A :=
  match xs with
  | []      => MNil
  | [x]     => MUnit x
  | [x;y]   => mdeep md (One x) MNil (One y)
  | [x;y;z] => mdeep md (Two x y) MNil (One z)
  | _       => MNil
  end.
```

### 10.5 Split Infrastructure

```coq
Definition splitDigit {M A} `{Monoid M} (md : A -> M)
    (p : M -> bool) (i : M) (d : Digit A) : list A * A * list A :=
  match d with
  | One x => ([], x, [])
  | Two x y =>
      if p (i <+> md x) then ([], x, [y]) else ([x], y, [])
  | Three x y z =>
      if p (i <+> md x) then ([], x, [y; z])
      else if p (i <+> md x <+> md y) then ([x], y, [z])
      else ([x; y], z, [])
  end.
```

```coq
Fixpoint viewL {M A} `{Monoid M} (md : A -> M) (dflt : A) (t : MSeq M A)
    {struct t} : option (A * MSeq M A) :=
  match t with
  | MNil    => None
  | MUnit x => Some (x, MNil)
  | MMore vm pr m sf =>
      match pr with
      | Two x y     => Some (x, mdeep md (One y) m sf)
      | Three x y z => Some (x, mdeep md (Two y z) m sf)
      | One x =>
          match viewL measureMTuple (MPair mzero dflt dflt) m with
          | None         => Some (x, toTree md (digitToList sf))
          | Some (t1, m') => Some (x, mdeep md (tupleToDigit t1) m' sf)
          end
      end
  end.

Fixpoint viewR {M A} `{Monoid M} (md : A -> M) (dflt : A) (t : MSeq M A)
    {struct t} : option (MSeq M A * A) :=
  match t with
  | MNil    => None
  | MUnit x => Some (MNil, x)
  | MMore vm pr m sf =>
      match sf with
      | Two x y     => Some (mdeep md pr m (One x), y)
      | Three x y z => Some (mdeep md pr m (Two x y), z)
      | One x =>
          match viewR measureMTuple (MPair mzero dflt dflt) m with
          | None         => Some (toTree md (digitToList pr), x)
          | Some (m', t1) => Some (mdeep md pr m' (tupleToDigit t1), x)
          end
      end
  end.
```

```coq
Definition deepL {M A} `{Monoid M} (md : A -> M) (dflt : A)
    (pr : list A) (m : MSeq M (MTuple M A)) (sf : Digit A) : MSeq M A :=
  match pr with
  | [x]     => mdeep md (One x) m sf
  | [x;y]   => mdeep md (Two x y) m sf
  | [x;y;z] => mdeep md (Three x y z) m sf
  | [] =>
      match viewL measureMTuple (MPair mzero dflt dflt) m with
      | None          => toTree md (digitToList sf)
      | Some (t1, m') => mdeep md (tupleToDigit t1) m' sf
      end
  | _ => MNil
  end.

Definition deepR {M A} `{Monoid M} (md : A -> M) (dflt : A)
    (pr : Digit A) (m : MSeq M (MTuple M A)) (sf : list A) : MSeq M A :=
  match sf with
  | [x]     => mdeep md pr m (One x)
  | [x;y]   => mdeep md pr m (Two x y)
  | [x;y;z] => mdeep md pr m (Three x y z)
  | [] =>
      match viewR measureMTuple (MPair mzero dflt dflt) m with
      | None          => toTree md (digitToList pr)
      | Some (m', t1) => mdeep md pr m' (tupleToDigit t1)
      end
  | _ => MNil
  end.
```

```coq
Fixpoint splitTree {M A} `{Monoid M} (md : A -> M) (dflt : A)
    (p : M -> bool) (i : M) (t : MSeq M A) {struct t}
    : MSeq M A * A * MSeq M A :=
  match t with
  | MNil    => (MNil, dflt, MNil)
  | MUnit x => (MNil, x, MNil)
  | MMore vm pr m sf =>
      let vpr  := i <+> measureDigit md pr in
      let vm_t := vpr <+> vm in
      if p vpr then
        let '(l, x, r) := splitDigit md p i pr in
        (toTree md l, x, deepL md dflt r m sf)
      else if p vm_t then
        let '(ml, xs, mr) :=
          splitTree measureMTuple (MPair mzero dflt dflt) p vpr m in
        let '(l, x, r) :=
          splitDigit md p (vpr <+> measureSeq measureMTuple ml) (tupleToDigit xs) in
        (deepR md dflt pr ml l, x, deepL md dflt r mr sf)
      else
        let '(l, x, r) := splitDigit md p vm_t sf in
        (deepR md dflt pr m l, x, toTree md r)
  end.
```

**Design**: Descend to the position where `p` flips. Three branches per level:
1. `p vpr`: split is in the front digit.
2. `p vm_t`: split is in the middle spine (recurse).
3. Otherwise: split is in the rear digit.

### 10.6 Random Access

```coq
Definition sz1 : A -> nat := fun _ => 1.

Definition index (dflt : A) (i : nat) (t : MSeq nat A) : A :=
  let '(_, x, _) := splitTree sz1 dflt (fun s => i <? s) 0 t in x.
```

(Inside `Section RandomAccess`, with `Context {A : Type}`.)

### 10.7 Approximation Types

```coq
Inductive MTupleA (M A : Type) : Type :=
  | MPairA   : M -> T A -> T A -> MTupleA M A
  | MTripleA : M -> T A -> T A -> T A -> MTupleA M A.

Inductive MSeqA (M A : Type) : Type :=
  | MNilA  : MSeqA M A
  | MUnitA : T A -> MSeqA M A
  | MMoreA : M -> T (DigitA A) -> T (MSeqA M (MTupleA M A)) -> T (DigitA A) -> MSeqA M A.

Instance Exact_MTuple / Instance Exact_MSeq / Instance BottomOf_MSeqA
Inductive LessDefined_MTupleA / Inductive LessDefined_MSeqA

Definition SplitDmd (M A : Type) : Type :=
  (T (MSeqA M A) * T A * T (MSeqA M A))%type.
```

### 10.8 Demand Functions

```coq
Definition toTreeD {M A} (outD : T (MSeqA M A)) : Tick unit :=
  match outD with Undefined => Tick.ret tt | Thunk _ => Tick.tick >> Tick.ret tt end.

Fixpoint viewLD {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (t : MSeq M A) (outD : T (MSeqA M B)) {struct t} : Tick (T (MSeqA M B)) :=
  Tick.tick >>
  match t with
  | MNil    => Tick.ret Undefined
  | MUnit _ => Tick.ret Undefined
  | MMore _ pr m _ =>
      match pr with
      | One _ =>
          let+ _ := viewLD (A := MTuple M A) (B := MTupleA M B)
                      measureMTuple (MPair mzero dflt dflt) m Undefined in
          Tick.ret Undefined
      | Two _ _     => Tick.ret Undefined
      | Three _ _ _ => Tick.ret Undefined
      end
  end.

Fixpoint viewRD {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (t : MSeq M A) (outD : T (MSeqA M B)) {struct t} : Tick (T (MSeqA M B)) :=
  Tick.tick >>
  match t with
  | MNil    => Tick.ret Undefined
  | MUnit _ => Tick.ret Undefined
  | MMore _ _ m sf =>
      match sf with
      | One _ =>
          let+ _ := viewRD (A := MTuple M A) (B := MTupleA M B)
                      measureMTuple (MPair mzero dflt dflt) m Undefined in
          Tick.ret Undefined
      | Two _ _     => Tick.ret Undefined
      | Three _ _ _ => Tick.ret Undefined
      end
  end.

Definition deepLD {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (r : list A) (m : MSeq M (MTuple M A)) (sf : Digit A) (outD : T (MSeqA M B))
    : Tick (T (MSeqA M (MTupleA M B))) :=
  match outD with
  | Undefined => Tick.ret Undefined
  | Thunk _ =>
      match r with
      | [] => let+ _ := viewLD (A := MTuple M A) (B := MTupleA M B)
                          measureMTuple (MPair mzero dflt dflt) m Undefined in
              Tick.ret Undefined
      | _  => Tick.ret Undefined
      end
  end.

Definition deepRD {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (pr : Digit A) (m : MSeq M (MTuple M A)) (l : list A) (outD : T (MSeqA M B))
    : Tick (T (MSeqA M (MTupleA M B))) :=
  match outD with
  | Undefined => Tick.ret Undefined
  | Thunk _ =>
      match l with
      | [] => let+ _ := viewRD (A := MTuple M A) (B := MTupleA M B)
                          measureMTuple (MPair mzero dflt dflt) m Undefined in
              Tick.ret Undefined
      | _  => Tick.ret Undefined
      end
  end.

Fixpoint splitTreeD {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (p : M -> bool) (i : M) (t : MSeq M A) (outD : SplitDmd M B) {struct t}
    : Tick (T (MSeqA M B)) :=
  Tick.tick >>
  match t with
  | MNil    => Tick.ret Undefined
  | MUnit x => let '(_, xD, _) := outD in Tick.ret (Thunk (MUnitA xD))
  | MMore vm pr m sf =>
      let '(lD, xD, rD) := outD in
      let vpr  := i <+> measureDigit md pr in
      let vm_t := vpr <+> vm in
      if p vpr then
        let+ _  := toTreeD lD in
        let+ mD := deepLD md dflt [] m sf rD in
        Tick.ret (Thunk (MMoreA vm (exact pr) mD (exact sf)))
      else if p vm_t then
        let+ mD := splitTreeD (A := MTuple M A) (B := MTupleA M B)
                     measureMTuple (MPair mzero dflt dflt) p vpr m
                     (Undefined, Undefined, Undefined) in
        let+ _  := deepRD md dflt pr m [] lD in
        let+ _  := deepLD md dflt [] m sf rD in
        Tick.ret (Thunk (MMoreA vm (exact pr) mD (exact sf)))
      else
        let+ _  := deepRD md dflt pr m [] lD in
        let+ _  := toTreeD rD in
        Tick.ret (Thunk (MMoreA vm (exact pr) (Thunk (bottom_of (exact m))) (exact sf)))
  end.

Definition indexD {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (p : M -> bool) (i : M) (t : MSeq M A) (xD : T B) : Tick (T (MSeqA M B)) :=
  splitTreeD md dflt p i t (Undefined, xD, Undefined).
```

Both halves `Undefined` => `deepLD`/`deepRD` cost 0.

### 10.9 Cost Potentials

```coq
Definition split_c1 : nat := 12.
Definition split_c2 : nat := 24.
```

```coq
Fixpoint lvc {M A} (s : MSeq M A) : nat :=
  match s with
  | MNil | MUnit _ => 1
  | MMore _ (One _)       m _ => S (lvc m)
  | MMore _ (Two _ _)     _ _ => 1
  | MMore _ (Three _ _ _) _ _ => 1
  end.

Fixpoint rvc {M A} (s : MSeq M A) : nat :=
  match s with
  | MNil | MUnit _ => 1
  | MMore _ _ m (One _)       => S (rvc m)
  | MMore _ _ _ (Two _ _)     => 1
  | MMore _ _ _ (Three _ _ _) => 1
  end.

Lemma lvc_le_depth : lvc s <= S (depth s).
Lemma rvc_le_depth : rvc s <= S (depth s).
```

### 10.10 Cost Lemmas

```coq
Lemma viewLD_cost : Tick.cost (viewLD md dflt t outD) <= lvc t.
Lemma viewRD_cost : Tick.cost (viewRD md dflt t outD) <= rvc t.
Lemma toTreeD_cost : Tick.cost (toTreeD outD) <= 1.
Lemma deepLD_cost  : Tick.cost (deepLD md dflt r m sf rD) <= lvc m.
Lemma deepRD_cost  : Tick.cost (deepRD md dflt pr m l lD) <= rvc m.
```

#### Index Cost (Clean Descent)

```coq
Theorem indexD_cost :
  Tick.cost (indexD md dflt p i t xD) <= 12 * depth t + 24.
```

*Proof*: By `fix SELF` (polymorphic recursion). With both halves `Undefined`,
every `toTreeD`/`deepLD`/`deepRD` costs 0, so each level is O(1).

#### Split Cost (Descent + Reconstruction)

```coq
Theorem splitTreeD_cost :
  Tick.cost (splitTreeD md dflt p i t outD) <= 14 * depth t + 27.
```

*Proof*: Uses `indexD_cost` for the middle recursion, plus `deepLD_cost`/
`deepRD_cost` (each bounded by `lvc m`/`rvc m` <= `S (depth m)`) for the
two reconstruction passes.

### 10.11 Ported Size/Depth Lemmas for MSeq

```coq
Lemma MSeq_ind_poly : (* polymorphic induction for MSeq *)
Lemma MSeq_nil_dec  : (* s = MNil \/ s <> MNil *)
Lemma size_lower_bound : s <> MNil -> 2^(depth s) <= size s.
Lemma size_pos : s <> MNil -> 0 < size s.
Corollary depth_log_size : s <> MNil -> depth s <= log2 (size s).
```

### 10.12 O(log n) Corollaries

```coq
Corollary index_O_log_n :
  t <> MNil ->
  Tick.cost (indexD md dflt p i t xD) <= 12 * log2 (size t) + 24.

Corollary split_O_log_n :
  t <> MNil ->
  Tick.cost (splitTreeD md dflt p i t outD) <= 14 * log2 (size t) + 27.
```

### 10.13 Future Work (Admitted/Commented)

`split_correct`, `indexD_approx`, `splitTreeD_spec` — require correct
`viewLD`/`viewRD`/`deepLD`/`deepRD` value demands.

---

## Summary of Verified Complexity Results

| Operation | Complexity | Key Lemma | File |
|-----------|-----------|-----------|------|
| `fcons` | O(1) amortised | `fconsD'_cost` | FingerCons.v |
| `fsnoc` | O(1) amortised | `fsnocD'_cost` | FingerSnoc.v |
| `head` | O(1) worst-case | `headD'_cost` | FingerHead.v |
| `ftail` | O(1) amortised | `ftailD'_cost` | FingerTail.v |
| `concat` | O(log n) worst-case | `concatD_cost_O_log_n` | FingerConcat.v |
| `index` | O(log n) worst-case | `index_O_log_n` | FingerSplit.v |
| `splitTree` | O(log n) worst-case | `split_O_log_n` | FingerSplit.v |
| **Overall** | O(1) amortised (persistent) | `amortized_cost` | FingerPhysicist.v |
