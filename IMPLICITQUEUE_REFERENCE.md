# ImplicitQueue.v Reference Guide

This document summarises the structure of ImplicitQueue.v from Xia et al. (ICFP 2024) for reference when developing FingerTree.v. It explains what each section does and how to adapt it.

## 1. Pure Types (adapt completely)

ImplicitQueue.v defines:
```coq
Inductive Front (A : Type) :=
  | FOne  : A -> Front A
  | FTwo  : A -> A -> Front A.

Inductive Rear (A : Type) :=
  | RZero : Rear A
  | ROne  : A -> Rear A.

Inductive Queue (A : Type) :=
  | Shallow : option A -> Queue A
  | Deep    : Front A -> Queue (A * A) -> Rear A -> Queue A.
```

**FingerTree.v replacement**: `Digit` (One/Two/Three), `Seq` (Nil/Unit/More).

## 2. Approximation Types (adapt, biggest section)

### 2a. Define approximated types

For each pure type, add a bottom element:
```coq
(* ImplicitQueue.v pattern *)
Inductive FrontA (A : Type) :=
  | FOneA  : A -> FrontA A
  | FTwoA  : A -> A -> FrontA A
  | FrontBot : FrontA A.
```

For the recursive type, the middle field gets wrapped in `T`:
```coq
Inductive QueueA (A : Type) :=
  | ShallowA : option A -> QueueA A
  | DeepA    : FrontA A -> T (QueueA (prodA A A)) -> RearA A -> QueueA A
  | QueueBot : QueueA A.
```

**Key**: `T` is the thunk approximation type from `Core.v`. `T X` is either `Thunk x` (with approximation `x : X`) or `Undefined` (unknown/not yet demanded).

### 2b. LessDefined (approximation ordering)

Define as an inductive relation. Pattern:
- Bottom is below everything
- Matching constructors are compared pointwise
- Different constructors are incomparable

```coq
Instance LessDefined_FrontA {A} `{LessDefined A} : LessDefined (FrontA A) :=
  { less_defined := LessDefinedFrontA }.
```

Then prove `Reflexive`, `Transitive`, `PreOrder`, `PartialOrder`.

### 2c. Exact (embedding pure into approximated)

```coq
Instance Exact_FrontA {A EA} `{Exact A EA} : Exact (Front A) (FrontA EA) :=
  { exact f := match f with
               | FOne x => FOneA (exact x)
               | FTwo x y => FTwoA (exact x) (exact y)
               end }.
```

### 2d. BottomOf

```coq
Instance BottomOf_FrontA {A} : BottomOf (FrontA A) :=
  { bottom := FrontBot }.
```

### 2e. Lub (least upper bound)

Define a function computing the lub, then prove it satisfies the `LubLaw` spec. Lub of incompatible constructors returns one of them (the spec only requires it to be an upper bound).

### 2f. Custom induction principle (CRITICAL)

Rocq generates a weak induction principle for `QueueA` because of the nested `QueueA (prodA A A)`. The artifact writes `QueueA_ind` manually (~50 lines).

**Pattern for SeqA_ind**:
```coq
Section SeqA_rect.
  Variable A : Type.
  Variable P : SeqA A -> Type.

  Hypothesis H_NilA  : P NilA.
  Hypothesis H_UnitA : forall a, P (UnitA a).
  Hypothesis H_MoreA : forall f (m : T (SeqA (prodA A A))) r,
    (forall s, m = Thunk s -> P_nested s) ->
    P (MoreA f m r).
  Hypothesis H_SeqBot : P SeqBot.

  (* P_nested handles the nested type *)
  ...
End SeqA_rect.
```

The key trick: universally quantify over the element type at the top level, then instantiate with `prodA A A` for the recursive case.

## 3. Demand Functions (adapt)

### Pattern for consD' (analogous to pushD')

The demand function takes:
1. The element being inserted
2. The input approximation
3. The output demand (what the caller needs from the result)

And returns: a `Tick` of the input demand (what we need from the input, plus cost).

```coq
Fixpoint pushD' {A} `{Exact A (EA A)}
  (x : A) (q : QueueA (EA A)) (outD : QueueA (EA A))
  : Tick (QueueA (EA A)) :=
  match outD with
  | QueueBot => Tick.ret QueueBot  (* caller needs nothing *)
  | ShallowA _ => ...              (* base cases *)
  | DeepA fD mD rD => ...          (* recursive cases *)
  end.
```

**Key operations in demand functions**:
- `Tick.ret x` — return with 0 cost
- `Tick.tick >> e` — 1 unit of cost, then continue with `e`
- `let~ x := e1 in e2` — bind (monadic sequencing, adds costs)
- `optimistic_thunk` — for thunks that might not be forced (assume best case)
- `Thunk x` / `Undefined` — constructing thunk approximations

### Pattern for unconsD' (analogous to popD')

Similar but handles the "pull from middle" case:
- When front digit is large enough: just shrink it, don't touch middle
- When front digit is `One`: force the middle thunk, extract a pair, create new suspension for `tail` of middle

## 4. Approximation Proofs (mostly mechanical)

For each demand function, prove:
```coq
Lemma consD'_approx : forall x s outD,
  outD ⊑ exact (cons x (IsExact_SeqA s)) ->
  consD' x (exact s) outD ⊑ exact s.
```

Proof technique: induction on the structure, case split on digit sizes, use `teardown`, `mgo_`, `keep_mgo_`.

## 5. Cost Proofs (the interesting part)

### Potential function
```coq
Fixpoint potential {A} (s : SeqA A) : nat :=
  match s with
  | SeqBot    => 0
  | NilA      => 0
  | UnitA _   => 0
  | MoreA f m r =>
      digit_potential f + digit_potential r +
      match m with
      | Thunk m' => potential m'
      | Undefined => 0
      end
  end.
```

### Amortised cost theorem
```coq
Theorem cons_amortised : forall x s outD,
  cost (consD' x s outD) + potential (value (consD' x s outD))
  <= potential s + C.
```
where `C` is a small constant (2 or 3).

## 6. Useful Library Types and Functions

From `Core.v`:
- `T A` — thunk type (`Thunk a | Undefined`)
- `prodA A B` — approximated product

From `Tick.v`:
- `Tick A` — computation with cost: `{ cost : nat; value : A }`
- `Tick.ret`, `Tick.bind`, `Tick.tick`

From `Approx.v`:
- `LessDefined`, `Exact`, `BottomOf`, `Lub`, `LubLaw`
- `less_defined` (the `⊑` notation)

From `ApproxM.v`:
- `mgo_` — tactic for monotonicity goals
- `optimistic_thunk`, `optimistic_thunk_go`, `optimistic_skip`

## 7. Common Pitfalls

1. **Termination checker**: `Fixpoint` through non-regular types (`Seq (A*A)`) can confuse the termination checker. If `Fixpoint` doesn't work, try `Function` with `{measure ...}` or restructure the recursion.

2. **Universe polymorphism**: The `Exact` typeclass can trigger universe issues. Use `#[local] Existing Instance Exact_id | 1.` at the top.

3. **prodA vs prod**: The approximated product `prodA` is NOT the same as Coq's built-in `prod`. Don't confuse them. Pure functions use `(A * A)`, approximated versions use `prodA A A`.

4. **Implicit arguments**: Set them immediately after each inductive definition with `Arguments`. Follow the artifact's convention.

5. **The `XXX` pattern in demand functions**: The artifact has comments marking design choices as slightly hacky. Don't be alarmed — these are acknowledged compromises in the framework, not bugs.
