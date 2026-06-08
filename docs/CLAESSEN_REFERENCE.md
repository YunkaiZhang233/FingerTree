# CLAESSEN_REFERENCE.md — Pure Specification

Reference for the pure finger tree operations as implemented in `Finger.v`. This file reflects the **actual code** in the project, not the original aspirational design.

## Types

```coq
Inductive Digit (A : Type) : Type :=
  | One   : A -> Digit A
  | Two   : A -> A -> Digit A
  | Three : A -> A -> A -> Digit A.

Inductive Tuple (A : Type) : Type :=
  | Pair   : A -> A -> Tuple A
  | Triple : A -> A -> A -> Tuple A.

Inductive Seq (A : Type) : Type :=
  | Nil  : Seq A
  | Unit : A -> Seq A
  | More : Digit A -> Seq (Tuple A) -> Digit A -> Seq A.
```

The middle field of `More` is polymorphic recursion at `Tuple A`. In the lazy / approximate version (`SeqA`), this field is wrapped in `T`.

`Digit` corresponds to Claessen's `Some`; renamed to avoid clashing with `option`'s `Some`. **Safe** = `Two`. **Dangerous** = `One`, `Three`.

## Implemented Pure Operations

### `fcons` (front cons / Claessen's `cons`)

```coq
Fixpoint fcons (A : Type) (x : A) (s : Seq A) : Seq A :=
  match s with
  | Nil => Unit x
  | Unit y => More (One x) Nil (One y)
  | More (One a) m r => More (Two x a) m r
  | More (Two a b) m r => More (Three x a b) m r
  | More (Three a b c) m r => More (Two x a) (fcons (Pair b c) m) r
  end.
```

Cost: 1 step per call; recurses only on the Three-front case. Amortised O(1).

### `head`

```coq
Definition head (A : Type) (s : Seq A) : option A :=
  match s with
  | Nil => None
  | Unit x => Some x
  | More (One x) _ _ => Some x
  | More (Two x _) _ _ => Some x
  | More (Three x _ _) _ _ => Some x
  end.
```

Pure projection; O(1) worst case, no recursion.

### `empty`

```coq
Definition empty (A : Type) : Seq A := Nil.
```

## To Be Implemented: `tail`

The next operation to verify. See `TAIL_ANALYSIS.md` for full design.

Pure definition (inline-style, no `deep0`):

```coq
Fixpoint tail (A : Type) (s : Seq A) : Seq A :=
  match s with
  | Nil => Nil                                    (* total: tail Nil = Nil *)
  | Unit _ => Nil
  | More (Three _ x y) m r => More (Two x y) m r  (* no recursion *)
  | More (Two _ x) m r => More (One x) m r        (* no recursion *)
  | More (One _) m r =>                           (* cascade *)
      match m with
      | Nil =>                                     (* reshape r *)
          match r with
          | One y => Unit y
          | Two y z => More (One y) Nil (One z)
          | Three y z w => More (One y) Nil (Two z w)
          end
      | _ =>                                       (* head m drives the choice *)
          match head m with
          | Some (Pair x y) => More (Two x y) (tail m) r          (* recurse *)
          | Some (Triple x _ _) => More (One x) (map1 chop_triple m) r  (* no recursion *)
          | None => Nil  (* unreachable *)
          end
      end
  end.
```

Cost: 1 step per call; recurses only on the (One-front, non-empty m, Pair-head) case. Amortised O(1).

### Helpers needed

```coq
Definition chop_triple {A : Type} (t : Tuple A) : Tuple A :=
  match t with
  | Triple _ y z => Pair y z
  | Pair x y => Pair x y    (* unreachable; total dummy *)
  end.

Definition map1 {A : Type} (f : A -> A) (s : Seq A) : Seq A :=
  match s with
  | Nil => Nil
  | Unit x => Unit (f x)
  | More (One x) m r => More (One (f x)) m r
  | More (Two x y) m r => More (Two (f x) y) m r
  | More (Three x y z) m r => More (Three (f x) y z) m r
  end.
```

`map1` may already be implemented; check the existing pure section of `Finger.v` before duplicating.

## Out of Scope

The following are **not** implemented in the Coq development; their correctness follows by symmetry from the implemented operations and is discussed in the thesis prose only:

- `snoc` (symmetric to `fcons`)
- `last` (symmetric to `head`)
- `init` / `unsnoc` (symmetric to `tail` / `uncons`)
- Combined `uncons : Seq A → option (A * Seq A)` returning both head and tail simultaneously

The decision to verify `head` and `tail` separately (rather than a combined `uncons`) avoided having to handle `option (A * Seq A)` and the associated `prodA` / `optionA` machinery on the output side of the demand semantics. This keeps demand functions returning simple `Tick (T (SeqA A))`.

## Worked Examples (sanity checks)

Confirm `tail` matches expectations on small inputs:

| Input | Expected output | Cascades? |
|---|---|---|
| `Nil` | `Nil` | no |
| `Unit a` | `Nil` | no |
| `More (Three a x y) m r` | `More (Two x y) m r` | no |
| `More (Two a x) m r` | `More (One x) m r` | no |
| `More (One a) Nil (One y)` | `Unit y` | no (m empty) |
| `More (One a) Nil (Two y z)` | `More (One y) Nil (One z)` | no (m empty) |
| `More (One a) Nil (Three y z w)` | `More (One y) Nil (Two z w)` | no (m empty) |
| `More (One a) (Unit (Pair b c)) (One e)` | `More (Two b c) Nil (One e)` | **yes** (Pair head; recurse → `tail (Unit (Pair b c)) = Nil`) |
| `More (One a) (Unit (Triple b c d)) (One e)` | `More (One b) (Unit (Pair c d)) (One e)` | no (Triple head; chop) |

The Triple-head case avoids recursion entirely — Claessen's key optimisation. The Pair-head case is the only structurally recursive site.

## Approximation Types

These are in place in `Finger.v` Section 2:

```coq
Inductive DigitA (A : Type) : Type :=
  | OneA   : T A -> DigitA A
  | TwoA   : T A -> T A -> DigitA A
  | ThreeA : T A -> T A -> T A -> DigitA A.

Inductive TupleA (A : Type) : Type :=
  | PairA   : T A -> T A -> TupleA A
  | TripleA : T A -> T A -> T A -> TupleA A.

Inductive SeqA (A : Type) : Type :=
  | NilA  : SeqA A
  | UnitA : T A -> SeqA A
  | MoreA : T (DigitA A) -> T (SeqA (TupleA A)) -> T (DigitA A) -> SeqA A.
```

No `bot` constructor at any level. Bottom is represented by `Undefined` at the `T` level.

Full lattice instances (`LessDefined`, `Reflexive`, `Transitive`, `PreOrder`, `Antisym`, `PartialOrder`, `Exact`, `ExactMaximal`, `Lub`, `LubLaw`) exist for all three. `Exact_Seq` and `Lub_SeqA` are polymorphic `fix`es to handle the type-changing recursion at `MoreA`.

## Potential Function

```coq
Definition safe_DigitA {A : Type} (dA : DigitA A) : nat :=
  match dA with
  | OneA _ => 0
  | TwoA _ _ => 1
  | ThreeA _ _ _ => 0
  end.

Definition safe_T {A : Type} (fD : T (DigitA A)) : nat :=
  match fD with
  | Thunk d => safe_DigitA d
  | Undefined => 1
  end.

Instance Debitable_SeqA : forall A, Debitable (SeqA A) :=
  fix debt_SeqA (A : Type) (sA : SeqA A) :=
    match sA with
    | NilA => 0
    | UnitA _ => 0
    | MoreA fD mD rD =>
        safe_T fD + @Debitable_T _ (debt_SeqA _) mD + safe_T rD
    end.
```

This is the **safe** convention (Two contributes potential because the next operation is cheap, dangerous digits contribute 0). The original Claessen analysis uses the symmetric **danger** convention (One/Three = 1, Two = 0). Both work; we picked safe because it makes `fconsD'_cost` cleaner.

## Naming Convention

- `f` prefix for definitions on the pure `Seq` (e.g., `fcons` to avoid clashing with `List`'s `cons`).
- Plain names for queries (`head`, `tail`).
- `A` suffix for approximation-type operations (`fconsA`, `headA`, `tailA`).
- `D'` suffix for "raw" demand functions on pure `Seq A` and approximation `SeqA B` (e.g., `fconsD'`).
- `D` (no prime) suffix for the corollary specialised at `B := A` (e.g., `fconsD`).
- `_approx`, `_spec`, `_cost` for the three standard proofs.