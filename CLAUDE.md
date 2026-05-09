# CLAUDE.md — Finger Tree Formal Verification Project

## Project Overview

This is a **MEng thesis project** formally verifying the amortised time complexity of **Claessen's 2020 simplified finger tree** (a persistent deque) using the **bidirectional demand semantics** framework from Xia et al. (ICFP 2024).

The goal: prove that `cons`, `snoc`, `uncons` (head+tail), and `unsnoc` (last+init) all run in **O(1) amortised time**, even under persistent use, using the Rocq Prover (Coq).

## Key References

- **Data structure**: Koen Claessen, "Finger trees explained anew, and slightly simplified" (Haskell Symposium 2020)
- **Verification framework**: Li-yao Xia et al., "Story of Your Lazy Function's Life: A Bidirectional Demand Semantics for Mechanized Cost Analysis of Lazy Programs" (ICFP 2024)
- **Template file**: `ImplicitQueue.v` from the ICFP 2024 artifact (branch `icfp24-artifact` of `github.com/lastland/ClairvoyanceMonad`)
- **Library**: The `Clairvoyance` Rocq library (installed via opam as part of the artifact)

## The Data Structure (Claessen 2020, Try 5)

```haskell
-- Haskell reference (paper's final version, Section 8)
data Seq a   = Nil | Unit a | More (Some a) (Seq (Tuple a)) (Some a)
data Some a  = One a | Two a a | Three a a a
data Tuple a = Pair a a | Triple a a a
```

We rename `Some` to `Digit` in Coq to avoid clashing with `option`'s `Some`.

Key properties:
- `Digit` (paper's `Some`) holds 1–3 elements at the fingers. `Two` is "safe", `One` and `Three` are "dangerous"
- `Tuple` holds 2–3 elements in the recursive spine. `Pair` and `Triple` play different roles in `tail`
- The middle field `Seq (Tuple a)` is **polymorphic recursion** — each level stores tuples of the level below
- In the lazy version, the middle field is wrapped in a **thunk** (suspension)
- This is a **deque**: both ends support insertion and deletion
- `tail` has a three-way branch when pulling from the middle: empty / Pair (recurse) / Triple (chop, no recursion)
- The `chop`/`map1` pattern for Triples is Claessen's key insight — it avoids recursion when possible

See `CLAESSEN_REFERENCE.md` for the complete function-by-function specification.

## Relationship to ImplicitQueue.v

The finger tree is a generalisation of Okasaki's implicit queue:

| Aspect | ImplicitQueue | FingerTree (this project) |
|--------|--------------|--------------------------|
| Front digit | `One \| Two` (1–2) | `One \| Two \| Three` (1–3) |
| Rear digit | `Zero \| One_r` (0–1) | `One \| Two \| Three` (1–3) |
| Spine element | `A * A` (pairs) | `Tuple A` (Pair/Triple) |
| Safe digits | — | `Two` |
| Dangerous | all | `One`, `Three` |
| Operations | push (snoc), pop (uncons) | cons, snoc, uncons, unsnoc |
| Base cases | `Shallow (option A)` | `Nil \| Unit A` |
| tail cascade | always recurses | Pair → recurse, Triple → chop (no recursion) |
| Extra helpers | — | `map1`, `chop`, `mapLast`, `chopLast` |

The proof structure is **identical** — follow ImplicitQueue.v section by section, adapting for wider digits, the Tuple type, and symmetric operations.

## File Structure

The main file is `theories/FingerTree.v` (or just `FingerTree.v` depending on project layout). It follows ImplicitQueue.v's structure:

### Section 1: Pure Definitions (~done)
- `Digit`, `Tuple`, `Seq` inductive types
- Helper functions: `map1`, `mapLast`, `chop`, `chopLast`
- Pure operations: `cons`, `snoc`, `uncons`, `unsnoc`, `head`, `last`, `tail`, `init`
- `toList` / `toListWith` for functional correctness specification

### Section 2: Approximation Types & Lattice Boilerplate (~600+ lines)
- `DigitA` — approximated digit with a `DigitBot` constructor
- `TupleA` — approximated tuple with a `TupleBot` constructor
- `SeqA` — approximated sequence with `SeqBot` constructor, middle wrapped in `T` (thunk)
- For each of `DigitA`, `SeqA`: instances for `LessDefined`, `Reflexive`, `Transitive`, `PreOrder`, `PartialOrder`, `Exact`, `BottomOf`, `Lub`, `LubLaw`
- **Critical**: `SeqA` requires a hand-written custom induction principle (`SeqA_ind`) because Rocq's auto-generated one doesn't handle `SeqA (prodA A A)` nesting

### Section 3: Demand Functions (~200 lines)
- `consD'`, `snocD'` — demand functions for insertion
- `unconsD'`, `unsnocD'` — demand functions for removal
- These mirror the pure operations but track cost via `Tick` and compute input demands from output demands

### Section 4: Approximation Proofs (~300 lines)
- `consD'_approx`, `unconsD'_approx`, etc.
- Prove that demand functions compute valid approximations

### Section 5: Cost Proofs / Physicist's Argument (~300 lines)
- Potential function on `SeqA`
- Amortised cost theorems: `cost + Φ_new ≤ Φ_old + O(1)`

### Section 6: Persistence (stretch goal)
- Extends to persistent use via `LubLaw` and monotonicity

## Key Patterns from ImplicitQueue.v to Follow

### Approximation types
For every pure constructor, add a `Bot` constructor:
```coq
(* Pure *)
Inductive Digit (A : Type) := One | Two | Three.

(* Approximated *)
Inductive DigitA (A : Type) :=
  | OneA : A -> DigitA A
  | TwoA : A -> A -> DigitA A
  | ThreeA : A -> A -> A -> DigitA A
  | DigitBot : DigitA A.

(* Pure *)
Inductive Tuple (A : Type) := Pair | Triple.

(* Approximated *)
Inductive TupleA (A : Type) :=
  | PairA : A -> A -> TupleA A
  | TripleA : A -> A -> A -> TupleA A
  | TupleBot : TupleA A.
```

### The thunk wrapper
The middle field in `SeqA` uses `T` (the thunk type from the library):
```coq
Inductive SeqA (A : Type) :=
  | NilA  : SeqA A
  | UnitA : A -> SeqA A
  | MoreA : DigitA A -> T (SeqA (TupleA A)) -> DigitA A -> SeqA A
  | SeqBot : SeqA A.
```

### LessDefined instances
Pattern: `Bot ⊑ anything`, then pointwise on matching constructors:
```coq
Inductive LessDefinedDigitA {A} `{LessDefined A} : DigitA A -> DigitA A -> Prop :=
  | LD_DigitBot : forall d, LessDefinedDigitA DigitBot d
  | LD_OneA : forall x y, x ⊑ y -> LessDefinedDigitA (OneA x) (OneA y)
  | LD_TwoA : forall x1 x2 y1 y2, x1 ⊑ y1 -> x2 ⊑ y2 ->
      LessDefinedDigitA (TwoA x1 x2) (TwoA y1 y2)
  | LD_ThreeA : forall x1 x2 x3 y1 y2 y3, x1 ⊑ y1 -> x2 ⊑ y2 -> x3 ⊑ y3 ->
      LessDefinedDigitA (ThreeA x1 x2 x3) (ThreeA y1 y2 y3).
```

### Custom induction principle for SeqA
Rocq's auto-generated induction principle for `SeqA` won't handle the nested `SeqA (prodA A A)`. You must write `SeqA_ind` by hand, following the pattern of `QueueA_ind` in ImplicitQueue.v. The key is to universally quantify over the type parameter and thread the inductive hypothesis through the `T` wrapper and `prodA` nesting.

### Demand functions
Use `Tick` monad for cost, `optimistic_thunk` for thunks that might not be forced:
```coq
(* Skeleton for consD' *)
Fixpoint consD' {A} `{Exact A (EA A)}
  (x : A) (s : SeqA (EA A)) (outD : SeqA (EA A))
  : Tick (SeqA (EA A)) := ...
```

### Potential function
For the deque, potential should measure digit "buffer" at each level:
```coq
(* digit_potential (OneA _) = 0 *)
(* digit_potential (TwoA _ _) = 1 *)
(* digit_potential (ThreeA _ _ _) = 2 *)
(* digit_potential DigitBot = 0 *)
```
Total node potential = `digit_potential f + digit_potential r`, summed recursively over materialised spine nodes.

## Coding Conventions

- Follow ImplicitQueue.v's style exactly (naming, tactic usage, proof structure)
- Use `teardown` for repetitive case analysis
- Use `mgo_` and `keep_mgo_` for optimistic specification proofs
- Use `invert_clear` for inversions that clean up hypotheses
- All proofs should be `Defined` (not `Qed`) if they compute, `Qed` for Props
- Use `Arguments` to set implicit arguments after each inductive definition
- Comment sections with `(* ================================================================= *)` banners

## Build

The project depends on the Clairvoyance library. Typical setup:
```bash
opam install coq-clairvoyance  # or build from source
```

The `_CoqProject` should include:
```
-R theories Clairvoyance
```
or whatever the local logical path is. Match the existing artifact's project configuration.

Compile with:
```bash
coq_makefile -f _CoqProject -o Makefile
make
```

## Current Status

- Section 1 (pure definitions) is drafted in `FingerTree.v`
- Sections 2–6 are TODO
- Priority: get Section 2 (lattice boilerplate) compiling, then Section 3 (demand functions)
- Symmetry exploitation: `snoc`/`unsnoc` are symmetric to `cons`/`uncons`, so proving one side first and then mirroring is efficient

## Amortised Analysis Summary

The debit invariant for the finger tree:
```
debits(m) ≤ min(|f| - 1, |r| - 1)
```

| (f, r) | Max debits |
|---------|-----------|
| (One, One) | 0 |
| (One, Two) or (Two, One) | 0 |
| (One, Three) or (Three, One) | 0 |
| (Two, Two) | 1 |
| (Two, Three) or (Three, Two) | 1 |
| (Three, Three) | 2 |

The `min` (rather than sum) is because **both** ends of the deque can trigger a force on the same middle suspension, so the suspension must be payable from the least-buffered side.

Key insight: after any cascade, the triggering digit resets to `Two` (safe), guaranteeing at least one non-cascading operation before the next cascade at that digit.