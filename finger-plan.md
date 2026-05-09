# Finger Tree Verification — Coding Plan

Working file: `src/Finger.v`
Reference: `CLAESSEN_REFERENCE.md`, `IMPLICITQUEUE_REFERENCE.md`, `src/ImplicitQueue.v`

---

## Status

| Section | Description | Status |
|---------|-------------|--------|
| 1 | Pure definitions (Claessen Try 5) | Done |
| 2 Part 1 | DigitA + lattice boilerplate | Done |
| 2 Part 2 | TupleA + lattice boilerplate | Done |
| 2 Part 3 | SeqA + SeqA_ind + lattice boilerplate | **Next** |
| 3 | Demand functions | TODO |
| 4 | Approximation proofs | TODO |
| 5 | Potential function + amortised cost theorems | TODO |
| 6 | Persistence (stretch goal) | TODO |

---

## Section 1 — What's in scope (for reference)

Pure types: `Digit`, `Tuple` (Pair/Triple), `Seq`.

Non-recursive O(1) helpers: `chop`, `chopLast`, `map1`, `mapLast`.

Operations: `head`, `last`, `cons`, `snoc`, `uncons`, `unsnoc`, `tail`, `init`.

`toListWith` / `toList` flatten using the `Tuple` case split.

Key structural facts:
- `cons` / `snoc` always push a `Pair` into the spine on overflow.
- `uncons` has a **three-way branch** when front digit is `One`: empty spine /
  spine head `Pair a b` (recurse, install `Two a b`) / spine head `Triple a _ _`
  (use `map1 chop`, install `One a`, no recursion).
- `unsnoc` is symmetric via `last` / `mapLast chopLast`.

---

## Section 2 Part 3 — SeqA (immediate next step)

### 2a. Define SeqA (under Unset Elimination Schemes)

```coq
Unset Elimination Schemes.

Inductive SeqA (A : Type) : Type :=
| NilA  : SeqA A
| UnitA : T A -> SeqA A
| MoreA : T (DigitA A) -> T (SeqA (TupleA A)) -> T (DigitA A) -> SeqA A.

Set Elimination Schemes.
```

- Digit fields are `T (DigitA A)` — T-wrapped, not raw.
- Middle field is `T (SeqA (TupleA A))` — thunked polymorphic recursion over
  `TupleA`, not `prodA`.
- No `SeqBot` constructor; bottom comes from `Undefined` at the `T` level.

### 2b. Write SeqA_ind by hand

Rocq's auto-generated induction principle is wrong for the nested
`SeqA (TupleA A)`. Follow `QueueA_ind` pattern (ImplicitQueue.v lines 365–384):

```coq
Lemma SeqA_ind (P : forall A, SeqA A -> Prop) :
  (forall A, P A NilA) ->
  (forall A x, P A (UnitA x)) ->
  (forall A f m r, TR1 (P (TupleA A)) m -> P A (MoreA f m r)) ->
  forall (A : Type) (s : SeqA A), P A s.
Proof.
  intros HNilA HUnitA HMoreA. fix SELF 2.
  destruct s.
  - apply HNilA.
  - apply HUnitA.
  - apply HMoreA. destruct t0.
    + constructor. apply SELF.
    + constructor.
Qed.
```

Key differences from `QueueA_ind`:
- Extra `UnitA` case.
- IH threads through `TupleA A` instead of `prodA A A`.

### 2c. Lattice boilerplate for SeqA

Same sequence as DigitA/TupleA, but proofs use `SeqA_ind` (not `destruct`)
for the inductive cases:

1. `LessDefined_SeqA` — inductive, constructors for `NilA` / `UnitA` / `MoreA`
   (pointwise on matching), T-level `Undefined` covers the bottom case.
2. `Reflexive_LessDefined_SeqA`
3. `Transitive_LessDefined_SeqA`
4. `PreOrder_LessDefined_SeqA`
5. `LessDefined_SeqA_antisym` + `PartialOrder_LessDefined_SeqA`
6. `Exact_Seq` — must be a `fix` over type parameters (see note below)
7. `BottomOf_SeqA` + `BottomIsLeast_SeqA`
8. `Lub_SeqA` + `LubLaw_SeqA`

#### Note on Exact_Seq

Must be parameterised as a fix, like `Exact_Queue` in ImplicitQueue.v (lines
477–482), so Rocq unifies the right `Exact` instance in the recursive call:

```coq
#[global] Instance Exact_Seq : forall A B `{Exact A B}, Exact (Seq A) (SeqA B) :=
  fix Exact_Seq A B _ s :=
    match s with
    | Nil        => NilA
    | Unit x     => UnitA (exact x)
    | More f m r => MoreA (exact f) (Thunk (Exact_Seq _ _ _ m)) (exact r)
    end.
```

In the `More` branch: `m : Seq (Tuple A)`, so the recursive call needs
`Exact (Tuple A) (TupleA B)`, which is resolved by the `Exact_Tuple` instance
already in scope.

---

## Section 3 — Demand Functions

Four demand functions in the `Tick` monad, mirroring the pure operations:

- `consD'`   — demand for `cons x s`
- `snocD'`   — demand for `snoc s x`
- `unconsD'` — demand for `uncons s`
- `unsnocD'` — demand for `unsnoc s`

`unconsD'` and `unsnocD'` have a **three-way branch** matching the pure
`uncons`/`unsnoc` structure (empty spine / Pair / Triple):

- **Triple case** in `unconsD'`: uses `map1 chop` — no recursive spine demand,
  just propagate demand through the non-recursive `map1`.
- **Pair case**: recursive spine demand, same pattern as ImplicitQueue.

`snocD'` / `unsnocD'` are symmetric to `consD'` / `unconsD'`.

Pattern (from ImplicitQueue.v):
- Use `Tick` for cost counting.
- Use `optimistic_thunk` for thunks that may not be forced.
- Each function returns the demanded approximation of the input.

---

## Section 4 — Approximation Proofs

For each demand function, prove it computes a valid approximation:

- `consD'_approx`
- `snocD'_approx`
- `unconsD'_approx`
- `unsnocD'_approx`

Use `mgo_` / `keep_mgo_` tactics and `invert_clear` for case analysis.
The Triple branch in `unconsD'_approx` will require a lemma about `map1 chop`
being monotone with respect to the approximation order.

---

## Section 5 — Potential Function & Amortised Cost

### Potential function (from CLAESSEN_REFERENCE.md Section 7)

```coq
Definition dang {A} (d : Digit A) : nat :=
  match d with
  | One _       => 1
  | Two _ _     => 0
  | Three _ _ _ => 1
  end.

Fixpoint pot {A} (s : Seq A) : nat :=
  match s with
  | Nil        => 0
  | Unit _     => 0
  | More f q r => dang f + pot q + dang r
  end.
```

`pot` counts dangerous digits (`One` and `Three`) across all spine levels.
`Two` is safe and contributes 0.

### Proof obligations (Claessen Section 9)

```
consT x q + pot (cons x q) - pot q  ≤  3
tailT q   + pot (tail q)   - pot q  ≤  2
```

Both sides recurse only on `Three` / `One` fronts respectively; in both cases
the recursive call leaves a `Two` (safe), reducing `dang` by 1 and paying for
the step.

---

## Section 6 — Persistence (stretch goal)

Extend to persistent use via `LubLaw` monotonicity. Follows naturally once
Section 5 is complete and `LubLaw_SeqA` is in place.

---

## Key Design Decisions (do not revisit)

- Section 1 uses Claessen's **Try 5** design: `Tuple = Pair | Triple` in the
  spine, not bare `A * A`. `uncons`/`unsnoc` use `head`/`last` + `map1`/
  `mapLast` for the Triple shortcut.
- `DigitA` and `TupleA` use `T A` fields, no bot constructor — matches
  ImplicitQueue.v's `FrontA`/`RearA` pattern exactly.
- `SeqA` digit fields are `T (DigitA A)`; spine field is `T (SeqA (TupleA A))`.
- `Exact_Seq` must be a polymorphic `fix` (not a plain instance) to avoid
  instance-mismatch in the recursive case — see ImplicitQueue.v comment
  lines 443–476.
- Preamble contains `make_partial_order` and `LessDefined_T_antisym` (not
  exported by any library module).
- All proofs follow ImplicitQueue.v naming and tactic style.
