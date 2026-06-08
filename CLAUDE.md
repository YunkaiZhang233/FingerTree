# CLAUDE.md — Finger Tree Formal Verification Project

## Project Overview

MEng thesis project formally verifying the amortised time complexity of **Claessen's 2020 simplified finger tree** (a persistent deque) using the **bidirectional demand semantics** framework from Xia et al. (ICFP 2024).

**Goal**: prove that `cons`, `snoc`, `head`, and `tail` run in **O(1) amortised time**, even under persistent use, using the Rocq Prover (Coq). This goal is **met and machine-checked** (no `Admitted`/`admit` on the core path).

**Current status:**

- ✅ Pure data structure and operations (`FingerCore.v`)
- ✅ Approximation types & full lattice infrastructure (`FingerCore.v`)
- ✅ Demand semantics for `fcons` (`fconsD'`) — full proofs (`_approx`, `_spec`, `_cost`) — `FingerCons.v`
- ✅ Demand semantics for `fsnoc` (`fsnocD'`) — full proofs — `FingerSnoc.v` (symmetric dual of cons)
- ✅ Demand semantics for `head` (`headD'`) — full proofs — `FingerHead.v`
- ✅ Demand semantics for `ftail` (`ftailD'`) — full proofs, including the One-front cascade through Pair/Triple — `FingerTail.v`
- ✅ Sub-additivity of `debt` for `SeqA` (`debt_SeqA_lub_subadditive`) — `FingerCore.v`
- ✅ Physicist's argument over `op = Empty | FCons A | FSnoc A | Head | FTail`: all instances (`eval`, `exec`, `demand`, `potential`, `budget`, `pd`, `cd`, `well_defined_potential`, `physicist's_argumentD`, `amortized_cost`) closed — `FingerPhysicist.v`. Uniform `budget = 4`.
- ✅ Size/depth metrics + `O(log n)` foundations (`size_lower_bound`, `depth_log_size`) — `FingerSize.v`
- 🟡 **Secondary (cost-only)**: `concat`/`glue` (`FingerConcat.v`) and measure-annotated `index`/`split` (`FingerSplit.v`, `FingerMonoid.v`) — **worst-case O(log n) COST bounds fully proven**; their functional-correctness lemmas (`_approx`/`_spec`) are `Admitted` as scoped future work (5 in `FingerConcat.v`, 2 in `FingerSplit.v`).
- ❌ **Out of thesis scope**: `last`/`init` — symmetric to `head`/`tail`, described in thesis only.

## Key References

- **Data structure**: Koen Claessen, "Finger trees explained anew, and slightly simplified" (Haskell Symposium 2020).
- **Verification framework**: Li-yao Xia et al., "Story of Your Lazy Function's Life: A Bidirectional Demand Semantics for Mechanized Cost Analysis of Lazy Programs" (ICFP 2024).
- **Persistent analysis confirmation**: Anton Lorenzen, "Lightweight Testing of Persistent Amortized Time Complexity in the Credit Monad" (2025) — verifies via QuickCheck that Claessen's `tail` has O(1) amortised cost in the persistent setting, using credit passing. Confirms our pen-and-paper analysis is correct.
- **Measure-annotated trees**: Hinze & Paterson, "Finger trees: a simple general-purpose data structure" (JFP 16(2), 2006); X. Leroy, "Persistent data structures", lecture 5 (2023). Basis for `FingerMonoid.v` / `FingerSplit.v`.
- **Template file**: `ImplicitQueue.v` from the ICFP 2024 artifact. This project mirrors its structure closely.
- **Library**: The `Clairvoyance` Rocq library (the artifact's library), vendored under `src/` (everything except `src/Finger*.v`).

## The Data Structure

```
Seq A   = Nil | Unit A | More (Digit A) (Seq (Tuple A)) (Digit A)
Digit A = One A | Two A A | Three A A A
Tuple A = Pair A A | Triple A A A
```

`Some` renamed to `Digit` in Coq (to avoid colliding with `option`'s `Some`).

Key invariants:
- `Digit` holds 1–3 elements at the fingers. `Two` is **safe**; `One` and `Three` are **dangerous**.
- `Tuple` holds 2–3 elements in the spine.
- The middle field is **polymorphic recursion** (each level stores tuples of the level below) and **lazy** (wrapped in `T`).
- `tail`'s cascading case (front digit `One`) has a three-way branch: empty spine / spine head `Pair x y` (recurse) / spine head `Triple x _ _` (chop via `map1`, **no recursion**). The chop/`map1` shortcut for `Triple` is Claessen's key insight. `chop_triple` and `map1` live at `FingerTail.v:29` and `FingerTail.v:38`.

## Verification Patterns Learned (these all work; consult before re-deriving)

### Polymorphic-recursion induction
- Single-argument lemmas use the custom `SeqA_ind` (`FingerCore.v:590`). Its `MoreA` case provides a `TR1`-wrapped IH at `TupleA A`. (`FingerSize.v` also defines `Seq_ind_poly` for the *pure* `Seq`.)
- Two-argument lemmas (antisymmetry, sub-additivity) require `fix SELF n` with `A` universally quantified **inside** the statement, with explicit `@` when composing through smaller types.

### Mixed-monad bind notation footgun
The `>>` notation is overloaded for the `M` monad (`Core.v`) and the `Tick` monad (`Tick.Notations`). **Always use `let+` for `Tick`** explicitly to avoid ambiguity.

### Forcing the outer thunk for monotonicity
If a clairvoyant function `fA : T (SeqA A) → M ...` deterministically returns a non-bottom value for `q = Undefined`, monotonicity fails. **Always use the `forcing q (...)` pattern** (which gives `bottom` on `Undefined`) for the outer wrapper:
- `fA' : SeqA A → M ...` (the body operating on unwrapped `SeqA A`)
- `fA  : T (SeqA A) → M ... := forcing q fA'`

This makes `fA_mon`'s `Undefined` case trivial via `solve_mon`.

### Demand for queries with `outD = None`
For `head s` / `tail s` on non-`Nil` `s`, even when the user demands nothing of the output (`outD = None` or `outD ≤ NilA`), the demand on `s` is NOT `bottom` — it must be a **structured shape** showing that the operation forced the spine top and the digit constructor. Returning `bottom` breaks `CvDemand` (because `headA Undefined = forcing Undefined _ = bottom`, which has no optimistic witness). See `headD'`'s design at `FingerHead.v:43`.

### Budget tightness under safe-convention
Convention: `safe_DigitA` = 0 for One/Three, 1 for Two; undefined-default = 1 (`FingerCore.v:828`). Worst-case input demand has potential `1 (TwoA) + 1 (Undefined rear) = 2`; plus 1 cost = 3. The physicist's argument uses a **uniform `budget = 4`** across all operations (`FingerPhysicist.v`), which comfortably covers every case (cons/snoc/head/tail) under a single constant.

### `pose proof` stalls on let-laden lemma types
We observed `pose proof (fconsD'_cost_bottom x q)` stalling due to elaboration of `let inM := ... in let cost := ... in ...`-style lemma types. Workarounds:
- `eapply lemma in H` to instantiate against a known premise.
- Pass typeclass args explicitly with `@`.
- Inline the case analysis if the lemma is only used once (we did this for `fconsD'_cost_bottom` in the `physicist's_argumentD` FCons-Undefined branch).

### Sub-additivity of `debt`
`debt_SeqA_lub_subadditive` (`FingerCore.v:886`) decomposes:
- `safe_DigitA_lub_subadditive` (digit level).
- `safe_T_lub_subadditive` (T-lifted digit).
- Main lemma via `SeqA_ind`, with the `MoreA` case combining all three plus the spine IH.

Reusable for any operation's `well_defined_potential` — `cons`/`snoc`/`head`/`tail` all share this single proof (it lives once in `FingerCore.v`; the other files do not re-prove it).

## File Structure

The development is split across ten `src/Finger*.v` files (it was originally one monolithic `Finger.v`; that file no longer exists). Build/dependency order is fixed in `_CoqProject`.

```
File                  Content
FingerCore.v          Pure data structure, approximation types & lattice,
                      debt machinery (safe_DigitA / safe_T / debt_SeqA),
                      SeqA_ind, sub-additivity lemmas, shared tactics
FingerCons.v          fcons / fconsA / fconsD' + proofs (approx, spec, cost)
FingerSnoc.v          fsnoc / fsnocA / fsnocD' + proofs (symmetric dual of cons)
FingerHead.v          head / headA / headD' + proofs
FingerTail.v          ftail / ftailA / ftailD' + proofs; chop_triple, map1
FingerSize.v          Seq_ind_poly, digit_size/size/depth, size_lower_bound,
                      depth_log_size (O(log n) foundations)
FingerConcat.v        concat / Claessen's glue; worst-case O(log n) cost bound
FingerMonoid.v        measure-monoid interface (size / interval / last-value)
FingerSplit.v         measure-annotated trees; O(log n) index & split cost
FingerPhysicist.v     empty + operation algebra op + reverse physicist's
                      method → amortized_cost (the main theorem)
```

Within each operation file the layout follows the artifact convention:
pure function → clairvoyant (`A`, via `forcing`) + monotonicity → demand
function (`D'`) → `_approx` / `_spec` / `_cost` proofs.

## Operation Algebra in Physicist's Argument

`op = Empty | FCons A | FSnoc A | Head | FTail` (`FingerPhysicist.v:83`). Uniform `budget = 4` for every operation. The final theorem is:

```coq
Theorem amortized_cost : AmortizedCostSpec op value valueA.
```

proved by `eapply @physicist's_method; typeclasses eauto`. `Print Assumptions amortized_cost` should report only `Classical_Prop.classic` (inherited from the upstream library); the `Admitted` lemmas in `FingerConcat.v`/`FingerSplit.v` do **not** feed into it.

## Remaining Work (post-core)

The core deque result is complete. What remains is correctness for the secondary operations:

1. `FingerConcat.v`: discharge the 5 `Admitted` correctness lemmas (`glueD'_approx`, `glueD'_spec`, and helpers) — requires a correct `unbundle` (currently stubbed for cost-only analysis).
2. `FingerSplit.v`: discharge the 2 `Admitted` correctness lemmas (`splitD_approx` / `splitD_spec`); the demand *values* (not just the tick structure) need to be filled in.

The cost bounds for both (`concatD_cost*`, `indexD_cost`, `splitTreeD_cost`, `*_O_log_n`) are already proven and depend only on `FingerSize.v`.

## Coding Conventions

- Follow `ImplicitQueue.v` style (naming, tactics, structure).
- `mgo_` / `keep_mgo_` / `mgo_brute_force` for optimistic specs (defined at the top of `FingerCore.v`).
- `invert_clear` for clean inversions; `teardown` to destruct on every match/if.
- `Qed` for Props (default); `Defined` only for terms that need to compute.
- Section banner: `(** ===== Section name ===== *)`.
- `Tick`-monad bind: always `let+`, never `>>` (collision risk with `M`'s `>>`).

## Build / Dependencies

The project depends on the vendored `Clairvoyance` library (`src/` minus `Finger*.v`), `coq-equations`, and **`coq-hammer-tactics`** — CoqHammer's `Tactics`/`sauto` are imported (`From Hammer Require Import Tactics`) and used throughout the finger-tree proofs, so the dependency is required (do **not** drop it). `_CoqProject` maps `src/` to the `Clairvoyance` namespace and lists files in dependency order, finger-tree files last. Build with `make` (it generates `Makefile.coq` from `_CoqProject`). CI checks Coq 8.19 only.
