# CLAUDE.md — Finger Tree Formal Verification Project

## Project Overview

MEng thesis project formally verifying the amortised time complexity of **Claessen's 2020 simplified finger tree** (a persistent deque) using the **bidirectional demand semantics** framework from Xia et al. (ICFP 2024).

**Goal**: prove that `cons`, `head`, and `tail` (with the symmetric `snoc`, `last`, `init` left as an explicit thesis note) run in **O(1) amortised time**, even under persistent use, using the Rocq Prover (Coq).

**Current status (close to thesis deadline):**

- ✅ Pure data structure and operations (Section 1)
- ✅ Approximation types & full lattice infrastructure (Section 2)
- ✅ Demand semantics for `cons` (`fconsD'`) with full proofs (`_approx`, `_spec`, `_cost`)
- ✅ Demand semantics for `head` (`headD'`) with full proofs
- ✅ Sub-additivity of `debt` for `SeqA` (`debt_SeqA_lub_subadditive`)
- ✅ Physicist's argument framework over `op = Empty | FCons A | Head`: all instances (`eval`, `exec`, `demand`, `potential`, `budget`, `pd`, `cd`, `well_defined_potential`, `physicist's_argumentD`, `amortized_cost`) closed
- ⏳ **NEXT**: `tail` (full scope, including the One-front cascade through Pair/Triple)
- ❌ **Out of thesis scope**: `snoc`/`unsnoc`/`last`/`init` — symmetric arguments described in thesis only

## Key References

- **Data structure**: Koen Claessen, "Finger trees explained anew, and slightly simplified" (Haskell Symposium 2020).
- **Verification framework**: Li-yao Xia et al., "Story of Your Lazy Function's Life: A Bidirectional Demand Semantics for Mechanized Cost Analysis of Lazy Programs" (ICFP 2024).
- **Persistent analysis confirmation**: Anton Lorenzen, "Lightweight Testing of Persistent Amortized Time Complexity in the Credit Monad" (2025) — verifies via QuickCheck that Claessen's `tail` has O(1) amortised cost in the persistent setting, using credit passing. Confirms our pen-and-paper analysis is correct.
- **Template file**: `ImplicitQueue.v` from the ICFP 2024 artifact. This project mirrors its structure closely.
- **Library**: The `Clairvoyance` Rocq library (the artifact's library).

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
- `tail`'s cascading case (front digit `One`) has a three-way branch: empty spine / spine head `Pair x y` (recurse) / spine head `Triple x _ _` (chop via `map1`, **no recursion**). The chop/`map1` shortcut for `Triple` is Claessen's key insight.

## Verification Patterns Learned (these all work; consult before re-deriving)

### Polymorphic-recursion induction
- Single-argument lemmas use the custom `SeqA_ind` (line ~587). Its `MoreA` case provides a `TR1`-wrapped IH at `TupleA A`.
- Two-argument lemmas (antisymmetry, sub-additivity) require `fix SELF n` with `A` universally quantified **inside** the statement, with explicit `@` when composing through smaller types.

### Mixed-monad bind notation footgun
The `>>` notation is overloaded for the `M` monad (`Core.v`) and the `Tick` monad (`Tick.Notations`). **Always use `let+` for `Tick`** explicitly to avoid ambiguity.

### Forcing the outer thunk for monotonicity
If a clairvoyant function `fA : T (SeqA A) → M ...` deterministically returns a non-bottom value for `q = Undefined`, monotonicity fails. **Always use the `forcing q (...)` pattern** (which gives `bottom` on `Undefined`) for the outer wrapper:
- `fA' : SeqA A → M ...` (the body operating on unwrapped `SeqA A`)
- `fA  : T (SeqA A) → M ... := forcing q fA'`

This makes `fA_mon`'s `Undefined` case trivial via `solve_mon`.

### Demand for queries with `outD = None`
For `head s` / `tail s` on non-`Nil` `s`, even when the user demands nothing of the output (`outD = None` or `outD ≤ NilA`), the demand on `s` is NOT `bottom` — it must be a **structured shape** showing that the operation forced the spine top and the digit constructor. Returning `bottom` breaks `CvDemand` (because `headA Undefined = forcing Undefined _ = bottom`, which has no optimistic witness). See `headD'`'s revised design at lines ~1708–1730 of `Finger.v`.

### Budget tightness under safe-convention
Convention: `safe_DigitA` = 0 for One/Three, 1 for Two; undefined-default = 1. Worst-case input demand has potential `1 (TwoA) + 1 (Undefined rear) = 2`. Plus 1 cost = 3. So `budget = 3` is tight for operations that touch this case. Current budgets: Empty/FCons/Head all = 3. **Tail will need budget 3 too** by the analysis in `TAIL_ANALYSIS.md`.

### `pose proof` stalls on let-laden lemma types
We observed `pose proof (fconsD'_cost_bottom x q)` stalling due to elaboration of `let inM := ... in let cost := ... in ...`-style lemma types. Workarounds:
- `eapply lemma in H` to instantiate against a known premise.
- Pass typeclass args explicitly with `@`.
- Inline the case analysis if the lemma is only used once (we did this for `fconsD'_cost_bottom` in the `physicist's_argumentD` FCons-Undefined branch).

### Sub-additivity of `debt`
`debt_SeqA_lub_subadditive` (line ~1480) decomposes:
- `safe_DigitA_lub_subadditive` (digit level).
- `safe_T_lub_subadditive` (T-lifted digit).
- Main lemma via `SeqA_ind`, with the `MoreA` case combining all three plus the spine IH.

Reusable for any future operation's `well_defined_potential` — `tail` will not need to re-prove this.

## File Structure (Finger.v)

```
Lines    Content
~30      Imports
~130–230 Section 1: Pure data structure & operations
~240–815 Section 2: Approximation types & lattice
~820–1090 Section 3: fcons / fconsA / fconsD' (definition)
~1090–1670 Section 4: fcons proofs (approx, spec, cost) + sub-additivity (1445–1535)
~1697–1840 Section 5: head / headA / headD'
~1845–1895 Section 6: empty / forceD
~1917–2266 Section 7: Physicist's Argument
```

Next addition: **Section 5.5** between Head and Empty/Physicist's, covering `tail` / `tailA` / `tailD'` and its proofs. Then extend the operation algebra `op` to include `Tail` and update the Physicist's Argument section.

## Operation Algebra in Physicist's Argument

Currently: `op = Empty | FCons A | Head`. Budgets all = 3.

After `tail` is added: `op = Empty | FCons A | Head | Tail`. `Tail` budget: 3 (per analysis in `TAIL_ANALYSIS.md`).

## Next Step: implementing `tail` (full scope)

Detailed feasibility analysis and design blueprint: see `TAIL_ANALYSIS.md`.

**Phased plan** (~7–8 working days estimated):
1. **Phase A**: Pure `tail` + `chop_triple` + reuse of existing `map1`. `Compute` tests.
2. **Phase B**: `tail_ind` custom induction principle (9 cases).
3. **Phase C**: `tailA' / tailA` (clairvoyant via `forcing`) + `tailA_mon`.
4. **Phase D**: `tailD'` with two helpers — `add_pair_to_head_demand`, `inverse_chop_demand` — plus their debt-preservation lemmas.
5. **Phase E**: Big lemmas `tailD'_approx`, `tailD'_spec`, `tailD'_cost`.
6. **Phase F**: Extend `op`, `eval`, `exec`, `demand`, `wf_eval`, `monotonic_exec`, `pd`, `cd`, `physicist's_argumentD`.

**Design decision**: NOT factoring through a separate `deep0` (à la Lorenzen). Inline the structure into `tail` directly, matching Claessen's presentation. This avoids mutual recursion at the pure level and keeps proofs flatter.

## Coding Conventions

- Follow `ImplicitQueue.v` style (naming, tactics, structure).
- `mgo_` / `keep_mgo_` / `mgo_brute_force` for optimistic specs.
- `invert_clear` for clean inversions.
- `Qed` for Props (default); `Defined` only for terms that need to compute.
- Section banner: `(** ===== Section name ===== *)`.
- `Tick`-monad bind: always `let+`, never `>>` (collision risk with `M`'s `>>`).

## Build / Dependencies

The project depends on the Clairvoyance library (installed alongside the ICFP 2024 artifact). Confirm `_CoqProject` is set up accordingly. CoqHammer was originally imported but is not used in current proofs — consider dropping the import to speed up compilation.