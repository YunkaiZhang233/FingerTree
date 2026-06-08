# Formally Verified Amortised Complexity of Claessen's Finger Tree

A Rocq (Coq) formalisation, developed for an MEng thesis, of the amortised
time complexity of **Koen Claessen's 2020 simplified finger tree** under persistent case, using the **bidirectional demand semantics** and **reverse physicist's method** of Xia et al. (ICFP 2024).

The headline result is machine-checked and assumption-free (no `Admitted`, no
`admit`): under the demand semantics, every deque operation runs in **O(1)
amortised time, even under persistent (non-linear) use**.

> This repository vendors the **ICFP 2024 artifact / `Clairvoyance` library**
> as its proof framework. That code is *not* part of this thesis — see
> [Repository layout](#repository-layout) for the split between the upstream
> library and the files written for this thesis.

---

## What is verified

The data structure (`A` is the element type):

```
Seq A   = Nil | Unit A | More (Digit A) (Seq (Tuple A)) (Digit A)
Digit A = One A | Two A A | Three A A A      -- the 1–3 element "fingers"
Tuple A = Pair A A | Triple A A A            -- the 2–3 element spine nodes
```

The spine is **polymorphically recursive** (each level stores tuples of the
level below) and **lazy**. `Two` is a *safe* digit; `One`/`Three` are
*dangerous*. The amortised argument uses the "safe digit" potential: `Two`
contributes 1, `One`/`Three` contribute 0.

### Core result — O(1) amortised deque (complete, 0 admits)

For the operation algebra `op = Empty | FCons x | FSnoc x | Head | FTail`, the
reverse physicist's method yields a uniform amortised budget of **4 ticks per
operation** that holds over *any* trace, including persistent reuse of
intermediate structures.

| Operation        | Demand fn  | Proven properties                          | File                 |
|------------------|------------|--------------------------------------------|----------------------|
| `empty`          | `emptyD`   | `_approx`, `_spec`                         | `FingerPhysicist.v`  |
| `fcons` (front+) | `fconsD'`  | `_approx`, `_spec`, `_cost`                | `FingerCons.v`       |
| `fsnoc` (rear+)  | `fsnocD'`  | `_approx`, `_spec`, `_cost`                | `FingerSnoc.v`       |
| `head`           | `headD'`   | `_approx`, `_spec`, `_cost`                | `FingerHead.v`       |
| `ftail`          | `ftailD'`  | `_approx`, `_spec`, `_cost`                | `FingerTail.v`       |

The whole argument is assembled in **`FingerPhysicist.v`**, culminating in:

```coq
Theorem amortized_cost : AmortizedCostSpec op value valueA.
```

`ftail` is the hard case: its cascading branch (front digit `One`) either
recurses on a `Pair`-headed spine or, for a `Triple`-headed spine, "chops" via
`map1 chop_triple` with **no recursion** — Claessen's key insight, which is what
makes the operation O(1) amortised rather than O(log n).

The debt sub-additivity machinery (`debt_SeqA_lub_subadditive` and friends),
needed for `WellDefinedPotential`, lives once in **`FingerCore.v`** and is
shared by every operation.

### Secondary results — O(log n) worst-case (cost proven, correctness pending)

| Result                                   | Statement (cost bound)                          | File              | Status                |
|------------------------------------------|-------------------------------------------------|-------------------|-----------------------|
| `concat` / Claessen's `glue`             | `concatD_cost`, `concatD_cost_O_log_n`          | `FingerConcat.v`  | cost ✅ / correctness ⏳ |
| `index` / `splitTree` (measure-annotated)| `indexD_cost`, `splitTreeD_cost`, `*_O_log_n`   | `FingerSplit.v`   | cost ✅ / correctness ⏳ |

For these two, the **worst-case O(log n) cost bounds are fully proven**; the
functional-correctness lemmas (`_approx` / `_spec`) are `Admitted` as scoped
future work (5 in `FingerConcat.v`, 2 in `FingerSplit.v`). The `O(log n)`
asymptotics rest on `size_lower_bound` / `depth_log_size` in `FingerSize.v`.
`FingerSplit.v` works over an abstract measure **`Monoid`** (`FingerMonoid.v`),
recovering random access, min-max queues, and ordered sequences à la
Hinze–Paterson by changing the monoid instance.

---

## Repository layout

### Thesis contribution (the files written for this project)

```
src/FingerCore.v        Data structure, approximation types, lattice, debt machinery
src/FingerCons.v        fcons  + demand analysis + proofs
src/FingerSnoc.v        fsnoc  + demand analysis + proofs (symmetric dual of cons)
src/FingerHead.v        head   + demand analysis + proofs
src/FingerTail.v        ftail  + demand analysis + proofs (the cascade / chop trick)
src/FingerPhysicist.v   empty + operation algebra + reverse physicist's method  ← main theorem
src/FingerSize.v        size / depth metrics; size_lower_bound, depth_log_size
src/FingerConcat.v      concat / glue; worst-case O(log n) cost bound
src/FingerMonoid.v      measure-monoid interface (size / interval / last-value)
src/FingerSplit.v       measure-annotated trees; O(log n) index & split cost bounds

docs/REFERENCE.md                 Detailed development reference
docs/SPLIT_NOTE.md                Notes on the split / measured-tree development
docs/TAIL_ANALYSIS.md             Feasibility analysis & design blueprint for ftail
docs/CLAESSEN_REFERENCE.md        Notes on Claessen 2020
docs/IMPLICITQUEUE_REFERENCE.md   Notes mapping ImplicitQueue.v to this development
CLAUDE.md                         Project notes / conventions
```

### Upstream library — *not* part of this thesis

These are the **ICFP 2024 artifact** files (the `Clairvoyance` library),
vendored unchanged as the verification framework. The finger-tree files
`From Clairvoyance Require Import` them.

```
src/Core.v  src/Approx.v  src/ApproxM.v  src/Tick.v  src/TickCost.v  src/Cost.v
src/Misc.v  src/ListA.v  src/List.v  src/Prod.v  src/Option.v  src/Relations.v
src/Setoid.v  src/FormalTranslation.v  src/DemandSemantics.v  src/Interfaces.v
src/QueueInterface.v  src/BankersQueue.v  src/ImplicitQueue.v
src/InsertionSort.v  src/SelectionSort.v
```

`ImplicitQueue.v` is the template this development mirrors most closely (the
simplified finger tree generalises the implicit queue: digits widen from {1,2}
to {1,2,3}, and both ends support insertion/deletion).

---

## Building

### Dependencies

- **Rocq Prover (Coq)** ≥ 8.16 (CI checks 8.16 – 8.19)
- [`coq-equations`](https://github.com/mattam82/Coq-Equations) ≥ 1.3
- [`coq-hammer-tactics`](https://github.com/lukaszcz/coqhammer) ≥ 1.3.2 — the
  `sauto` / `Tactics` component is used throughout the finger-tree proofs (no
  external SMT solver required)

All three ship with the [Coq Platform](https://github.com/coq/platform). With
opam:

```sh
opam install . --deps-only      # reads coq-finger-tree.opam
```

### Compile

```sh
make            # generates Makefile.coq from _CoqProject, then builds everything
make clean      # remove build artifacts
```

`_CoqProject` maps `src/` to the `Clairvoyance` logical namespace and lists the
files in dependency order; the finger-tree files come last.

### Checking assumptions

To confirm the core result depends on nothing but classical logic, check a
major proof term:

```coq
Print Assumptions amortized_cost.
```

You should see only `Classical_Prop.classic` (excluded middle, inherited from
the upstream library). The `Admitted` lemmas listed above are confined to the
correctness side of `concat`/`split` and do **not** feed into `amortized_cost`.

---

## Proof status at a glance

| File                 | `Qed` | `Admitted` | Notes                                       |
|----------------------|:-----:|:----------:|---------------------------------------------|
| `FingerCore.v`       |  34   |     0      | data structure, lattice, debt sub-additivity |
| `FingerCons.v`       |  11   |     0      | complete                                     |
| `FingerSnoc.v`       |  11   |     0      | complete                                     |
| `FingerHead.v`       |   7   |     0      | complete                                     |
| `FingerTail.v`       |  19   |     0      | complete                                     |
| `FingerPhysicist.v`  |  13   |     0      | complete — `amortized_cost`                  |
| `FingerSize.v`       |   5   |     0      | complete                                     |
| `FingerMonoid.v`     |   2   |     0      | complete                                     |
| `FingerConcat.v`     |  18   |     5      | cost proven; correctness future work         |
| `FingerSplit.v`      |  16   |     2      | cost proven; correctness future work         |

---

## References

- **Data structure** — Koen Claessen, *"Finger trees explained anew, and
  slightly simplified"*, Haskell Symposium 2020.
- **Verification framework** — Li-yao Xia, Laura Israel, Maite Kramarz, Nicholas
  Coltharp, Koen Claessen, Stephanie Weirich, Yao Li, *"Story of Your Lazy
  Function's Life: A Bidirectional Demand Semantics for Mechanized Cost Analysis
  of Lazy Programs"*, ICFP 2024. (This repo vendors its artifact.)
- **Persistent-cost confirmation** — Anton Lorenzen, *"Lightweight Testing of
  Persistent Amortized Time Complexity in the Credit Monad"*, 2025 — independently
  confirms (via QuickCheck) that Claessen's `tail` is O(1) amortised under
  persistence.
- **Measure-annotated trees** — Hinze & Paterson, *"Finger trees: a simple
  general-purpose data structure"*, JFP 16(2), 2006; X. Leroy, *Persistent data
  structures*, lecture 5, 2023.

## License & attribution

This project is released under the MIT License (see `LICENSE`).

The files under [Upstream library](#upstream-library--not-part-of-this-thesis)
are from the ICFP 2024 artifact accompanying Xia et al. and remain under the
license and copyright of their original authors; they are included here as the
verification framework. All `Finger*.v` files and the documentation in `docs/`
are the original work of this thesis.
