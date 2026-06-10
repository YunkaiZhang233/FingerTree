# `wip/` — scratch for the `glueD'_spec` proof effort

Work-in-progress Coq for closing the last admit in `src/FingerConcat.v`
(`glueD'_spec`). **Not in `_CoqProject`** — `make` ignores this directory, so
these files may contain `admit`/`Abort` without breaking the build.

Full plan: [`../docs/CONCAT_SPEC_PLAN.md`](../docs/CONCAT_SPEC_PLAN.md).

## Files

| File | What it is |
|---|---|
| `step_lemma.v` | `fconsA_elemD_step` — the kernel lemma. Case 1 proven; cases 2–5 admitted with per-case strategy comments. |
| `inspect.v` | Goal-inspection harness. Prints the exact goal an arm presents, then `Abort`s. Copy a block, set `s1`/`s2`, run the preamble, `idtac` the goal. |

## Workflow

```sh
# from the FingerTree repo root, with src/*.vo already built (run `make` once):

# iterate a wip lemma (fast — loads FingerConcat.vo, not the whole project)
~/.opam/thesis/bin/coqc -Q src Clairvoyance wip/step_lemma.v

# see an arm's goal shape before writing tactics
~/.opam/thesis/bin/coqc -Q src Clairvoyance wip/inspect.v

# once a lemma is fully Qed: paste it into src/FingerConcat.v, then refresh the .vo
make
```

Then the next scratch file can `Require Import FingerConcat` and see the newly
integrated lemma.

## Conventions

- `Set Implicit Arguments.` at the top of every scratch (matches
  `FingerConcat.v`; otherwise recursive/`@` calls won't elaborate).
- Inspect, don't guess: `match goal with |- ?g => idtac g end.`
- Model each `fconsA_elemD_step` / `fsnocA_elemD_step` case on the matching
  case of `fconsD'_spec` / `fsnocD'_spec` in `src/FingerCons.v` /
  `src/FingerSnoc.v`.
- Tactic-pattern catalogue is in the design doc (`§5`).

## Definition of done

`glueD'_spec` is `Qed`; `Print Assumptions glueD'_spec` is clean. Then delete
`src/FingerConcatAlt.v`, drop it from `_CoqProject`, and this `wip/` directory
can go too.
