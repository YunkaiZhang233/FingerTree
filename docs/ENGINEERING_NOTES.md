# Proof Engineering Takeaways

A record of the recurring Coq/Rocq pitfalls, idioms, and tactical patterns that came up while mechanising the simplified finger tree. Written for the future self continuing this project (or a successor working in the same demand-semantics framework).

The patterns here are not deep theorems; they are the surface-level friction of working with this particular codebase. Knowing them up front would have saved hours.

---

## 1. Implicit arguments and `Set Maximal Implicit Insertion`

The codebase uses `Set Implicit Arguments` together with `Set Maximal Implicit Insertion`. This causes typeclass arguments (and sometimes type parameters) to be inserted aggressively at application sites. The symptom is bewildering: you write `lemma x y z` and Coq complains that one of your explicit arguments has the wrong type, because Coq has silently consumed it as an implicit.

The fix is the `@`-form, which makes every argument explicit and lets you fill in implicits with `_`:

```coq
pose proof (@fconsD'_cost A B _ _ x s outD Happrox) as Hfcons.
```

Count the implicits carefully. For `fconsD'_cost` with signature `forall (A B : Type) ` `{LessDefined B, Exact A B} (x : A) (s : Seq A) (outD : SeqA B), outD `is_approx` fcons x s -> ...`, the implicits after `A B` are `LessDefined B` and `Exact A B` (two typeclass slots). So the `@`-form takes `A B _ _ x s outD Happrox` — eight arguments.

For `fconsD'_approx`, which also requires `!Reflexive LDB`, there is one extra typeclass slot: `@fconsD'_approx A B _ _ _ x s outD Happrox` (nine arguments).

When in doubt: type the lemma name in Coq and look at its raw type with `About lemma_name` to count implicits.

A related pitfall: when you change a lemma's signature (e.g. add `!Reflexive LDB` to a hypothesis list), every `@`-call site must be updated. The error messages in this case are misleading — Coq complains about a downstream argument's type, not about the wrong number of arguments.

---

## 2. `let`-bound names hiding cleanup work

Lemma statements often use `let inM := ... in let cost := Tick.cost inM in ...` to abbreviate. When you `pose proof` such a lemma, the resulting hypothesis contains these `let`-bindings literally. They behave correctly for unification, but for arithmetic via `lia` or `nia` you usually want them inlined:

```coq
pose proof (@fconsD'_cost A B _ _ x s outD Happrox) as Hfcons.
cbv zeta in Hfcons.
```

`cbv zeta` unfolds local `let`-bindings and nothing else. After this, `Hfcons` becomes a flat inequality `debt (Tick.val ...) + Tick.cost ... <= ...` that `lia`/`nia` can read.

---

## 3. `simpl` vs `cbn` vs `change` vs `Arguments F : simpl nomatch`

The single biggest time sink in this project. Coq has multiple reduction tactics, each with subtle differences. The rules of thumb I converged on:

**`simpl`** is the default but over-eager. On a function whose body matches on a variable, `simpl` will unfold one step too far and leave you with a partially-reduced `match ... with` that nothing matches against cleanly. Combined with `Set Implicit Arguments`, the resulting goals can be hard to read.

**`cbn`** is the more disciplined cousin. It respects `Arguments F : simpl nomatch` and `Arguments F : simpl never` annotations. Prefer `cbn` to `simpl` when targeted reduction matters. For example, `cbn [List.fold_right]` reduces only `List.fold_right`, leaving everything else alone.

**`Arguments F : simpl nomatch`** is the workhorse annotation. Add this after defining any `Fixpoint` whose body case-matches on its argument. It tells `simpl` (and `cbn`) to stop unfolding when the discriminee is a variable, which is almost always what you want. We added this for `toTuples`, `toTuplesA`, and `glueD'` to prevent runaway unfolding.

**`Arguments F : simpl never`** is the nuclear option: never unfold `F` via `simpl`/`cbn`. Reserve for cases where you really do not want automatic reduction (e.g. you want to manage all unfolding yourself via `unfold ... in *` or `change`).

**`change <expr1> with <expr2>`** is the manual override. Use when `simpl`/`cbn` over-reduces and you want to refold back to a folded form:

```coq
change (match Tick.val (fconsD' x s outD) with
        | Thunk q => q
        | Undefined => bottom_of (exact s)
        end) with innerD_forced.
```

This is brittle (the LHS must match the goal exactly) but invaluable when nothing else works.

**`replace <expr1> with <expr2> by reflexivity`** is `change`'s easier sibling. It evaluates both sides definitionally; if they reduce to the same term, the rewrite succeeds. Use for cases where `change`'s lockstep matching fails but the equality is true by computation.

---

## 4. Polymorphic recursion: `Seq_ind` and `SeqA_ind`

The biggest structural pitfall in this codebase. `Seq A` and `SeqA A` both contain non-uniform recursive positions (`More _ : Seq (Tuple A)`, `MoreA _ : T (SeqA (TupleA A))`). Coq's automatic `induction q` generates an induction principle that is **useless** for these types — the IH it produces has the wrong type, often something like `T (DigitA u1)` (a stray hypothesis named like an IH but not actually an inductive hypothesis).

The solution is custom induction principles. `SeqA_ind` exists for the clairvoyant side (uses `TR1` to lift the predicate over `T`). For the pure side, we wrote `Seq_ind_poly`:

```coq
Lemma Seq_ind_poly (P : forall A, Seq A -> Prop) :
  (forall A, P A Nil) ->
  (forall A x, P A (Unit x)) ->
  (forall A f m r, P (Tuple A) m -> P A (More f m r)) ->
  forall A (s : Seq A), P A s.
Proof.
  intros HNil HUnit HMore.
  fix SELF 2.
  destruct s.
  - apply HNil.
  - apply HUnit.
  - apply HMore. apply SELF.
Qed.
```

When applying these, the lemma statement must be shaped so that `A` and the inductee come **first**, before any typeclass binders. The motive of the induction principle quantifies over `A` at the outermost level, and `apply (Seq_ind_poly ...)` only unifies cleanly if the goal universals match. This often means restating the lemma with an unusual quantifier order:

```coq
Lemma debt_le_2depth :
  forall (A : Type) (s : Seq A),
  forall (B : Type) `{LessDefined B, Exact A B} (outD : SeqA B),
    outD `is_approx` s -> debt outD <= 2 * depth s.
```

Note that `A` and `s` come first, then `B` and the typeclasses. This is necessary for the apply to work; the natural ordering (`A B (s : Seq A) (outD : SeqA B)`) does not match the induction principle's motive.

A related lesson: after `apply (Seq_ind_poly ...)`, do not `intros` before applying. The conclusion of `Seq_ind_poly` is `forall A s, P A s` — if you have already introduced `A` and `s`, the goal is not in the right shape. Revert them first if necessary.

When the natural induction works but the IH name is something nonsensical like `IHm1 : T (DigitA u1)`, that is the symptom: Coq's auto-induction failed to produce a usable hypothesis. Switch to `Seq_ind_poly` or `SeqA_ind`.

---

## 5. `lia` versus `nia`

`lia` decides linear arithmetic over integers. It handles addition, subtraction, multiplication by constants, ordering — all linearly. It does **not** handle multiplication of two variables.

`nia` extends `lia` with limited nonlinear reasoning. It will discharge `a * b <= c` when given enough bounds on `a` and `b`. It is slower than `lia` and not complete, but it covers many cases that arise in cost-bound proofs where you have `length as_ * (depth s_2 + 2 * length as_) <= C`.

The pattern that worked repeatedly in this project: when you have a hypothesis with a product (typically from a fold cost lemma), you cannot just `lia` — you must first derive a concrete numerical bound. Example:

```coq
assert (Hfold' : Tick.cost (foldl_fsnocD' as_ s_1 outD) <= 30).
{ etransitivity; [exact Hfold | ]. nia. }
lia.
```

The trick is to use `nia` to prove a concrete linear-in-`depth` bound (e.g. `<= 30 + 6 * depth m_1`), then `lia` for the final combination. `nia` is happy as long as the products involve bounded variables.

When `nia` fails too, fall back to manual case-split on the bounded variable:

```coq
destruct (length as_) as [|[|[|[|n]]]] eqn:E;
  try (simpl; nia); exfalso; lia.
```

This case-splits `length as_` into 0, 1, 2, 3, and "at least 4", which the bound contradicts.

---

## 6. Inverting `less_defined` hypotheses

The codebase has many goals of the form `q' ≤ q` where `q' : SeqA A`, `q : SeqA A`, and you want to extract structural information about `q'` given `q`'s shape. The `invert_clear` tactic (from the project's tactics library) handles this:

```coq
invert_clear Hq1 as [| | f' ? m' ? r' ? Hf Hm Hr].
```

Three pipes for three constructors of `LessDefined_SeqA`. The pattern's underscores are positional placeholders for binders we do not name; the named identifiers (`f', m', r', Hf, Hm, Hr`) are accessible afterwards.

Common pitfall: the pattern shape depends on the **exact constructor count** and **field count** of the inductive being inverted. If you write `[| | x y z]` but the third constructor has 6 fields, Coq complains opaquely. Check the inductive's definition (`Inductive LessDefined_SeqA ...`) for the constructor signatures.

For `LessDefined_T` (`T A` is `Thunk A | Undefined`), the pattern is `[? ? Hinner |]`: first branch is `LessDefined_Thunk_Thunk` (two name slots for the wrapped values plus the equality), second branch is `LessDefined_Undefined` (no slots).

When the inversion produces a Thunk-Thunk case AND an Undefined case, handle both. The Undefined case is usually discharged with `apply bottom_is_least; reflexivity`.

---

## 7. The `let+`/`Tick.bind` pattern in demand functions

The demand functions (`fconsD'`, `fsnocD'`, `glueD'`, etc.) use a monadic style:

```coq
let+ innerD := fconsD' x s outD in
... use innerD ...
```

This expands to `Tick.bind (fconsD' x s outD) (fun innerD => ...)`. When proving cost lemmas, `Tick.cost` distributes over bind: `Tick.cost (Tick.bind m f) = Tick.cost m + Tick.cost (f (Tick.val m))`.

To make this visible in the goal, use `simpl Tick.cost` or `cbn [Tick.cost Tick.bind]`. After reduction, your goal will mention `Tick.cost (fconsD' x s outD)` (which you bound via `fconsD'_cost`) and `Tick.cost (continuation (Tick.val ...))` (which you handle by IH or further reduction).

The other half of bind, `Tick.val`, follows the same pattern: `Tick.val (Tick.bind m f) = Tick.val (f (Tick.val m))`. For `Tick.ret`, both `Tick.cost (Tick.ret x) = 0` and `Tick.val (Tick.ret x) = x`.

These identities are often left implicit in proofs — Coq reduces them automatically when `simpl`/`cbn` is invoked. But when they don't reduce (e.g. because the continuation is opaque), use `unfold Tick.bind, Tick.ret in *` to force them.

---

## 8. Setting up the proof: `revert`, polymorphic motives, and `apply`

For lemmas that induct over polymorphic types via `Seq_ind_poly` or `SeqA_ind`, the proof setup is delicate. The pattern is:

```coq
Lemma my_lemma : forall (A : Type) (s : Seq A), ...
Proof.
  apply (Seq_ind_poly
    (fun (A : Type) (s : Seq A) =>
       ... full statement ...)).
  - (* Nil case *) intros ...
  - (* Unit case *) intros ...
  - (* More case *) intros ... IHm ...
Qed.
```

Notice: no `intros` at all before `apply`. The lemma's universal binders need to be present in the goal for the induction principle's conclusion to unify.

If you accidentally `intros A` (or worse, all the hypotheses) before applying, the goal no longer has the shape `forall A s, P A s` and the apply fails with cryptic unification errors. The fix is `revert` everything that was introduced, or restate the lemma cleanly and re-enter the proof.

For the motive, ensure that universal type binders and typeclasses inside the motive use **different names** from the outer lemma's quantifier names. Coq's variable hygiene usually handles this automatically, but a clash will produce inscrutable "cannot ensure X is a subtype of Y" errors.

---

## 10. The IH usually lives inside `TR1` or behind `invert_clear`

When `SeqA_ind` (the clairvoyant induction principle) is used, the IH for the `MoreA f m r` case is typed `TR1 (P (TupleA A)) m`, not directly `P (TupleA A) m_inner`. `TR1` is the lift of a predicate over `T`: either `m = Thunk m_inner` with `P m_inner`, or `m = Undefined`. You unpack the IH by inverting it:

```coq
invert_clear IHm as [m_inner IHm_inner | ].
```

The first branch gives the Thunk case and the inner IH. The second branch gives the Undefined case (often trivial: `apply bottom_is_least; reflexivity` or similar).

This is symmetric with how `Hm : mD ≤ Thunk (exact m_inner)` is inverted: the same `T` structure shows up on both sides. You typically end up with three nested `invert_clear`s in deep cases — one for `Hq1`, one for `Hm`, one for `IHm`. Plan your variable names ahead of time so you do not run out of meaningful identifiers.

---

## 11. Typeclass resolution for `Exact` instances

The codebase has several `Exact` instances of different priorities: `Exact_id | 1` (lowest priority, generic), `Exact_Tuple`, `Exact_Digit`, `Exact_Seq`. When applying lemmas at non-leaf types (e.g. an IH at `Tuple A`), Coq's typeclass resolution sometimes picks the wrong instance, producing errors like "cannot ensure Exact A B is a subtype of Exact A0 B".

Two strategies:

**Be explicit with `@`-form**: pass the instance directly.

```coq
apply (@IHm (TupleA B0) _ (Exact_Tuple _ _) m_inner Hm_inner).
```

**Use named-argument syntax**: forces Coq to fill in specific slots.

```coq
apply IHm with (B := TupleA B0).
```

When neither works, the issue is usually a deeper mismatch in the motive shape — go back and check that the lemma is stated with the right quantifier order for the induction principle.

---

## 13. Goal management in long proofs: `set` and `change`

Long proofs accumulate complex sub-expressions in the goal: `Tick.val (foldl_fsnocD' as' (fsnoc s_1 x) outD)` is unwieldy and clutters the goal display. Bind it to a local name:

```coq
set (innerD := Tick.val (foldl_fsnocD' as' (fsnoc s_1 x) outD)) in *.
set (innerD_forced := match innerD with
                      | Thunk q => q
                      | Undefined => bottom_of (exact (fsnoc s_1 x))
                      end) in *.
```

Now the goal mentions `innerD` and `innerD_forced` instead of their expansions. This makes the goal readable and lets you write `change ... with innerD_forced` to refold over-eager reductions back to the named form.

`set ... in *` makes the binding visible in hypotheses too, which is usually what you want.

---

## 14. When `lia`/`nia` is silent but should close

Sometimes `lia` simply does not fire on a goal that looks obviously linear. The most common reasons:

**The goal has `match ... with` left over** that `lia` does not see through. Reduce it first with `simpl`/`cbn`.

**There is a function application that `lia` treats as opaque** but you actually know its value. Bring it into the linear fragment by destructuring or by `unfold`ing.

**The goal has `S (S (S ...))` from unreduced naturals.** Sometimes `lia` handles these; sometimes a `simpl` first helps.

**One side has a `let`-binding.** Run `cbv zeta` to inline.

When `lia` is silent, suspect one of these four. If none apply, the goal genuinely is not in `lia`'s fragment — try `nia` or a manual case-split.

---

## 15. Big-picture lesson: scope ruthlessly

When time is tight, write a design document that explicitly enumerates "in scope" and "out of scope" pieces, with rationale for each. Without this discipline, you find yourself half-mechanizing five different theorems and finishing none. With it, you can deliver one fully-proven result and clearly defer the rest.

Each helper lemma admitted "with comment justifying its truth" is a small honest debt. A pile of half-finished proofs is a large dishonest one.