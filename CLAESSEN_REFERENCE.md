# Claessen 2020 — Complete Implementation Reference

This document transcribes every function from the final version (Try 5)
of Claessen's "Finger Trees Explained Anew, and Slightly Simplified"
into Coq-style pseudocode, with explanations.

The paper only shows one side of the deque (`head`, `cons`, `tail`) and
states that `last`, `snoc`, `init` are "symmetrically implemented".
We provide both sides explicitly here.

---

## 1. Data Types

The paper's final data structure (Section 8):

```haskell
data Seq a   = Nil | Unit a | More (Some a) (Seq (Tuple a)) (Some a)
data Some a  = One a | Two a a | Three a a a
data Tuple a = Pair a a | Triple a a a
```

In Coq, we rename `Some` to `Digit` (to avoid the clash with `option`'s `Some`):

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

**Key structural points:**

- `Digit` holds 1–3 elements at the "fingers" (front and rear).
- `Tuple` holds 2–3 elements in the recursive spine.
- `Seq (Tuple A)` is the polymorphic recursion: level 0 stores `A`,
  level 1 stores `Tuple A`, level 2 stores `Tuple (Tuple A)`, etc.
- `Digit` and `Tuple` are *different types* with different roles:
  `Digit` appears at the fingers, `Tuple` appears in the spine.
- `Two` is the "safe" digit (buffer against both `cons` and `tail`).
  `One` and `Three` are "dangerous".
- `Pair` and `Triple` in the spine serve different roles in `tail`:
  `Pair` requires recursion to remove, `Triple` can be chopped in O(1).

---

## 2. Observation Functions

### 2.1 head (paper Section 8)

```coq
Definition head {A} (s : Seq A) : option A :=
  match s with
  | Nil                    => None
  | Unit x                 => Some x
  | More (One x) _ _       => Some x
  | More (Two x _) _ _     => Some x
  | More (Three x _ _) _ _ => Some x
  end.
```

O(1). Just reads the first element of the front digit.

### 2.2 last (symmetric, not shown in paper)

```coq
Definition last {A} (s : Seq A) : option A :=
  match s with
  | Nil                    => None
  | Unit x                 => Some x
  | More _ _ (One x)       => Some x
  | More _ _ (Two _ x)     => Some x
  | More _ _ (Three _ _ x) => Some x
  end.
```

O(1). Reads the last element of the rear digit.

---

## 3. Non-recursive Helpers

### 3.1 map1 (paper Section 6, updated in Section 8)

Applies a function to *only the first element* of a sequence.
Non-recursive — O(1).

```coq
Definition map1 {A} (f : A -> A) (s : Seq A) : Seq A :=
  match s with
  | Nil                    => Nil        (* not reached in practice *)
  | Unit x                 => Unit (f x)
  | More (One x) q u       => More (One (f x)) q u
  | More (Two x y) q u     => More (Two (f x) y) q u
  | More (Three x y z) q u => More (Three (f x) y z) q u
  end.
```

**Why this works:** `map1` does not recurse into the spine `q`.
It only touches the front digit. This is the key to the O(1)
`Triple` case in `tail`.

**Important constraint:** `map1` requires `f : A -> A` (same
input and output type). This is satisfied because `chop : Tuple A -> Tuple A`.

### 3.2 mapLast (symmetric, not shown in paper)

Applies a function to *only the last element* of a sequence.
Non-recursive — O(1).

```coq
Definition mapLast {A} (f : A -> A) (s : Seq A) : Seq A :=
  match s with
  | Nil                    => Nil
  | Unit x                 => Unit (f x)
  | More f' q (One x)       => More f' q (One (f x))
  | More f' q (Two x y)     => More f' q (Two x (f y))
  | More f' q (Three x y z) => More f' q (Three x y (f z))
  end.
```

### 3.3 chop (paper Section 8, defined inline in more0)

Trims a `Triple` to a `Pair` by removing its first element:

```coq
Definition chop {A} (t : Tuple A) : Tuple A :=
  match t with
  | Triple _ y z => Pair y z
  | p            => p        (* only called on Triples *)
  end.
```

### 3.4 chopLast (symmetric, not shown in paper)

Trims a `Triple` to a `Pair` by removing its last element:

```coq
Definition chopLast {A} (t : Tuple A) : Tuple A :=
  match t with
  | Triple a b _ => Pair a b
  | p            => p
  end.
```

---

## 4. Insertion

### 4.1 cons (paper Section 8)

```coq
Fixpoint cons {A} (x : A) (s : Seq A) : Seq A :=
  match s with
  | Nil                    => Unit x
  | Unit y                 => More (One x) Nil (One y)
  | More (One a) m r       => More (Two x a) m r
  | More (Two a b) m r     => More (Three x a b) m r
  | More (Three a b c) m r => More (Two x a) (cons (Pair b c) m) r
  end.
```

**Case-by-case:**

1. **Nil → Unit x**: trivial.
2. **Unit y → More (One x) Nil (One y)**: promote to `More` with
   singleton front/rear digits and empty spine.
3. **One a → Two x a**: front has room, just grow. O(1), no recursion.
4. **Two a b → Three x a b**: front has room, just grow. O(1), no recursion.
5. **Three a b c → Two x a, push Pair b c**: front overflows.
   Keep `x` and `a` in front as `Two x a` (safe digit).
   Pair up `b` and `c` into `Pair b c` and push into middle. **Recursive.**

**Critical design choice in case 5:** We leave `Two x a` (safe) at the top,
not `One x` (dangerous). And we push `Pair b c`, not `Triple a b c`.
The paper explicitly warns: "it is very important that we choose [Two]"
because `Two` won't trigger recursion on the *next* `cons` or `tail`.

### 4.2 snoc (symmetric, not shown in paper)

```coq
Fixpoint snoc {A} (s : Seq A) (x : A) : Seq A :=
  match s with
  | Nil                    => Unit x
  | Unit y                 => More (One y) Nil (One x)
  | More f m (One a)       => More f m (Two a x)
  | More f m (Two a b)     => More f m (Three a b x)
  | More f m (Three a b c) => More f (snoc m (Pair a b)) (Two c x)
  end.
```

Symmetric: overflow on `Three a b c` in rear pairs up `(a, b)` into
the middle, keeping `Two c x` as the new rear.

---

## 5. Deletion

### 5.1 tail (paper Section 8)

The paper defines `tail` using a helper `more0` for the underflow case.
Here we present them together as `uncons` (returning both the removed
element and the remainder), which is closer to what the demand function
needs.

First, the paper's presentation:

```haskell
-- Paper's tail
tail :: Seq a -> Seq a
tail (Unit _)              = Nil
tail (More (Three _ x y) q u) = More (Two x y) q u
tail (More (Two _ x) q u)     = More (One x) q u
tail (More (One _) q u)       = more0 q u

-- Paper's more0
more0 :: Seq (Tuple a) -> Some a -> Seq a
more0 Nil (One y)          = Unit y
more0 Nil (Two y z)        = More (One y) Nil (One z)
more0 Nil (Three y z w)    = More (One y) Nil (Two z w)
more0 q u =
  case head q of
    Pair x y     -> More (Two x y) (tail q) u
    Triple x _ _ -> More (One x) (map1 chop q) u
      where chop (Triple _ y z) = Pair y z
```

**Case analysis in more0 (the interesting part):**

When the front digit is `One`, removing it empties the front.
We must refill from the middle spine `q`:

1. **Middle empty, rear is One a**: collapse to `Unit a`.
2. **Middle empty, rear is Two a b**: rebuild as `More (One a) Nil (One b)`.
3. **Middle empty, rear is Three a b c**: rebuild as `More (One a) Nil (Two b c)`.
4. **Middle non-empty, head is Pair x y**: install `Two x y` as the new
   front (safe digit!), then recursively `tail` the middle to remove the
   pair. **This is the expensive recursive case.**
5. **Middle non-empty, head is Triple x y z**: install `One x` as the new
   front, then use `map1 chop` to transform the `Triple x y z` into
   `Pair y z` *in place*. **No recursion!** O(1) because `map1` is
   non-recursive.

**Why case 5 doesn't recurse:** The `Triple` has 3 elements. We take 1
for the front digit, and the remaining 2 fit in a `Pair`. We just
rewrite the tuple in place (via `map1 chop`). The spine structure
doesn't change — same number of tuples, one just got smaller.

**Why case 4 leaves Two (safe):** Same reasoning as `cons` — after a
recursive call, leave a safe digit so the *next* operation doesn't
also recurse.

### 5.2 Combined as uncons (for demand function compatibility)

```coq
Fixpoint uncons {A} (s : Seq A) : option (A * Seq A) :=
  match s with
  | Nil => None
  | Unit x => Some (x, Nil)
  | More (Three x a b) m r => Some (x, More (Two a b) m r)
  | More (Two x a) m r     => Some (x, More (One a) m r)
  | More (One x) m r =>
      match head m with
      | None =>
          (* Middle empty — restructure from rear *)
          match r with
          | One a       => Some (x, Unit a)
          | Two a b     => Some (x, More (One a) Nil (One b))
          | Three a b c => Some (x, More (One a) Nil (Two b c))
          end
      | Some (Pair a b) =>
          (* Pair: install Two a b, recurse to remove from middle *)
          match uncons m with
          | Some (_, m') => Some (x, More (Two a b) m' r)
          | None => None  (* unreachable *)
          end
      | Some (Triple a _ _) =>
          (* Triple: install One a, chop in place — no recursion *)
          Some (x, More (One a) (map1 chop m) r)
      end
  end.
```

**Note on the Pair case:** We call `head m` to inspect the tuple, then
`uncons m` to actually remove it. In the pure (strict) version this
inspects the middle twice. In the lazy version, the middle is a thunk —
forcing it once memoises the result, so the second access is free.

### 5.3 init / unsnoc (symmetric, not shown in paper)

```coq
Fixpoint unsnoc {A} (s : Seq A) : option (Seq A * A) :=
  match s with
  | Nil => None
  | Unit x => Some (Nil, x)
  | More f m (Three a b x) => Some (More f m (Two a b), x)
  | More f m (Two a x)     => Some (More f m (One a), x)
  | More f m (One x) =>
      match last m with
      | None =>
          match f with
          | One a       => Some (Unit a, x)
          | Two a b     => Some (More (One a) Nil (One b), x)
          | Three a b c => Some (More (Two a b) Nil (One c), x)
          end
      | Some (Pair a b) =>
          match unsnoc m with
          | Some (m', _) => Some (More f m' (Two a b), x)
          | None => None
          end
      | Some (Triple _ _ c) =>
          Some (More f (mapLast chopLast m) (One c), x)
      end
  end.
```

---

## 6. Append (for completeness — not verified in thesis)

### 6.1 digitToList

```coq
Definition digitToList {A} (d : Digit A) : list A :=
  match d with
  | One a       => a :: nil
  | Two a b     => a :: b :: nil
  | Three a b c => a :: b :: c :: nil
  end.
```

### 6.2 toTuples

Converts a list of 2–9 elements into a list of 1–3 tuples:

```coq
Fixpoint toTuples {A} (xs : list A) : list (Tuple A) :=
  match xs with
  | nil                       => nil
  | x :: y :: nil             => Pair x y :: nil
  | x :: y :: z :: w :: nil   => Pair x y :: Pair z w :: nil
  | x :: y :: z :: rest       => Triple x y z :: toTuples rest
  | _                         => nil  (* unreachable for valid sizes *)
  end.
```

**Size analysis:** Input is 2–9 elements, output is 1–3 tuples.
The function consumes elements in groups of 3 (as `Triple`s),
except when 2 or 4 remain (which become `Pair`s).

### 6.3 glue

Concatenates two sequences with a small list of elements in between:

```coq
Fixpoint glue {A} (s1 : Seq A) (xs : list A) (s2 : Seq A) : Seq A :=
  match s1, s2 with
  | Nil, _     => foldr cons s2 xs
  | _, Nil     => foldl snoc s1 xs
  | Unit x, _  => foldr cons s2 (x :: xs)
  | _, Unit y  => foldl snoc s1 (xs ++ y :: nil)
  | More u1 q1 v1, More u2 q2 v2 =>
      More u1
        (glue q1
              (map Pair_or_Triple (toTuples (digitToList v1 ++ xs ++ digitToList u2)))
              q2)
        v2
  end.
```

**Note:** The `map Pair_or_Triple` is implicit — `toTuples` already
produces `Tuple`s, and `glue` at the next level expects `list (Tuple A)`.
The size of the middle list passed to `glue` recursively is 1–3 tuples,
which fits the 0–3 size annotation.

### 6.4 append

```coq
Definition append {A} (s1 s2 : Seq A) : Seq A :=
  glue s1 nil s2.
```

---

## 7. Potential Function and Cost Functions (Section 9)

### 7.1 Potential

```coq
Definition dang {A} (d : Digit A) : nat :=
  match d with
  | One _     => 1
  | Two _ _   => 0
  | Three _ _ _ => 1
  end.

Fixpoint pot {A} (s : Seq A) : nat :=
  match s with
  | Nil        => 0
  | Unit _     => 0
  | More u q v => dang u + pot q + dang v
  end.
```

**Intuition:** `pot` counts the number of "dangerous" digits (`One` and
`Three`) across all levels of the spine. `Two` is safe and contributes 0.

Both `cons` and `tail` produce `Two` (safe) at the front when they
recurse, which *decreases* `dang` by 1. This decrease pays for the
recursion.

### 7.2 consT — actual time of cons

```coq
Fixpoint consT {A} (x : A) (s : Seq A) : nat :=
  match s with
  | Nil                    => 1
  | Unit _                 => 1
  | More (One _) _ _       => 1
  | More (Two _ _) _ _     => 1
  | More (Three _ b c) m _ => 1 + consT (Pair b c) m
  end.
```

### 7.3 tailT / more0T — actual time of tail

```coq
Fixpoint more0T {A} (m : Seq (Tuple A)) (r : Digit A) : nat :=
  match head m with
  | None             => 1
  | Some (Pair _ _)  => 1 + tailT m
  | Some (Triple _ _ _) => 1
  end

with tailT {A} (s : Seq A) : nat :=
  match s with
  | Nil                    => 0  (* not called on empty *)
  | Unit _                 => 1
  | More (Three _ _ _) _ _ => 1
  | More (Two _ _) _ _     => 1
  | More (One _) m r       => more0T m r
  end.
```

### 7.4 The proof obligations (Section 9)

The paper states these two properties:

```
consT x q + pot (cons x q) - pot q  ≤  3
tailT q   + pot (tail q)   - pot q  ≤  2
```

In words: actual time + change in potential ≤ constant.

These were verified by QuickCheck and then discharged with the
automated theorem prover E, via structural induction on `q`.

**Where the constants come from:**
- The 3 for `cons` arises when `cons x (Unit y)` creates
  `More (One x) Nil (One y)`, increasing potential from 0 to 2.
  Actual time is 1, so amortised cost = 1 + 2 = 3.
- The 2 for `tail` arises in the worst non-recursive case.

---

## 8. Summary of All Functions and Their Complexities

| Function  | Worst-case  | Amortised | Recurses? | Uses map1? |
|-----------|-------------|-----------|-----------|------------|
| head      | O(1)        | O(1)      | No        | No         |
| last      | O(1)        | O(1)      | No        | No         |
| cons      | O(log n)    | O(1)      | On Three  | No         |
| snoc      | O(log n)    | O(1)      | On Three  | No         |
| tail      | O(log n)    | O(1)      | On Pair   | On Triple  |
| init      | O(log n)    | O(1)      | On Pair   | On Triple  |
| append    | O(log n)    | O(log n)  | Always    | No         |

**The Pair/Triple distinction in tail:**
- When `tail` pulls from the middle and finds a **Pair**: it must
  recursively remove it → O(log n) worst case, but amortised O(1)
  because it leaves a safe `Two` digit.
- When `tail` pulls from the middle and finds a **Triple**: it chops
  it to a Pair via `map1 chop` → O(1) even worst case, no recursion.

---

## 9. Key Differences from ImplicitQueue.v

| Aspect | ImplicitQueue | Claessen Finger Tree |
|--------|--------------|---------------------|
| Front digit | `One \| Two` | `One \| Two \| Three` |
| Rear digit | `Zero \| One` | `One \| Two \| Three` |
| Spine element | `A * A` (pair) | `Tuple A` (Pair/Triple) |
| Operations | push, pop (one-ended) | cons, snoc, tail, init (deque) |
| tail cascade | Always recurses | Pair → recurse, Triple → chop |
| Extra helpers | — | `map1`, `chop`, `mapLast`, `chopLast` |
| Potential | front_pot only | dang(front) + pot(mid) + dang(rear) |
| append | Not supported | O(log n) via `glue` + `toTuples` |

**For the demand semantics verification:** The main new challenge vs
ImplicitQueue is that `uncons`/`unsnoc` have a **three-way branch**
(empty / Pair / Triple) instead of a two-way branch, and the Triple
case uses `map1` rather than recursion. The demand function for the
Triple case will need to track the demand through `map1` and `chop`,
which are non-recursive but still touch the spine.
