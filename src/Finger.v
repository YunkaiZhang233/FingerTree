(** * Finger Trees (Claessen 2020, simplified)
 
    Based on: "Finger trees explained anew, and slightly simplified"
    by Koen Claessen (Haskell Symposium 2020).
 
    We verify amortized constant-time deque operations (cons, snoc,
    uncons, unsnoc) using the bidirectional demand semantics and the
    reverse physicist's method from Xia et al. (ICFP 2024).
 
    The key data structure is:
 
      Seq A = Nil | Unit A | More (Digit A) (Seq (A * A)) (Digit A)
 
    where Digit A holds 1--3 elements. The recursive spine stores
    pairs, doubling the element type at each level — the same
    polymorphic recursion pattern as the implicit queue.
 
    Compared to ImplicitQueue.v:
      - Digit range widens from {1,2} to {1,2,3}
      - Both ends support insertion and deletion (deque, not queue)
      - The amortised argument uses min(|f|-1, |r|-1) for the
        debit invariant instead of the asymmetric (|f|-1)+(1-|r|)
*)
 
From Coq Require Import Arith Psatz Relations RelationClasses List.
From Clairvoyance Require Import Core Approx ApproxM Tick Prod Option.
 
Import ListNotations.
 
Import Tick.Notations.
Open Scope tick_scope.
 
Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.
 
#[local] Existing Instance Exact_id | 1.

(** Tear down goals by destructing on every match/if in context or goal. *)
Ltac teardown := repeat (simpl; match goal with
                                | [_ : context [match ?x with _ => _ end] |- _ ] => destruct x
                                | [_ : context [if ?x then _ else _] |- _ ] => destruct x
                                | |- context [match ?x with _ => _ end] => destruct x
                                | |- context [if ?x then _ else _] => destruct x
                                end).
 
Ltac keep_mgo_ :=
  mgo_; repeat (apply optimistic_thunk_go; mgo_).
 
Ltac mgo_brute_force :=
  solve [mgo_; repeat ((apply optimistic_skip + apply optimistic_thunk_go); mgo_)].
 
(** Inversion that clears the original hypothesis. *)
Tactic Notation "invert_clear" hyp(H) "as" simple_intropattern(pat) :=
  let H' := fresh "H'" in
  rename H into H';
  let HI := fresh "HI" in
  pose I as HI;
  inversion H' as pat;
  repeat lazymatch goal with
    | _ : ?type |- _ => match type with
                        | ?x = ?y => subst x + subst y
                        end
    end;
  clear HI;
  clear H'.
 
Tactic Notation "invert_clear" hyp(H) :=
  invert_clear H as [ ].
 
Tactic Notation "invert_clear" integer(n) "as" simple_intropattern(pat) :=
  progress (intros until n);
  match goal with
  | H : _ |- _ => invert_clear H as pat
  end.
 
Tactic Notation "invert_clear" integer(n) :=
  progress (intros until n);
  match goal with
  | H : _ |- _ => invert_clear H as [ ]
  end.

(* ================================================================= *)
(** ** Section 1: Pure Data Structure                                  *)
(* ================================================================= *)
 
(** *** Digits
 
    A digit holds 1, 2, or 3 elements.  In the number-system analogy,
    these are redundant digits from {1,2,3}, with 2 being "safe" and
    1, 3 being "dangerous" (one step from underflow/overflow).
 
    Compared to ImplicitQueue.v:
      Front = One | Two        (1--2, front digit)
      Rear  = Zero | One_r     (0--1, rear digit)
 
    Here both digits use the same symmetric type. *)
 
Inductive Digit (A : Type) : Type :=
  | One   : A -> Digit A
  | Two   : A -> A -> Digit A
  | Three : A -> A -> A -> Digit A.
 
Arguments One   {A}.
Arguments Two   {A}.
Arguments Three {A}.

(** *** The Sequence Type
 
    The core finger tree / implicit deque.
 
    Nil   — empty sequence
    Unit  — singleton (no digits, no spine)
    More  — front digit, lazy middle of pairs, rear digit
 
    The middle [m : Seq (A * A)] is the polymorphic recursion:
    level 0 stores A, level 1 stores A*A, level 2 stores
    (A*A)*(A*A), etc.  Each element at level k represents 2^k
    original elements.
 
    Note: in the lazy version, the [m] field would be wrapped in
    a thunk.  Here we give the pure (strict) reference implementation
    first; the lazy/approximated version comes in Section 2. *)
 
Inductive Seq (A : Type) : Type :=
  | Nil  : Seq A
  | Unit : A -> Seq A
  | More : Digit A -> Seq (A * A) -> Digit A -> Seq A.
 
Arguments Nil  {A}.
Arguments Unit {A}.
Arguments More {A}.

(* ================================================================= *)
(** ** Operations                                                      *)
(* ================================================================= *)
 
(** *** cons — insert at the front
 
    Three cases:
    - [Nil]: become a singleton.
    - [Unit y]: promote to [More] with front [One x], rear [One y],
      empty middle.
    - [More f m r]:
      + [f = One a]:     grow to [Two x a].
      + [f = Two a b]:   grow to [Three x a b].
      + [f = Three a b c]: overflow!  Keep [Two x a] in front,
        pair up [(b, c)] and cons the pair into the middle.
        The front goes from dangerous (Three) to safe (Two). *)
 
Fixpoint cons {A : Type} (x : A) (s : Seq A) : Seq A :=
  match s with
  | Nil              => Unit x
  | Unit y           => More (One x) Nil (One y)
  | More (One a) m r       => More (Two x a) m r
  | More (Two a b) m r     => More (Three x a b) m r
  | More (Three a b c) m r => More (Two x a) (cons (b, c) m) r
  end.
 
(** *** snoc — insert at the rear
 
    Symmetric to [cons].  Overflow on the rear digit [Three a b c]
    pairs up [(a, b)] and snocs into the middle, keeping [Two c x]
    as the new rear. *)
 
Fixpoint snoc {A : Type} (s : Seq A) (x : A) : Seq A :=
  match s with
  | Nil              => Unit x
  | Unit y           => More (One y) Nil (One x)
  | More f m (One a)       => More f m (Two a x)
  | More f m (Two a b)     => More f m (Three a b x)
  | More f m (Three a b c) => More f (snoc m (a, b)) (Two c x)
  end.
 
(** *** head — peek at the front element *)
 
Definition head {A : Type} (s : Seq A) : option A :=
  match s with
  | Nil                    => None
  | Unit x                 => Some x
  | More (One x) _ _       => Some x
  | More (Two x _) _ _     => Some x
  | More (Three x _ _) _ _ => Some x
  end.
 
(** *** last — peek at the rear element *)
 
Definition last {A : Type} (s : Seq A) : option A :=
  match s with
  | Nil                    => None
  | Unit x                 => Some x
  | More _ _ (One x)       => Some x
  | More _ _ (Two _ x)     => Some x
  | More _ _ (Three _ _ x) => Some x
  end.
 
(** *** tail — remove from the front
 
    When the front digit is [Two] or [Three], we just shrink it.
    When it is [One], we must pull a pair from the middle to refill.
 
    If the middle is empty, we restructure from the rear digit alone.
    If the middle is non-empty, we extract its head pair [(a, b)],
    install [Two a b] as the new front, and tail the middle.
 
    Returns [None] if the sequence is empty, [Some (x, s')] where
    [x] is the removed element and [s'] is the remaining sequence. *)
 
Fixpoint uncons {A : Type} (s : Seq A) : option (A * Seq A) :=
  match s with
  | Nil => None
  | Unit x => Some (x, Nil)
  | More (Three x a b) m r => Some (x, More (Two a b) m r)
  | More (Two x a) m r     => Some (x, More (One a) m r)
  | More (One x) m r =>
      match uncons m with
      | Some ((a, b), m') => Some (x, More (Two a b) m' r)
      | None =>
          match r with
          | One a         => Some (x, Unit a)
          | Two a b       => Some (x, More (One a) Nil (One b))
          | Three a b c   => Some (x, More (One a) Nil (Two b c))
          end
      end
  end.
 
(** *** unsnoc — remove from the rear
 
    Symmetric to [uncons]. *)
 
Fixpoint unsnoc {A : Type} (s : Seq A) : option (Seq A * A) :=
  match s with
  | Nil => None
  | Unit x => Some (Nil, x)
  | More f m (Three a b x) => Some (More f m (Two a b), x)
  | More f m (Two a x)     => Some (More f m (One a), x)
  | More f m (One x) =>
      match unsnoc m with
      | Some (m', (a, b)) => Some (More f m' (Two a b), x)
      | None =>
          match f with
          | One a         => Some (Unit a, x)
          | Two a b       => Some (More (One a) Nil (One b), x)
          | Three a b c   => Some (More (Two a b) Nil (One c), x)
          end
      end
  end.
 
(** *** Derived convenience functions *)
 
Definition tail {A : Type} (s : Seq A) : option (Seq A) :=
  match uncons s with
  | Some (_, s') => Some s'
  | None         => None
  end.
 
Definition init {A : Type} (s : Seq A) : option (Seq A) :=
  match unsnoc s with
  | Some (s', _) => Some s'
  | None         => None
  end.

(* ================================================================= *)
(** ** Conversion to lists (specification / extraction)                *)
(* ================================================================= *)
 
(** We flatten a [Digit] to a list, then use it to define [toList]
    for [Seq].  This serves as the functional correctness specification:
    every operation on [Seq] must agree with the corresponding list
    operation when viewed through [toList]. *)
 
Definition digitToList {A : Type} (d : Digit A) : list A :=
  match d with
  | One a       => a :: nil
  | Two a b     => a :: b :: nil
  | Three a b c => a :: b :: c :: nil
  end.
 
(** [toList] requires a "flattener" for elements, because at deeper
    levels of the spine, elements are pairs (or pairs of pairs, etc.).
    We parameterise by a function [f : A -> list B] that recursively
    flattens compound elements to lists of base elements. *)
 
Fixpoint toListWith {A B : Type} (f : A -> list B) (s : Seq A) : list B :=
  match s with
  | Nil          => nil
  | Unit x       => f x
  | More fr m rr =>
      List.flat_map f (digitToList fr)
      ++ toListWith (fun '(a, b) => f a ++ f b) m
      ++ List.flat_map f (digitToList rr)
  end.
 
Definition toList {A : Type} (s : Seq A) : list A :=
  toListWith (fun x => x :: nil) s.  