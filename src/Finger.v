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
(** ** Shared utilities (mirrors ImplicitQueue.v preamble)             *)
(* ================================================================= *)

Lemma make_partial_order A (R : A -> A -> Prop) `{PreOrder A R} :
  (forall (x y : A), R x y -> R y x -> x = y) -> PartialOrder eq R.
Proof.
  intros.
  unfold PartialOrder, relation_equivalence, predicate_equivalence, pointwise_lifting,
    relation_conjunction, predicate_intersection, pointwise_extension, Basics.flip.
  split.
  - destruct 1. split; reflexivity.
  - intros [ H1 H2 ]. apply H0; auto.
Qed.

Lemma LessDefined_T_antisym A `{LessDefined A} :
  (forall (x y : A), x `less_defined` y -> y `less_defined` x -> x = y) ->
  forall (x y : T A), x `less_defined` y -> y `less_defined` x -> x = y.
Proof.
  intro. repeat invert_clear 1; try f_equal; auto.
Qed.
#[global] Hint Resolve LessDefined_T_antisym : core.

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

(* ================================================================= *)
(** ** Section 2: Approximation Types                                  *)
(* ================================================================= *)

(** *** DigitA — approximated digit

    Mirrors [Digit] but with each element wrapped in [T] so that
    individual elements can be marked as undefined (not demanded).
    There is no [DigitBot] constructor: the "no demand on this digit
    slot" level of approximation is provided by [T (DigitA A)] in
    [SeqA], where [Undefined] represents zero demand on the whole
    digit.

    This follows the same pattern as [FrontA]/[RearA] in ImplicitQueue.v,
    which use [T A] fields rather than a dedicated bottom constructor. *)

Inductive DigitA (A : Type) : Type :=
| OneA   : T A -> DigitA A
| TwoA   : T A -> T A -> DigitA A
| ThreeA : T A -> T A -> T A -> DigitA A.

#[global] Hint Constructors DigitA : core.

Arguments OneA   {A}.
Arguments TwoA   {A}.
Arguments ThreeA {A}.

(** *** LessDefined for DigitA

    Approximation order: pointwise on matching constructors.
    Different constructors are incomparable — there is no "bot" row. *)

Inductive LessDefined_DigitA A `{LessDefined A} : LessDefined (DigitA A) :=
| LessDefined_OneA x1 x2 :
    x1 `less_defined` x2 ->
    OneA x1 `less_defined` OneA x2
| LessDefined_TwoA x1 x2 y1 y2 :
    x1 `less_defined` x2 -> y1 `less_defined` y2 ->
    TwoA x1 y1 `less_defined` TwoA x2 y2
| LessDefined_ThreeA x1 x2 y1 y2 z1 z2 :
    x1 `less_defined` x2 -> y1 `less_defined` y2 -> z1 `less_defined` z2 ->
    ThreeA x1 y1 z1 `less_defined` ThreeA x2 y2 z2.

#[global] Hint Constructors LessDefined_DigitA : core.
#[global] Existing Instance LessDefined_DigitA.

Lemma LessDefined_DigitA_refl A `{LessDefined A} :
  (forall (x : A), x `less_defined` x) ->
  forall (d : DigitA A), d `less_defined` d.
Proof.
  destruct d;
    repeat match goal with t : T A |- _ => destruct t end;
    auto.
Qed.
#[global] Hint Resolve LessDefined_DigitA_refl : core.

#[global] Instance Reflexive_LessDefined_DigitA A `{LessDefined A, Reflexive A less_defined} :
  Reflexive (@less_defined (DigitA A) _).
Proof.
  unfold Reflexive. auto.
Qed.

Lemma LessDefined_DigitA_trans A `{LessDefined A} :
  (forall (x y z : A), x `less_defined` y -> y `less_defined` z -> x `less_defined` z) ->
  forall (x y z : DigitA A),
    x `less_defined` y -> y `less_defined` z -> x `less_defined` z.
Proof.
  intro.
  repeat invert_clear 1;
    repeat match goal with
      | H : ?x `less_defined` ?y |- _ => invert_clear H
      end;
    repeat constructor; eauto.
Qed.
#[global] Hint Resolve LessDefined_DigitA_trans : core.

#[global] Instance Transitive_LessDefined_DigitA A `{LessDefined A, Transitive A less_defined} :
  Transitive (@less_defined (DigitA A) _).
Proof.
  unfold Transitive. eauto.
Qed.

#[global] Instance PreOrder_LessDefined_DigitA A `{LDA : LessDefined A, PreOrder A LDA} :
  PreOrder (@less_defined (DigitA A) _).
Proof.
  destruct H. constructor; eauto.
Qed.

Lemma LessDefined_DigitA_antisym A `{LessDefined A} :
  (forall (x y : A), x `less_defined` y -> y `less_defined` x -> x = y) ->
  forall (x y : DigitA A),
    x `less_defined` y -> y `less_defined` x -> x = y.
Proof.
  intro.
  repeat inversion_clear 1;
    repeat match goal with
      | H : ?x `less_defined` ?y |- _ => invert_clear H
      end;
    f_equal; eauto.
Qed.
#[global] Hint Resolve LessDefined_DigitA_antisym : core.

#[global] Instance PartialOrder_LessDefined_DigitA A
  `{LessDefined A, PartialOrder A eq less_defined} :
  PartialOrder eq (@less_defined (DigitA A) _).
Proof.
  apply make_partial_order. apply LessDefined_DigitA_antisym. firstorder.
Qed.

(** *** Exact for Digit / DigitA

    Embeds a pure [Digit A] into [DigitA B].  Each element [x : A] maps
    to [exact x : T B] via the [Exact_T] instance, which wraps it in
    [Thunk]. *)

#[global] Instance Exact_Digit A B `{Exact A B} : Exact (Digit A) (DigitA B) :=
  fun d => match d with
           | One x       => OneA   (exact x)
           | Two x y     => TwoA   (exact x) (exact y)
           | Three x y z => ThreeA (exact x) (exact y) (exact z)
           end.

(** [exact] produces maximal elements: if [exact d ⊑ dA] then [exact d = dA]. *)
#[global] Instance ExactMaximal_Digit A B `{ExactMaximal B A} :
  ExactMaximal (DigitA B) (Digit A).
Proof.
  intros dA []; unfold exact, Exact_Digit; inversion 1; subst; f_equal.
  - destruct x2; unfold exact, Exact_T.
    + f_equal. apply H. inversion H2; subst. assumption.
    + inversion H2.
  - destruct x2; unfold exact, Exact_T.
    + f_equal. apply H. inversion H3; subst. assumption.
    + inversion H3.
  - destruct y2; unfold exact, Exact_T.
    + f_equal. apply H. inversion H5; subst. assumption.
    + inversion H5.
  - destruct x2; unfold exact, Exact_T.
    + f_equal. apply H. inversion H4; subst. assumption.
    + inversion H4.
  - destruct y2; unfold exact, Exact_T.
    + f_equal. apply H. inversion H6; subst. assumption.
    + inversion H6.
  - destruct z2; unfold exact, Exact_T.
    + f_equal. apply H. inversion H7; subst. assumption.
    + inversion H7.
Qed.

(** *** Lub for DigitA

    Pointwise on matching constructors; incompatible constructors
    return [OneA Undefined] as a dummy (the LubLaw only requires
    [x ⊑ lub x y] when [cobounded x y], which never holds for
    different constructors). *)

#[global] Instance Lub_DigitA (A : Type) `{Lub A} : Lub (DigitA A) :=
  fun d1 d2 =>
    match d1, d2 with
    | OneA x1,         OneA x2         => OneA   (lub x1 x2)
    | TwoA x1 y1,      TwoA x2 y2      => TwoA   (lub x1 x2) (lub y1 y2)
    | ThreeA x1 y1 z1, ThreeA x2 y2 z2 => ThreeA (lub x1 x2) (lub y1 y2) (lub z1 z2)
    | _, _                              => OneA Undefined
    end.

#[global] Instance LubLaw_DigitA (A : Type)
  `{LDA : LessDefined A, Reflexive A less_defined, LBA : Lub A, @LubLaw _ LBA LDA} :
  LubLaw (DigitA A).
Proof.
  split.
  - repeat invert_clear 1; repeat constructor; apply lub_least_upper_bound; auto.
  - invert_clear 1. invert_clear H1.
    invert_clear H1; invert_clear H2; repeat constructor; apply lub_upper_bound_l; eauto.
  - invert_clear 1. invert_clear H1.
    invert_clear H1; invert_clear H2; repeat constructor; apply lub_upper_bound_r; eauto.
Qed.  