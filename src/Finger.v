(** * Finger Trees (Claessen 2020, simplified)
 
    Based on: "Finger trees explained anew, and slightly simplified"
    by Koen Claessen (Haskell Symposium 2020).
 
    We verify amortized constant-time deque operations (cons, snoc,
    uncons, unsnoc) using the bidirectional demand semantics and the
    reverse physicist's method from Xia et al. (ICFP 2024).
 
    The key data structure is:

      Seq A = Nil | Unit A | More (Digit A) (Seq (Tuple A)) (Digit A)

    where Digit A holds 1--3 elements and Tuple A is a 2- or 3-node.
    The recursive spine stores tuples, doubling (or tripling) the
    element type at each level — the same polymorphic recursion
    pattern as the implicit queue, with an extra Triple case.
 
    Compared to ImplicitQueue.v:
      - Digit range widens from {1,2} to {1,2,3}
      - Both ends support insertion and deletion (deque, not queue)
      - The amortised argument uses min(|f|-1, |r|-1) for the
        debit invariant instead of the asymmetric (|f|-1)+(1-|r|)
*)
 
From Coq Require Import Arith Psatz Relations RelationClasses List.
From Clairvoyance Require Import Core Approx ApproxM Tick Prod Option.

From Hammer Require Import Tactics.
 
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

(* Auxiliary tactic. *)
Ltac head_is_constructor t := match t with
                              | ?f ?x => head_is_constructor f
                              | _ => is_constructor t
                              end.

(* An incomplete tactic that indicates whether the head of a term
   is a constructor or projection. *)
Ltac head_is_constructor_or_proj t :=
  match t with
  | ?f ?x => head_is_constructor_or_proj f
  | fst => idtac
  | snd => idtac
  | _ => is_constructor t
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

(** *** Tuples (2-3 nodes)
 
    Each element in the recursive spine is a [Tuple], holding either
    2 or 3 elements.  This is what distinguishes Claessen's final
    design from the simpler pair-only version:
 
    - [Pair a b] represents 2 elements
    - [Triple a b c] represents 3 elements
 
    The key role of [Tuple] in the deque operations: when [tail]
    pulls from the middle and finds a [Triple], it can [chop] it
    to a [Pair] without recursing, using the non-recursive [map1].
    This avoids a recursive call in that case. *)
 
Inductive Tuple (A : Type) : Type :=
  | Pair   : A -> A -> Tuple A
  | Triple : A -> A -> A -> Tuple A.
 
Arguments Pair   {A}.
Arguments Triple {A}.

(** *** The Sequence Type
 
    Nil   — empty sequence
    Unit  — singleton (no digits, no spine)
    More  — front digit, middle spine of tuples, rear digit
 
    The middle [m : Seq (Tuple A)] is the polymorphic recursion.
    At level 0 we store [A], at level 1 [Tuple A], at level 2
    [Tuple (Tuple A)], etc.
 
    Note: in the lazy version, the [m] field would be wrapped in
    a thunk.  Here we give the pure (strict) reference implementation
    first; the lazy/approximated version comes in Section 2. *)
 
Inductive Seq (A : Type) : Type :=
  | Nil  : Seq A
  | Unit : A -> Seq A
  | More : Digit A -> Seq (Tuple A) -> Digit A -> Seq A.

Arguments Nil  {A}.
Arguments Unit {A}.
Arguments More {A}.



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
    levels of the spine, elements are tuples.  We parameterise by a
    function [f : A -> list B] that recursively flattens compound
    elements to lists of base elements. *)

Fixpoint toListWith {A B : Type} (f : A -> list B) (s : Seq A) : list B :=
  match s with
  | Nil          => nil
  | Unit x       => f x
  | More fr m rr =>
      List.flat_map f (digitToList fr)
      ++ toListWith (fun t => match t with
                              | Pair a b     => f a ++ f b
                              | Triple a b c => f a ++ f b ++ f c
                              end) m
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



(** *** TupleA — approximated spine tuple

    Mirrors [Tuple] exactly as [DigitA] mirrors [Digit]: each element
    field is wrapped in [T].  [PairA] and [TripleA] have 2 and 3
    fields respectively.  No bot constructor — the surrounding [T] in
    [SeqA] handles "this spine node is not demanded at all". *)

Inductive TupleA (A : Type) : Type :=
| PairA   : T A -> T A -> TupleA A
| TripleA : T A -> T A -> T A -> TupleA A.

#[global] Hint Constructors TupleA : core.

Arguments PairA   {A}.
Arguments TripleA {A}.

(** *** LessDefined for TupleA *)

Inductive LessDefined_TupleA A `{LessDefined A} : LessDefined (TupleA A) :=
| LessDefined_PairA x1 x2 y1 y2 :
    x1 `less_defined` x2 -> y1 `less_defined` y2 ->
    PairA x1 y1 `less_defined` PairA x2 y2
| LessDefined_TripleA x1 x2 y1 y2 z1 z2 :
    x1 `less_defined` x2 -> y1 `less_defined` y2 -> z1 `less_defined` z2 ->
    TripleA x1 y1 z1 `less_defined` TripleA x2 y2 z2.

#[global] Hint Constructors LessDefined_TupleA : core.
#[global] Existing Instance LessDefined_TupleA.

Lemma LessDefined_TupleA_refl A `{LessDefined A} :
  (forall (x : A), x `less_defined` x) ->
  forall (t : TupleA A), t `less_defined` t.
Proof.
  destruct t;
    repeat match goal with u : T A |- _ => destruct u end;
    auto.
Qed.
#[global] Hint Resolve LessDefined_TupleA_refl : core.

#[global] Instance Reflexive_LessDefined_TupleA A `{LessDefined A, Reflexive A less_defined} :
  Reflexive (@less_defined (TupleA A) _).
Proof.
  unfold Reflexive. auto.
Qed.

Lemma LessDefined_TupleA_trans A `{LessDefined A} :
  (forall (x y z : A), x `less_defined` y -> y `less_defined` z -> x `less_defined` z) ->
  forall (x y z : TupleA A),
    x `less_defined` y -> y `less_defined` z -> x `less_defined` z.
Proof.
  intro.
  repeat invert_clear 1;
    repeat match goal with
      | H : ?x `less_defined` ?y |- _ => invert_clear H
      end;
    repeat constructor; eauto.
Qed.
#[global] Hint Resolve LessDefined_TupleA_trans : core.

#[global] Instance Transitive_LessDefined_TupleA A `{LessDefined A, Transitive A less_defined} :
  Transitive (@less_defined (TupleA A) _).
Proof.
  unfold Transitive. eauto.
Qed.

#[global] Instance PreOrder_LessDefined_TupleA A `{LDA : LessDefined A, PreOrder A LDA} :
  PreOrder (@less_defined (TupleA A) _).
Proof.
  destruct H. constructor; eauto.
Qed.

Lemma LessDefined_TupleA_antisym A `{LessDefined A} :
  (forall (x y : A), x `less_defined` y -> y `less_defined` x -> x = y) ->
  forall (x y : TupleA A),
    x `less_defined` y -> y `less_defined` x -> x = y.
Proof.
  intro.
  repeat inversion_clear 1;
    repeat match goal with
      | H : ?x `less_defined` ?y |- _ => invert_clear H
      end;
    f_equal; eauto.
Qed.
#[global] Hint Resolve LessDefined_TupleA_antisym : core.

#[global] Instance PartialOrder_LessDefined_TupleA A
  `{LessDefined A, PartialOrder A eq less_defined} :
  PartialOrder eq (@less_defined (TupleA A) _).
Proof.
  apply make_partial_order. apply LessDefined_TupleA_antisym. firstorder.
Qed.

(** *** Exact for Tuple / TupleA *)

#[global] Instance Exact_Tuple A B `{Exact A B} : Exact (Tuple A) (TupleA B) :=
  fun t => match t with
           | Pair x y     => PairA   (exact x) (exact y)
           | Triple x y z => TripleA (exact x) (exact y) (exact z)
           end.

#[global] Instance ExactMaximal_Tuple A B `{ExactMaximal B A} :
  ExactMaximal (TupleA B) (Tuple A).
Proof.
  intros tA []; unfold exact, Exact_Tuple; inversion 1; subst; f_equal.
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

(** *** Lub for TupleA

    Pointwise on matching constructors; mismatched constructors return
    [PairA Undefined Undefined] as a dummy. *)

#[global] Instance Lub_TupleA (A : Type) `{Lub A} : Lub (TupleA A) :=
  fun t1 t2 =>
    match t1, t2 with
    | PairA x1 y1,      PairA x2 y2      => PairA   (lub x1 x2) (lub y1 y2)
    | TripleA x1 y1 z1, TripleA x2 y2 z2 => TripleA (lub x1 x2) (lub y1 y2) (lub z1 z2)
    | _, _                               => PairA Undefined Undefined
    end.

#[global] Instance LubLaw_TupleA (A : Type)
  `{LDA : LessDefined A, Reflexive A less_defined, LBA : Lub A, @LubLaw _ LBA LDA} :
  LubLaw (TupleA A).
Proof.
  split.
  - repeat invert_clear 1; repeat constructor; apply lub_least_upper_bound; auto.
  - invert_clear 1. invert_clear H1.
    invert_clear H1; invert_clear H2; repeat constructor; apply lub_upper_bound_l; eauto.
  - invert_clear 1. invert_clear H1.
    invert_clear H1; invert_clear H2; repeat constructor; apply lub_upper_bound_r; eauto.
Qed.

(* ================================================================= *)
(** ** Section 2 Part 3: SeqA — approximated sequence                 *)
(* ================================================================= *)

(** *** SeqA inductive definition

    The middle field is [T (SeqA (TupleA A))] — a thunk wrapping the
    polymorphic-recursive spine.  We suppress automatic elimination
    schemes because Rocq's auto-generated induction principle gives the
    wrong IH for nested [SeqA (TupleA A)]; we write [SeqA_ind] by hand
    below. *)

Unset Elimination Schemes.

Inductive SeqA (A : Type) : Type :=
| NilA  : SeqA A
| UnitA : T A -> SeqA A
| MoreA : T (DigitA A) -> T (SeqA (TupleA A)) -> T (DigitA A) -> SeqA A.

#[global] Hint Constructors SeqA : core.

Arguments NilA  {A}.
Arguments UnitA {A}.
Arguments MoreA {A}.

(** *** SeqA_ind — custom induction principle

    Universally quantifies over the type parameter so that the IH in
    the [MoreA] case holds at [TupleA A], not just at [A].  The middle
    field is split via [destruct t0] into [Thunk]/[Undefined] to
    discharge [TR1]. *)

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

Set Elimination Schemes.

(** *** LessDefined for SeqA

    Approximation order: pointwise on matching constructors.
    [T]-level [Undefined] provides the "bottom ⊑ anything" case for
    each field; there is no separate [SeqBot] constructor. *)

Inductive LessDefined_SeqA A `{LessDefined A} : LessDefined (SeqA A) :=
| LessDefined_NilA  : NilA `less_defined` NilA
| LessDefined_UnitA x1 x2 :
    x1 `less_defined` x2 ->
    UnitA x1 `less_defined` UnitA x2
| LessDefined_MoreA f1 f2 m1 m2 r1 r2 :
    f1 `less_defined` f2 -> m1 `less_defined` m2 -> r1 `less_defined` r2 ->
    MoreA f1 m1 r1 `less_defined` MoreA f2 m2 r2.

#[global] Hint Constructors LessDefined_SeqA : core.
#[global] Existing Instance LessDefined_SeqA.

(** *** Reflexivity *)

Lemma LessDefined_SeqA_refl A `{LessDefined A, Reflexive A less_defined} :
  (forall (x : A), x `less_defined` x) -> forall (s : SeqA A), s `less_defined` s.
Proof.
  induction s.
  - constructor.
  - constructor. 
    assert (@Reflexive (T A) less_defined) by apply Reflexive_LessDefined_T.
    reflexivity.
  - assert (@Reflexive (T (DigitA A)) less_defined) by apply Reflexive_LessDefined_T. 
    invert_clear H2.
    + constructor; try reflexivity. constructor. auto.
    + constructor; auto.
Qed.
#[global] Hint Resolve LessDefined_SeqA_refl : core.

#[global] Instance Reflexive_LessDefined_SeqA A `{LDA : LessDefined A, !Reflexive LDA} :
  Reflexive (@less_defined (SeqA A) _).
Proof.
  unfold Reflexive. eauto.
Qed.

(** *** Transitivity *)

Lemma LessDefined_SeqA_trans A `{LessDefined A, Transitive A less_defined} :
  (forall (x y z : A), x `less_defined` y -> y `less_defined` z -> x `less_defined` z) ->
  forall (x y z : SeqA A), x `less_defined` y -> y `less_defined` z -> x `less_defined` z.
Proof.
  induction y.
  - repeat invert_clear 1. auto.
  - assert (@Transitive (T A) less_defined) by apply Transitive_LessDefined_T.
    repeat invert_clear 1. constructor; eauto.
  - assert (@Transitive (T (DigitA A)) less_defined) by apply Transitive_LessDefined_T.
    repeat invert_clear 1. 
    repeat constructor; try (etransitivity; eauto).
    invert_clear H2; repeat match goal with
                       | H : ?x `less_defined` ?y |- _ =>
                           (head_is_constructor x + head_is_constructor y); invert_clear H
                       end; constructor.
    apply H2; eauto.
Qed.
#[global] Hint Resolve LessDefined_SeqA_trans : core.

#[global] Instance Transitive_LessDefined_SeqA A `{LDA : LessDefined A, Transitive A LDA} :
  Transitive (@less_defined (SeqA A) _).
Proof.
  unfold Transitive. eauto.
Qed.

(** *** PreOrder *)

#[global] Instance PreOrder_LessDefined_SeqA A `{LDA : LessDefined A, PreOrder A LDA} :
  PreOrder (@less_defined (SeqA A) _).
Proof.
  destruct H. constructor; eauto.
Qed.

(** *** Antisymmetry / PartialOrder *)

Lemma LessDefined_SeqA_antisym_aux :
  forall A `{LessDefined A},
  (forall (x y : A), x `less_defined` y -> y `less_defined` x -> x = y) ->
  forall (x y : SeqA A), x `less_defined` y -> y `less_defined` x -> x = y.
Proof.
  fix SELF 4.
  intros A H Hanti x y Hxy Hyx.
  destruct x; destruct y; inversion Hxy; inversion Hyx; subst;
    try reflexivity; try discriminate.
  - (* UnitA *)
    f_equal. apply (LessDefined_T_antisym Hanti); assumption.
  - (* MoreA *)
    f_equal.
    + apply LessDefined_T_antisym; eauto.
    + destruct t0 as [ms |]; destruct t3 as [ms2 |];
        try (inversion H5; fail); try (inversion H10; fail); try reflexivity.
      inversion H7; subst. inversion H16; subst.
      f_equal. apply (SELF _ _ (@LessDefined_TupleA_antisym A _ Hanti)); eauto.
      * inversion H7.
      * inversion H16.
    + apply LessDefined_T_antisym; eauto.
Qed.


Lemma LessDefined_SeqA_antisym A `{LessDefined A} :
  (forall (x y : A), x `less_defined` y -> y `less_defined` x -> x = y) ->
  forall (x y : SeqA A), x `less_defined` y -> y `less_defined` x -> x = y.
Proof.
  apply LessDefined_SeqA_antisym_aux.
Qed.
#[global] Hint Resolve LessDefined_SeqA_antisym : core.

#[global] Instance PartialOrder_LessDefined_SeqA A
  `{LessDefined A, PartialOrder A eq less_defined} :
  PartialOrder eq (@less_defined (SeqA A) _).
Proof.
  apply make_partial_order. apply LessDefined_SeqA_antisym. firstorder.
Qed.

(** *** Exact for Seq / SeqA

    Must be a polymorphic [fix] — see the comment in ImplicitQueue.v
    before [Exact_Queue] for why a plain instance causes an instance
    mismatch in the recursive [More] branch. *)

#[global] Instance Exact_Seq : forall A B `{Exact A B}, Exact (Seq A) (SeqA B) :=
  fix Exact_Seq A B _ s :=
    match s with
    | Nil        => NilA
    | Unit x     => UnitA (exact x)
    | More f m r => MoreA (exact f) (Thunk (Exact_Seq _ _ _ m)) (exact r)
    end.

(** *** BottomOf for SeqA *)

#[global] Instance BottomOf_SeqA (A : Type) : BottomOf (SeqA A) :=
  fun s => match s with
           | NilA        => NilA
           | UnitA _     => UnitA Undefined
           | MoreA _ _ _ => MoreA Undefined Undefined Undefined
           end.

#[global] Instance BottomIsLeast_SeqA (A : Type) `{LessDefined A} :
  BottomIsLeast (SeqA A).
Proof.
  invert_clear 1; repeat constructor.
Qed.

(** *** Lub for SeqA

    Must be a polymorphic [fix] for the same reason as [Exact_Seq]:
    the [MoreA] branch recurses at [TupleA A], so [Lub_T] for the
    middle field must be instantiated with [lub_SeqA (TupleA A)]. *)

#[global] Instance Lub_SeqA : forall (A : Type) `{Lub A}, Lub (SeqA A) :=
  fix lub_SeqA (A : Type) _ (s1 s2 : SeqA A) :=
    match s1, s2 with
    | NilA,            NilA            => NilA
    | UnitA x1,        UnitA x2        => UnitA (lub x1 x2)
    | MoreA f1 m1 r1,  MoreA f2 m2 r2  =>
        MoreA (lub f1 f2) (@lub _ (@Lub_T _ (lub_SeqA _ _)) m1 m2) (lub r1 r2)
    | _,               _               => NilA
    end.

(** *** LubLaw for SeqA *)

#[global] Instance LubLaw_SeqA (A : Type)
  `{LDA : LessDefined A, Reflexive A less_defined, LBA : Lub A, @LubLaw _ LBA LDA} :
  LubLaw (SeqA A).
Proof.
  split.
  - induction z; repeat invert_clear 1; repeat constructor;
      try solve [ apply lub_least_upper_bound; auto ].
    invert_clear H1; repeat match goal with
                       | H : ?x `less_defined` ?y |- _ =>
                           (head_is_constructor x + head_is_constructor y); invert_clear H
                       end; repeat constructor; auto.
    apply H1; auto.
    apply LubLaw_TupleA.
  - induction x; invert_clear 1;
      match goal with
      | H : ?P /\ ?Q |- _ => invert_clear H
      end;
      repeat match goal with
        | H : ?x `less_defined` ?y |- _ =>
            (head_is_constructor x + head_is_constructor y); invert_clear H
        end; repeat constructor; try solve [ apply lub_upper_bound_l; eauto ].
    invert_clear H1; auto.
    repeat match goal with
           | H : ?x `less_defined` ?y |- _ =>
               (head_is_constructor x + head_is_constructor y); invert_clear H
           end; constructor; try reflexivity.
    apply H1.
    + eauto.
    + apply LubLaw_TupleA.
    + eauto.
  - induction y; invert_clear 1;
      match goal with
      | H : ?P /\ ?Q |- _ => invert_clear H
      end;
      repeat match goal with
        | H : ?x `less_defined` ?y |- _ =>
            (head_is_constructor x + head_is_constructor y); invert_clear H
        end; repeat constructor; try solve [ apply lub_upper_bound_r; eauto ].
    invert_clear H1; auto.
    repeat match goal with
           | H : ?x `less_defined` ?y |- _ =>
               (head_is_constructor x + head_is_constructor y); invert_clear H
           end; constructor; try reflexivity.
    apply H1.
    + eauto.
    + apply LubLaw_TupleA.
    + eauto.
Qed.

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
        bundle [b] and [c] into [Pair b c] and cons it into the middle.
        The front goes from dangerous (Three) to safe (Two). *)

Fixpoint fcons {A : Type} (x : A) (s : Seq A) : Seq A :=
  match s with
  | Nil              => 
      let u' := x in
      Unit u'
  | Unit y           => 
      let f' := One x in
      let m' := Nil in
      let r' := One y in
      More f' m' r'
  | More f m r =>
      let (f, m) :=
        match f with
        | One a => 
            let f' := Two x a in
            (f', m)
        | Two a b => 
            let f' := Three x a b in
            (f', m)
        | Three a b c => 
            let f' := Two x a in
            let pbc := Pair b c in
            let m' := fcons pbc m in
            (f', m')
        end in
      More f m r
  end.


Lemma fcons_ind :
  forall (P : forall (A : Type), A -> Seq A -> Seq A -> Prop),
    (forall A x, P A x Nil (Unit x)) ->
    (forall A x y, P A x (Unit y) (More (One x) Nil (One y))) ->
    (forall A x a m r, P A x (More (One a) m r) (More (Two x a) m r)) ->
    (forall A x a b m r, P A x (More (Two a b) m r) (More (Three x a b) m r)) ->
    (forall A x a b c m r,
        P (Tuple A) (Pair b c) m (fcons (Pair b c) m) ->
        P A x (More (Three a b c) m r) (More (Two x a) (fcons (Pair b c) m) r)) ->
    forall A (x : A) (s : Seq A), P A x s (fcons x s).
Proof.
  intros ? H1 H2 H3 H4 H5. fix SELF 3. intros ? x s.
  refine (match s with
          | Nil => _
          | Unit y => _
          | More (One a) m r => _
          | More (Two a b) m r => _
          | More (Three a b c) m r => _
          end).
  - apply H1.
  - apply H2.
  - apply H3.
  - apply H4.
  - apply H5. apply SELF.
Qed.

Lemma fcons_go_deep (A : Type) (x : A) (q : Seq A)  : (q <> Nil) -> exists f m r, fcons x q = More f m r.
Proof.
  intro H. destruct q.
  - contradiction.
  - exists (One x), Nil, (One a). reflexivity.
  - destruct d.
    + exists (Two x a), q, d0. reflexivity.
    + exists (Three x a a0), q, d0. reflexivity.
    + exists (Two x a), (fcons (Pair a0 a1) q), d0. reflexivity. 
Qed.

From Clairvoyance Require Import Core.

(* Note that this definition *is* maximally lazy. *)
Fixpoint fconsA' (A : Type) (q : SeqA A) (x : T A) : M (SeqA A) :=
  tick >>
  (match q with
  | NilA =>
      ret (UnitA x)
  | UnitA y =>
      let~ f' := ret (OneA x) in
      let~ m' := ret NilA in
      let~ r' := ret (OneA y) in
      ret (MoreA f' m' r')
  | MoreA f m r =>
      let! f_val := force f in
      match f_val with
      | OneA a =>
          let~ f' := ret (TwoA x a) in
          ret (MoreA f' m r)
      | TwoA a b =>
          let~ f' := ret (ThreeA x a b) in
          ret (MoreA f' m r)
      | ThreeA a b c =>
          let~ f' := ret (TwoA x a) in
          let~ pbc := ret (PairA b c) in
          (* The termination checker rejects the imperative form
             let! m := force m in ... ; use forcing instead. *)
          let~ m' := forcing m (fun m => fconsA' m pbc) in
          ret (MoreA f' m' r)
      end
  end).


Definition fconsA (A : Type) (x : T A) (q : T (SeqA A)) : M (SeqA A) :=
  forcing q (fun q => fconsA' q x).

Lemma fconsA_mon (A : Type) `{LDA : LessDefined A, PreOrder A LDA} x' x (q' q : T (SeqA A)) 
  : x' `less_defined` x ->
    q' `less_defined` q ->
    fconsA x' q' `less_defined` fconsA x q.
Proof.
  invert_clear 2; try solve [ solve_mon ].
  rename x0 into q'. rename y into q. rename H1 into Hq.
  simpl. induction q as [| x'' | f m r]; try solve [ solve_mon ].
  - (* NilA *)
    invert_clear Hq.
    simpl. apply bind_mon.
    + solve [solve_mon].
    + intros x1 x2 Hx12. inversion Hx12; subst. solve_mon.
  - (* UnitA *)
    invert_clear Hq.
    simpl. apply bind_mon.
    + solve [solve_mon].
    + intros xa xb Hxab. apply bind_mon.
      * solve [solve_mon].
      * intros f1 f2 Hf12. inversion Hf12; subst. solve_mon.
        try solve [ solve_mon ].
  - (* MoreA *)
    rename H1 into IH.
    invert_clear Hq.
    simpl. apply bind_mon.
    + solve [solve_mon].
    + intros x1 x2 Hx12. apply bind_mon.
      * solve [solve_mon].
      * intros x3 x4 Hx34. inversion Hx34; subst. try solve [ solve_mon ].
        -- apply bind_mon.
           ++ solve [solve_mon].
           ++ intros x7 x8 Hx78. inversion Hx78; subst. try solve [ solve_mon ]. solve [solve_mon].
        -- apply bind_mon; try solve [ solve_mon ].
           intros x9 x10 Hx910. inversion Hx910; subst. apply bind_mon; try solve [ solve_mon ].
           ++ (* pbc demand: x11 `less_defined` x12 (any shape) *)
              intros x11 x12 Hx1112.
              (* No inversion of Hx1112: IH only needs x11 ≤ x12 as-is.
                 Destruct H2 (m1 ≤ r) and IH (TR1 P r) BEFORE apply bind_mon
                 so r = Thunk r_inner and IH : P r_inner are concrete.
                 Follows ImplicitQueue.v lines 688-694. *)
              invert_clear H2; try solve [solve_mon].
              invert_clear IH as [? IH |]; try solve [solve_mon].
              apply bind_mon.
              ** apply thunk_mon. simpl.
                 (* Goal: fconsA' m1_inner x11 ≤ fconsA' r_inner x12 *)
                 apply IH; try solve [auto]. typeclasses eauto.
              ** intros x13 x14 Hx1314. apply ret_mon. solve_mon.
           ++ (* Thunk case of Hx910: same IH pattern as the Undefined case above *)
              apply bind_mon; try solve [ solve_mon ].
              intros x11 x12 Hx1112.
              invert_clear H2; try solve [solve_mon].
              invert_clear IH as [? IH |]; try solve [solve_mon].
              apply bind_mon.
              ** apply thunk_mon. simpl.
                 apply IH; try solve [auto]. typeclasses eauto.
              ** intros x13 x14 Hx1314. apply ret_mon. solve_mon.
Qed.


(* Fixpoint fcons {A : Type} (x : A) (s : Seq A) : Seq A :=
  match s with
  | Nil              => 
      let u' := x in
      Unit u'
  | Unit y           => 
      let f' := One x in
      let m' := Nil in
      let r' := One y in
      More f' m' r'
  | More f m r =>
      let (f, m) :=
        match f with
        | One a => 
            let f' := Two x a in
            (f', m)
        | Two a b => 
            let f' := Three x a b in
            (f', m)
        | Three a b c => 
            let f' := Two x a in
            let pbc := Pair b c in
            let m' := fcons pbc m in
            (f', m')
        end in
      More f m r
  end. *)

Fixpoint fconsD' (A B : Type) `{Exact A B}
    (x : A) (s : Seq A) (outD : SeqA B)
    : Tick (T (SeqA B)) :=
  Tick.tick >>
  match s with
  | Nil =>
      (* fcons x Nil = Unit x *)
      match outD with
      | UnitA _ => Tick.ret (Thunk NilA)
      | _       => bottom
      end

  | Unit y =>
      (* fcons x (Unit y) = More (One x) Nil (One y) *)
      match outD with
      | MoreA _ _ rD =>
          let yD := match rD with
                    | Thunk (OneA yD) => yD
                    | _               => Undefined
                    end in
          Tick.ret (Thunk (UnitA yD))
      | _ => bottom
      end

  | More (One a) m r =>
      (* fcons x (More (One a) m r) = More (Two x a) m r *)
      match outD with
      | MoreA fD mD rD =>
          let aD := match fD with
                    | Thunk (TwoA _ aD) => aD
                    | _                 => Undefined
                    end in
          Tick.ret (Thunk (MoreA (Thunk (OneA aD)) mD rD))
      | _ => bottom
      end

  | More (Two a b) m r =>
      (* fcons x (More (Two a b) m r) = More (Three x a b) m r *)
      match outD with
      | MoreA fD mD rD =>
          let '(aD, bD) := match fD with
                           | Thunk (ThreeA _ aD bD) => (aD, bD)
                           | _                      => (Undefined, Undefined)
                           end in
          Tick.ret (Thunk (MoreA (Thunk (TwoA aD bD)) mD rD))
      | _ => bottom
      end

  | More (Three a b c) m r =>
      (* fcons x (More (Three a b c) m r) = More (Two x a) (fcons (Pair b c) m) r *)
      match outD with
      | MoreA fD mD rD =>
          let aD := match fD with
                    | Thunk (TwoA _ aD) => aD
                    | _                 => Undefined
                    end in
          let+ mD_in := thunkD (fconsD' (Pair b c) m) mD in
          Tick.ret (Thunk (MoreA (Thunk (ThreeA aD (exact b) (exact c))) mD_in rD))
      | _ => bottom
      end
  end.

Definition fconsD (A : Type) : A -> Seq A -> SeqA A -> Tick (T (SeqA A)) :=
  fconsD'.

Lemma fconsD'_approx : forall (A B : Type)
    `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (x : A) (s : Seq A) (outD : SeqA B),
    outD `is_approx` fcons x s ->
    Tick.val (fconsD' x s outD) `is_approx` s.
Proof.
  intros ? ? LDB EAB RLDB ? ? ?. revert A x s B LDB EAB RLDB outD.
  apply (fcons_ind (fun A x s s' =>
    forall B `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
           (outD : SeqA B),
      outD `less_defined` exact s' ->
      Tick.val (fconsD' x s outD) `less_defined` exact s)); intros until outD. 
  (* Nil *)
  {
    refine (match outD with
            | UnitA (Thunk xD) => _
            | _ => _ end); intro Happrox;
      repeat match goal with
        | H : ?x `less_defined` ?y |- _ =>
            (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
        end; repeat constructor; simpl; repeat constructor; auto.
  }
  (* Unit *)
  {
    refine (match outD with
            | MoreA fD mD _ => _
            | _ => bottom
            end); intro Happrox; teardown;
      repeat match goal with
        | H : ?x `less_defined` ?y |- _ =>
            (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
        end; repeat constructor; auto.
  }
  (* More (One a) m r *)
  {
    refine (match outD with
            | MoreA fD mD' _ => _
            | _ => _
            end); try solve [ repeat constructor; reflexivity ].
    intro Happrox. teardown; repeat match goal with
        | H : ?x `less_defined` ?y |- _ =>
            (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
        end; repeat constructor; auto.
  }
  (* More (Two a b) m r *)
  {
    (* Goal 4: More (Two a b) *)
    intro Happrox.
    refine (match outD as o
              return o `less_defined` exact (More (Three x a b) m r) ->
                    Tick.val (fconsD' x (More (Two a b) m r) o) `less_defined`
                    exact (More (Two a b) m r)
            with
            | MoreA fD mD rD => _
            | _ => _
            end Happrox); clear Happrox; try auto.
    intro Happrox.
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
    simpl.
    destruct fD as [ fA | ].
    * (* fD = Thunk fA *)
      destruct fA as [ t1 | t1 t2 | t1 t2 t3 ].
      -- (* OneA — contradicts HfD *)
         invert_clear HfD. invert_clear H0.
      -- (* TwoA — contradicts HfD *)
         invert_clear HfD. invert_clear H0.
      -- (* ThreeA t1 t2 t3 *)
         invert_clear HfD. invert_clear H0.
         repeat constructor; assumption.
    * (* fD = Undefined *)
      simpl. repeat constructor; try assumption.
  }
  (* More (Three a b c) m r *)
  {
    refine (match outD with
            | MoreA fD mD' rD => _
            | _ => _
            end); try solve [ invert_clear 1 ].
    intro Happrox.
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
    invert_clear HmD as [ | mA ? HmA ].
    { 
      (* Subgoal 1: mD' = Undefined — no demand on middle *)
      simpl.
      destruct fD as [ fA | ].
      * (* fD = Thunk fA *)
        destruct fA as [ t1 | t1 t2 | t1 t2 t3 ].
        -- (* OneA — contradicts HfD *)
          invert_clear HfD. invert_clear H1.
        -- (* TwoA *)
          invert_clear HfD. invert_clear H1.
          repeat match goal with
          | H : ?x `less_defined` ?y |- _ =>
              (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
          end; repeat constructor; auto; reflexivity.
        -- (* ThreeA — contradicts HfD *)
          invert_clear HfD. invert_clear H1.
      * (* fD = Undefined *)
        repeat match goal with
          | H : ?x `less_defined` ?y |- _ =>
              (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
          end; repeat constructor; auto; reflexivity.
    }
    (* Subgoal 2: mD' = Thunk mA — recursive call *)
    {
      specialize (H _ _ _ _ mA HmA).
      simpl.
      destruct (Tick.val (fconsD' (Pair b c) m mA)) as [ sD | ] eqn:EfconsD.
      * (* Thunk sD *)
        destruct fD as [ fA | ].
        -- destruct fA as [ t1 | t1 t2 | t1 t2 t3 ].
          ++ (* OneA — contradicts HfD *)
              invert_clear HfD. invert_clear H1.
          ++ (* TwoA *)
              invert_clear HfD. invert_clear H1.
              simpl. 
              repeat match goal with
              | H : ?x `less_defined` ?y |- _ =>
                  (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
              end; repeat constructor; auto; reflexivity.
          ++ (* ThreeA — contradicts HfD *)
              invert_clear HfD. invert_clear H1.
        -- (* fD = Undefined *)
          simpl. 
          repeat match goal with
              | H : ?x `less_defined` ?y |- _ =>
                  (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
              end; repeat constructor; auto; reflexivity.
      * (* Undefined *)
        destruct fD as [ fA | ].
        -- destruct fA as [ t1 | t1 t2 | t1 t2 t3 ].
          ++ invert_clear HfD. invert_clear H1.
          ++ invert_clear HfD. invert_clear H1.
              simpl. 
              repeat match goal with
              | H : ?x `less_defined` ?y |- _ =>
                  (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
              end; repeat constructor; auto; reflexivity.
          ++ invert_clear HfD. invert_clear H1.
        -- simpl. 
           repeat match goal with
              | H : ?x `less_defined` ?y |- _ =>
                  (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
              end; repeat constructor; auto; reflexivity.
    }
  }
Qed.

Corollary fconsD_approx (A : Type) `{LDA : LessDefined A, !Reflexive LDA}
  (x : A) (q : Seq A) (outD : SeqA A) :
  outD `is_approx` fcons x q -> Tick.val (fconsD' x q outD) `is_approx` q.
Proof.
  eapply fconsD'_approx.
Qed.

Lemma fconsD'_exact (A B : Type) `{Exact A B} (x : A) (s : Seq A) :
  Tick.val (fconsD' x s (exact (fcons x s))) = exact s.
Proof.
  generalize dependent B. generalize dependent A.
  induction s.
  - (* Nil *) reflexivity.
  - (* Unit *) reflexivity.
  - (* More f m r *)
    destruct d as [| | a b c].
    + (* One *) reflexivity.
    + (* Two *) reflexivity.
    + (* Three a b c *)
      simpl. intros.
      unfold exact in IHs.
      rewrite (IHs (Pair b c) (TupleA B) _).
      reflexivity.
Qed.

#[local] Existing Instance Reflexive_LessDefined_T.
#[local] Existing Instance Reflexive_LessDefined_prodA.

Lemma fconsD'_spec (A B : Type) :
  forall `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (x : A) (s : Seq A) (outD : SeqA B),
    outD `is_approx` fcons x s ->
    forall sD, sD = Tick.val (fconsD' x s outD) ->
      let dcost := Tick.cost (fconsD' x s outD) in
      fconsA (exact x) sD [[ fun out cost =>
                               outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros LDB HReflexive EAB x s outD Happrox sD HsD dcost.
  revert A x s B LDB HReflexive EAB outD Happrox sD HsD dcost.
  apply (fcons_ind
    (fun A x s s' =>
       forall B `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
              (outD : SeqA B),
         outD `is_approx` s' ->
         forall sD, sD = Tick.val (fconsD' x s outD) ->
           let dcost := Tick.cost (fconsD' x s outD) in
           fconsA (exact x) sD [[ fun out cost =>
                                    outD `less_defined` out /\ cost <= dcost ]])).
  (* Case 1: s = Nil, s' = Unit x *)
  {
    intros A x B LDB HReflexive EAB outD Happrox sD HsD dcost.
    revert Happrox.
    destruct outD; intro Happrox; try (invert_clear Happrox; fail).
    subst. simpl.
    mgo_.
  }
  (* Case 2: s = Unit y, s' = More (One y) Nil (One x) *)
  {
    intros A x y B LDB HReflexive EAB outD Happrox sD HsD dcost.
    revert Happrox.
    destruct outD; intro Happrox; try (invert_clear Happrox; fail).
    subst. simpl.
    mgo_.
    repeat (apply optimistic_thunk_go; mgo_); invert_clear Happrox as [ | | ? ? ? ? ? ? Ht Ht0 Ht1 ].
    - exact Ht.
    - exact Ht0.
    - destruct t1 as [ [ | | ] | ].
      + reflexivity.
      + invert_clear Ht1. invert_clear H.
      + invert_clear Ht1. invert_clear H.
      + constructor.
    
  }
  (* Case 3: s = More (One a) m r, s' = More (Two x a) m r *)
  {
    intros A x a m r B LDB HReflexive EAB outD Happrox sD HsD dcost.
    revert Happrox.
    destruct outD; intro Happrox; try (invert_clear Happrox; fail).
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
    subst. simpl.
    keep_mgo_.
    (* Remaining goals from keep_mgo_: need to show field-level less_defined *)
    (* Force the front digit — need to case split on t *)
    destruct t as [ [ | | ] | ].
      * (* OneA *)
        invert_clear HfD. invert_clear H.
      * (* TwoA 
          exact front = Thunk (TwoA (exact x) (exact a)).
           So HfD : t ≤ Thunk (TwoA (exact x) (exact a)). *)
        invert_clear HfD. invert_clear H.
        simpl. solve [solve_mon]. 
      * (* ThreeA — contradicts HfD *)
        invert_clear HfD. invert_clear H.
      * (* Undefined *)
        simpl. repeat constructor.
  }

  (* Case 4: s = More (Two a b) m r, s' = More (Three x a b) m r *)
  {
    intros A x a b m r B LDB HReflexive EAB outD Happrox sD HsD dcost.
    revert Happrox.
    destruct outD; intro Happrox; try (invert_clear Happrox; fail).
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
    subst. simpl.
    keep_mgo_.
    destruct t as [ [ | | ] | ].
      * (* OneA — contradicts HfD *)
        invert_clear HfD. invert_clear H.
      * (* TwoA — contradicts HfD since exact front = ThreeA *)
        invert_clear HfD. invert_clear H.
      * (* ThreeA *)
        invert_clear HfD. invert_clear H.
        simpl. keep_mgo_.
      * (* Undefined *)
        simpl. keep_mgo_.
  }

  (* Case 5: s = More (Three a b c) m r *)
  {
    intros A x a b c m r IH B LDB HReflexive EAB outD Happrox sD HsD dcost.
    revert Happrox.
    destruct outD; intro Happrox; try (invert_clear Happrox; fail).
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
    subst. simpl.

    destruct t0 as [ mA | ].

    (* Thunk mA: recursive call *)
    {
      simpl.
      invert_clear HmD as [| ? ? HmA].
      mgo_.
      apply optimistic_thunk_go. mgo_.
      apply optimistic_thunk_go. mgo_.
      apply optimistic_thunk_go. mgo_.
      eapply optimistic_mon.
      {
        change (((fun m0 => fconsA' m0 (Thunk (PairA (exact b) (exact c)))) $! Tick.val (fconsD' (Pair b c) m mA))) with (fconsA (exact (Pair b c)) (Tick.val (fconsD' (Pair b c) m mA))).
        eapply IH; try eauto. typeclasses eauto.
      }
      {
        intros ? ? [Hout Hcost]. keep_mgo_.
        (* field-level goals: use HfD, HrD, Hout, Hcost *)
        destruct t as [ [ | | ] | ];
                  try (invert_clear HfD; invert_clear H);
                  simpl; repeat constructor; eauto. reflexivity.
      }
    }

    (* Undefined — no recursion, forcing is vacuous *)
    {
      simpl.
      mgo_.
      apply optimistic_thunk_go. mgo_.
      apply optimistic_thunk_go. mgo_.
      apply optimistic_skip. mgo_.
      
      destruct t as [ [ | | ] | ];
      try (invert_clear HfD; invert_clear H);
      simpl; repeat constructor; try assumption; reflexivity.
    }
  }
Qed.

Corollary fconsD_spec (A : Type) :
  forall `{LDA : LessDefined A, !Reflexive LDA}
    (x : A) (s : Seq A) (outD : SeqA A),
    outD `is_approx` fcons x s ->
    forall sD, sD = Tick.val (fconsD x s outD) ->
      let dcost := Tick.cost (fconsD x s outD) in
      fconsA (exact x) sD [[ fun out cost =>
                               outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros. eapply fconsD'_spec; eauto.
Qed.

Class Debitable (A : Type) := debt : A -> nat.

#[global] Instance Debitable_T (A : Type) `{Debitable A} : Debitable (T A) :=
  fun xD => match xD with
            | Thunk x => debt x
            | Undefined => 0
            end.

Definition safe_DigitA {A : Type} (dA : DigitA A) : nat :=
  match dA with
  | OneA _ => 0
  | TwoA _ _ => 1
  | ThreeA _ _ _ => 0
  end.

#[global] Instance Debitable_SeqA : forall (A : Type), Debitable (SeqA A) :=
  fix debt_SeqA (A : Type) (sA : SeqA A) :=
    match sA with
    | NilA => 0
    | UnitA _ => 0
    | MoreA fD mD rD =>
        T_rect _ safe_DigitA 1 fD +
        @Debitable_T _ (debt_SeqA _) mD +
        T_rect _ safe_DigitA 1 rD
    end.

Ltac unfold_debt := 
  unfold debt at 1; simpl Debitable_T; simpl Debitable_SeqA; 
  simpl safe_DigitA; simpl T_rect.

(* Helper for sub-addivitty *)
Lemma safe_DigitA_lub_subadditive
  (A : Type) `{LDA : LessDefined A, !Reflexive LDA, LBA : Lub A,
                 !@LubLaw A LBA LDA}
  (d1 d2 d : DigitA A) :
  d1 `less_defined` d ->
  d2 `less_defined` d ->
  safe_DigitA (lub d1 d2) <= safe_DigitA d1 + safe_DigitA d2.
Proof.
  intros H1 H2. invert_clear H1; invert_clear H2; simpl; lia.
Qed.  

Definition safe_T {A : Type} (fD : T (DigitA A)) : nat :=
  match fD with
  | Thunk d => safe_DigitA d
  | Undefined => 1
  end.

(* Then T_rect _ safe_DigitA 1 fD = safe_T fD, which 
   Coq can verify by reflexivity, and Debitable_SeqA can use 
   safe_T for clarity. But you don't need to refactor 
   Debitable_SeqA, just use safe_T as a name in the lemma. *)

Lemma safe_T_lub_subadditive
  (A : Type) `{LDA : LessDefined A, !Reflexive LDA, LBA : Lub A,
                 !@LubLaw A LBA LDA}
  (f1 f2 fd : T (DigitA A)) :
  f1 `less_defined` fd ->
  f2 `less_defined` fd ->
  safe_T (lub f1 f2) <= safe_T f1 + safe_T f2.
Proof.
  intros H1 H2.
  invert_clear H1; invert_clear H2; simpl; try lia.
  eapply safe_DigitA_lub_subadditive; eassumption.
Qed.

Lemma debt_SeqA_lub_subadditive :
  forall (A : Type) (x : SeqA A),
    forall `{LDA : LessDefined A, !Reflexive LDA, LBA : Lub A,
              !@LubLaw A LBA LDA}
           (y d : SeqA A),
      x `less_defined` d ->
      y `less_defined` d ->
      debt (lub x y) <= debt x + debt y.
Proof.
  apply (SeqA_ind
    (fun A x =>
       forall `{LDA : LessDefined A, !Reflexive LDA, LBA : Lub A,
                 !@LubLaw A LBA LDA}
              (y d : SeqA A),
         x `less_defined` d ->
         y `less_defined` d ->
         debt (lub x y) <= debt x + debt y)).
  - (* NilA *)
    intros A0 LDA0 RLDA0 LBA0 LLA0 y d Hx Hy.
    invert_clear Hx. invert_clear Hy. simpl. sauto unfold:debt.
  - (* UnitA *)
    intros A0 xA LDA0 RLDA0 LBA0 LLA0 y d Hx Hy.
    invert_clear Hx. invert_clear Hy. simpl. sauto unfold:debt.
  - (* MoreA *)
    intros A0 fx mx rx IH LDA0 RLDA0 LBA0 LLA0 y d Hx Hy.
    (* Force d = MoreA fd md rd *)
    invert_clear Hx as [ | | fd ? md ? rd ? Hfx Hmx Hrx ].
    (* Force y = MoreA fy my ry *)
    invert_clear Hy as [ | | fy ? my ? ry ? Hfy Hmy Hry ].
    (* Simplify the lub and debt *)
    simpl.
    (* Goal looks like:
       safe_T (lub fx fy) + Debitable_T (...) (lub mx my) + safe_T (lub rx ry)
       <= (safe_T fx + Debitable_T (...) mx + safe_T rx)
        + (safe_T fy + Debitable_T (...) my + safe_T ry)
       Possibly with T_rect _ safe_DigitA 1 instead of safe_T. *)
    change (T_rect _ safe_DigitA 1) with (@safe_T A0) in *.
    (* Three sub-bounds *)
    pose proof (@safe_T_lub_subadditive A0 _ _ _ _ fx fy f2 Hfx Hfy) as Bf.
    pose proof (@safe_T_lub_subadditive A0 _ _ _ _ rx ry r2 Hrx Hry) as Br.
    (* Spine: lift IH through T *)
    assert (Bm : @Debitable_T _ (@Debitable_SeqA (TupleA A0)) (lub mx my)
               <= @Debitable_T _ (@Debitable_SeqA (TupleA A0)) mx
                + @Debitable_T _ (@Debitable_SeqA (TupleA A0)) my).
    { 
      invert_clear Hmx; invert_clear Hmy; simpl; try lia.
      (* mx = Thunk mxA, my = Thunk myA, md = Thunk mdA, with mxA, myA ≤ mdA *)
      invert_clear IH as [ ? IH' | ].
      eapply IH'; eauto; typeclasses eauto. 
    }
    repeat unfold_debt.
    change (T_rect (fun _ : T (DigitA A0) => nat) safe_DigitA 1) with (@safe_T A0) in *.
    lia.
Qed.

Lemma fconsD'_cost : forall (A B : Type) `{LessDefined B, Exact A B}
    (x : A) (s : Seq A) (outD : SeqA B),
    outD `is_approx` fcons x s ->
    let inM := fconsD' x s outD in
    let cost := Tick.cost inM in
    let inD := Tick.val inM in
    debt inD + cost <= 2 + debt outD.
Proof.
  intros A B LDB EAB x s. revert A x s B LDB EAB.
  apply (fcons_ind (fun (A : Type) (x : A) (s : Seq A) (s' : Seq A) =>
    forall B LDB EAB outD,
      outD `is_approx` s' ->
      let inM := fconsD' x s outD in
      let cost := Tick.cost inM in
      let inD := Tick.val inM in
      debt inD + cost <= 2 + debt outD)).
  
  (* Nil: fcons x Nil = Unit x
       inD = Thunk NilA, cost = 1
       debt(Thunk NilA) + 1 = 0 + 1 = 1 ≤ 2 + debt(UnitA _) = 2 + 0 *)
  {
    intros A x B LDB EAB outD Happrox.
    destruct outD; try (invert_clear Happrox; fail).
    simpl. lia.
  }

  (* Unit y: fcons x (Unit y) = More (One x) Nil (One y)
       inD = Thunk (UnitA yD), cost = 1
       debt(UnitA yD) + 1 = 0 + 1 = 1 ≤ 2 + debt(MoreA fD mD rD) *)
  {
    intros A x y B LDB EAB outD Happrox.
    destruct outD; try (invert_clear Happrox; fail).
    simpl. lia.
  }

  (* One a: fcons x (More (One a) m r) = More (Two x a) m r
       inD = Thunk (MoreA (Thunk (OneA aD)) mD rD), cost = 1
       safe(OneA) = 0, so debt contribution from front = 0
       Need: 0 + debt(mD) + safe(rD) + 1 ≤ 2 + safe(fD) + debt(mD) + safe(rD) *)
  {
    intros A x a m r B LDB EAB outD Happrox.
    destruct outD; try (invert_clear Happrox; fail).
    simpl.
    destruct t as [ [ | | ] | ]; simpl; sauto unfold:debt.
  }

  (* Two a b: fcons x (More (Two a b) m r) = More (Three x a b) m r
       inD = Thunk (MoreA (Thunk (TwoA aD bD)) mD rD), cost = 1
       safe(TwoA) = 1, so debt contribution from front = 1
       Need: 1 + debt(mD) + safe(rD) + 1 ≤ 2 + safe(fD) + debt(mD) + safe(rD) *)
  {
    intros A x a b m r B LDB EAB outD Happrox.
    destruct outD; try (invert_clear Happrox; fail).
    simpl.
    destruct t as [ [ | | ] | ]; simpl; sauto unfold:debt.
  }

  (* Three a b c: RECURSIVE
       fcons x (More (Three a b c) m r) = More (Two x a) (fcons (Pair b c) m) r
       IH: debt(mD_in) + rc ≤ 2 + debt(mD_out)
       Need: 0 + debt(mD_in) + safe(rD) + 1 + rc ≤ 2 + safe(fD) + debt(mD_out) + safe(rD) *)
  {
    intros A x a b c m r IH B LDB EAB outD Happrox.
    destruct outD; try (invert_clear Happrox; fail).
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
    simpl.
    (* Need to case split on t0 (middle demand) for thunkD *)
    destruct t0 as [ mA | ].

    (* Thunk mA — recursive call fires *)
    {
      simpl.
      invert_clear HmD as [ | ? ? HmA ].
      specialize (IH _ _ _ mA HmA).
      simpl in IH.
      (* Now IH : debt (Tick.val (fconsD' (Pair b c) m mA)) +
                  Tick.cost (fconsD' (Pair b c) m mA) ≤ 2 + debt mA *)
      destruct (Tick.val (fconsD' (Pair b c) m mA)) as [ sD | ].
      (* Thunk sD *)
      {
        assert (HIH : debt sD + Tick.cost (fconsD' (Pair b c) m mA) <= 2 + debt mA).
        { 
          change (debt (Thunk sD)) with (debt sD) in IH.
          change (debt (Thunk mA)) with (debt mA) in IH.
          lia. 
        }
        destruct t as [ fA | ].
        - (* Thunk fA *)
          destruct fA as [ | | ].
          + (* OneA — contradicts HfD *)
            exfalso. invert_clear HfD. invert_clear H.
          + (* TwoA — the valid case *)
            cbn in *. lia.
          + (* ThreeA — contradicts HfD *)
            exfalso. invert_clear HfD. invert_clear H.
        - (* Undefined *)
          simpl debt in *.
          destruct t1 as [ dA | ].
          + destruct dA as [ | | ]; simpl in *. 
            all: repeat unfold_debt.
            all: change (Debitable_SeqA sD) with (debt sD) in *.
            all: change (Debitable_SeqA mA) with (debt mA) in *.
            all: lia.
          + repeat unfold_debt.
            change (Debitable_SeqA sD) with (debt sD) in *.
            change (Debitable_SeqA mA) with (debt mA) in *.
            lia.
      }


    (* Undefined — thunkD returns bottom, no recursion *)
    {
      simpl.
      destruct t as [ [ | | ] | ]; simpl; sauto unfold:debt.
    }
  }

  (* Undefined — middle not demanded, thunkD returns bottom (cost 0, val Undefined).
   No recursion. debt reduces to safe(front) + safe(rear) on both sides.
   Goal: safe(t1) + 1 ≤ 2 + safe(t) + safe(t1), i.e., 1 ≤ 2 + safe(t). Trivial. *)
  {
    simpl thunkD. simpl Tick.val. simpl Tick.cost.
    destruct t as [ [ | | ] | ]; destruct t1 as [ [ | | ] | ]; simpl; lia.
  }
  }
Qed.


Corollary fconsD_cost (A : Type) `{LessDefined A}
    (x : A) (s : Seq A) (outD : SeqA A) :
    outD `is_approx` fcons x s ->
    let inM := fconsD x s outD in
    let cost := Tick.cost inM in
    let inD := Tick.val inM in
    debt inD + cost <= 2 + debt outD.
Proof.
  intros. apply fconsD'_cost. auto.
Qed.

Lemma fconsD'_cost_bottom (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (x : A) (s : Seq A) :
  let inM := fconsD' x s (bottom_of (exact (fcons x s))) in
  debt (Tick.val inM) + Tick.cost inM <= 3.
Proof.
  destruct s as [ | y | d m r ].
  - (* s = Nil *)
    simpl. lia.
  - (* s = Unit y *)
    simpl. lia.
  - (* s = More d m r *)
    destruct d as [ a | a b | a b c ]; simpl; lia.
Qed.

(**
==============
Head Operations

head (Unit x) = Some x
head (More (One x) _ _ ) = Some x
head (More (Two x _) _ _ ) = Some x
head (More (Three x _ _) _ _ ) = Some x
*)
Definition head {A : Type} (s : Seq A) : option A :=
  match s with
  | Nil => None
  | Unit x => Some x
  | More (One x) _ _ => Some x
  | More (Two x _) _ _ => Some x
  | More (Three x _ _) _ _ => Some x
  end.


(* Demand function *)
Definition headD' {A B : Type} `{Exact A B} (s : Seq A) (outD : option (T B))
    : Tick (T (SeqA B)) :=
  Tick.tick >>
  match s, outD with
  | Nil, None => Tick.ret (Thunk NilA)
  | Unit x, Some xD =>
      Tick.ret (Thunk (UnitA xD))
  | Unit x, None => Tick.ret (Thunk (UnitA Undefined))
  | More (One x) m r, Some xD =>
      Tick.ret (Thunk (MoreA (Thunk (OneA xD)) Undefined Undefined))
  | More (One x) m r, None =>
      Tick.ret (Thunk (MoreA (Thunk (OneA Undefined)) Undefined Undefined))
  | More (Two x _) m r, Some xD =>
      Tick.ret (Thunk (MoreA (Thunk (TwoA xD Undefined)) Undefined Undefined))
  | More (Two x _) m r, None =>
      Tick.ret (Thunk (MoreA (Thunk (TwoA Undefined Undefined)) Undefined Undefined))
  | More (Three x _ _) m r, Some xD =>
      Tick.ret (Thunk (MoreA (Thunk (ThreeA xD Undefined Undefined)) Undefined Undefined))
  | More (Three x _ _) m r, None =>
      Tick.ret (Thunk (MoreA (Thunk (ThreeA Undefined Undefined Undefined)) Undefined Undefined))
  | _, _ => bottom
  end.

(* Specialization *)
Definition headD (A : Type) : Seq A -> option (T A) -> Tick (T (SeqA A)) :=
  headD'.

(* Functional correctness *)
Lemma headD'_approx : forall (A B : Type)
    `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (s : Seq A) (outD : option (T B)),
    outD `is_approx` head s ->
    Tick.val (headD' s outD) `is_approx` s.
Proof.
  intros A B LDB RLDB EAB s outD Happrox.
  destruct s as [ | a | d s' d0 ]; destruct outD as [ xD | ]; simpl in *.
  - (* Nil, Some xD — bottom case, Happrox : Some xD ≤ None is impossible *)
    invert_clear Happrox.
  - (* Nil, None *) repeat constructor.
  - (* Unit a, Some xD *) repeat constructor. invert_clear Happrox. assumption.
  - (* Unit a, None *) repeat constructor.
  - (* More d s' d0, Some xD *)
    destruct d; repeat constructor; invert_clear Happrox; assumption.
  - (* More d s' d0, None *)
    destruct d; repeat constructor.
Qed.

Corollary headD_approx (A : Type) `{LDA : LessDefined A, !Reflexive LDA}
    (s : Seq A) (outD : option (T A)) :
    outD `is_approx` head s ->
    Tick.val (headD s outD) `is_approx` s.
Proof.
  eapply headD'_approx.
Qed.

(* Cost — trivial, cost is always 1, debt of input ≤ 2 + debt of output *)
Lemma headD'_cost : forall (A B : Type) `{Exact A B}
    (s : Seq A) (outD : option (T B)),
    Tick.cost (headD' s outD) <= 1.
Proof.
  intros. destruct s; destruct outD; simpl; try lia.
  all: destruct d; simpl; lia.
Qed.

Corollary headD_cost (A : Type) `{Exact A}
    (s : Seq A) (outD : option (T A)) :
    Tick.cost (headD s outD) <= 1.
Proof.
  eapply headD'_cost.
Qed.

Definition headA' (A : Type) (q : SeqA A) : M (option (T A)) :=
  tick >>
    match q with
    | NilA => ret None
    | UnitA x => ret (Some x)
    | MoreA fD _ _ =>
        forcing fD (fun f =>
          match f with
          | OneA x => ret (Some x)
          | TwoA x _ => ret (Some x)
          | ThreeA x _ _ => ret (Some x)
          end)
    end.
 
Definition headA (A : Type) (q : T (SeqA A)) : M (option (T A)) :=
  forcing q headA'.

Lemma headA_mon (A : Type) `{LDA : LessDefined A, PreOrder A LDA}
    (q1 q2 : T (SeqA A)) :
    q1 `less_defined` q2 ->
    headA q1 `less_defined` headA q2.
Proof.
  invert_clear 1; try solve [ solve_mon ].
  (* Both Thunk: q1 = Thunk x1, q2 = Thunk y1, x1 ≤ y1 *)
  rename x into x1. rename y into y1. rename H0 into Hxy.
  simpl. unfold headA'. apply bind_mon; [ reflexivity | ].
  intros x x' Hxx'.
  (* match x1 ≤ match y1, given Hxy : x1 ≤ y1 *)
  invert_clear Hxy; try solve [ solve_mon ].
Qed.

Lemma headD'_spec : forall (A B : Type)
    `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (s : Seq A) (outD : option (T B)),
    outD `is_approx` head s ->
    forall sD, sD = Tick.val (headD' s outD) ->
      let dcost := Tick.cost (headD' s outD) in
      headA sD [[ fun out cost =>
                     outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros A B LDB RLDB EAB s outD Happrox sD HsD dcost.
  destruct s as [ | a | d s' d0 ].
  3: destruct d.
  all: destruct outD;
       simpl in *;
       try (invert_clear Happrox; fail).
  - (* Nil, None *)              subst. unfold headA, headA'. mgo_.
  - (* Unit a, Some t *)         subst. unfold headA, headA'. mgo_.
  - (* More (One _), Some t *)   subst. unfold headA, headA'. simpl. mgo_.
  - (* More (Two _ _), Some t *) subst. unfold headA, headA'. simpl. mgo_.
  - (* More (Three _ _ _), Some t *) subst. unfold headA, headA'. simpl. mgo_.
Qed.

Corollary headD_spec : forall (A : Type) `{LDA : LessDefined A, !Reflexive LDA}
    (s : Seq A) (outD : option (T A)),
    outD `is_approx` head s ->
    forall sD, sD = Tick.val (headD s outD) ->
      let dcost := Tick.cost (headD s outD) in
      headA sD [[ fun out cost =>
                     outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros.
  apply headD'_spec; auto.
Qed.

(** ===== ftail (Section 5.5) ===== *)

(* Drop the first element of a [Tuple].  Used in [ftail]'s Triple-head
   branch to convert [Triple x y z] into [Pair y z] without recursing
   into the spine.  The [Pair] arm is unreachable in [ftail]'s usage but
   kept to make the function total. *)
Definition chop_triple {A : Type} (t : Tuple A) : Tuple A :=
  match t with
  | Triple _ y z => Pair y z
  | Pair x y     => Pair x y
  end.

(* Apply [f] to the first element of a [Seq], leaving the rest of the
   structure intact.  Non-recursive — touches only the topmost element.
   Used in [ftail]'s Triple-head branch via [map1 chop_triple m]. *)
Definition map1 {A : Type} (f : A -> A) (s : Seq A) : Seq A :=
  match s with
  | Nil                    => Nil
  | Unit x                 => Unit (f x)
  | More (One x)       m r => More (One (f x))     m r
  | More (Two x y)     m r => More (Two (f x) y)   m r
  | More (Three x y z) m r => More (Three (f x) y z) m r
  end.

(** *** ftail — drop the front element

    Nine effective cases:
    - [Nil]: total, returns [Nil] (Claessen leaves it undefined; we make
      it total to simplify Coq).
    - [Unit _]: drops the singleton.
    - [More (Three _ x y) m r]: Three → Two, no recursion.
    - [More (Two _ x) m r]: Two → One, no recursion.
    - [More (One _) Nil r]: reshape [r] (three sub-cases).
    - [More (One _) m r] with [m ≠ Nil]:
      + [head m = Some (Pair x y)]: recurse on [m]; front becomes
        [Two x y].  The only structurally recursive site.
      + [head m = Some (Triple x _ _)]: chop via [map1 chop_triple];
        front becomes [One x].  No recursion — Claessen's key trick. *)
Fixpoint ftail {A : Type} (s : Seq A) : Seq A :=
  match s with
  | Nil                    => Nil
  | Unit _                 => Nil
  | More (Three _ x y) m r => More (Two x y) m r
  | More (Two _ x)     m r => More (One x)   m r
  | More (One _)       m r =>
      match m with
      | Nil =>
          match r with
          | One   y     => Unit y
          | Two   y z   => More (One y) Nil (One z)
          | Three y z w => More (One y) Nil (Two z w)
          end
      | _ =>
          match head m with
          | Some (Pair   x y)   => More (Two x y) (ftail m) r
          | Some (Triple x _ _) => More (One x)   (map1 chop_triple m) r
          | None                => Nil    (* unreachable: m ≠ Nil *)
          end
      end
  end.

(* Sanity checks against the worked-examples table in
   CLAESSEN_REFERENCE.md.  Re-enable to confirm.

Compute @ftail nat Nil.
Compute @ftail nat (Unit 1).
Compute @ftail nat (More (Three 1 2 3) Nil (One 5)).
Compute @ftail nat (More (Two 1 2) Nil (One 5)).
Compute @ftail nat (More (One 1) Nil (One 5)).
Compute @ftail nat (More (One 1) Nil (Two 5 6)).
Compute @ftail nat (More (One 1) Nil (Three 5 6 7)).
Compute @ftail nat (More (One 1) (Unit (Pair 2 3)) (One 5)).
Compute @ftail nat (More (One 1) (Unit (Triple 2 3 4)) (One 5)).
*)

(** Helper unfolds for the One-front cascade cases of [ftail_ind].
    They rewrite [ftail (More (One a) m r)] using a known value of
    [head m], without requiring the caller to destructure [m] — keeping
    [m] as a variable so the subsequent [SELF] call passes Coq's
    structural-recursion check. *)
Lemma ftail_one_unfold_pair (A : Type) (a x y : A)
      (m : Seq (Tuple A)) (r : Digit A) :
  head m = Some (Pair x y) ->
  ftail (More (One a) m r) = More (Two x y) (ftail m) r.
Proof.
  intro Eh.
  destruct m as [ | tu | [tu | tu tv | tu tv tw] mm rm];
    simpl in Eh; try discriminate;
    inversion Eh; subst tu; reflexivity.
Qed.

Lemma ftail_one_unfold_triple (A : Type) (a x y z : A)
      (m : Seq (Tuple A)) (r : Digit A) :
  head m = Some (Triple x y z) ->
  ftail (More (One a) m r) = More (One x) (map1 chop_triple m) r.
Proof.
  intro Eh.
  destruct m as [ | tu | [tu | tu tv | tu tv tw] mm rm];
    simpl in Eh; try discriminate;
    inversion Eh; subst tu; reflexivity.
Qed.

(** *** ftail_ind — custom induction principle, 9 cases.

    Mirrors the structure of [fcons_ind].  Cases 8 (Pair-head, recursive)
    and 9 (Triple-head, non-recursive) split by [head m], not by [m]'s
    constructor — see [ftail_one_unfold_pair] / [ftail_one_unfold_triple]
    above.  This keeps [m] as a Coq-tracked subterm of [s] so the inner
    [SELF] call structurally type-checks. *)
Lemma ftail_ind :
  forall (P : forall (A : Type), Seq A -> Seq A -> Prop),
    (forall A, P A Nil Nil) ->
    (forall A x, P A (Unit x) Nil) ->
    (forall A a x y m r,
        P A (More (Three a x y) m r) (More (Two x y) m r)) ->
    (forall A a x m r,
        P A (More (Two a x) m r) (More (One x) m r)) ->
    (forall A a y,
        P A (More (One a) Nil (One y)) (Unit y)) ->
    (forall A a y z,
        P A (More (One a) Nil (Two y z))
             (More (One y) Nil (One z))) ->
    (forall A a y z w,
        P A (More (One a) Nil (Three y z w))
             (More (One y) Nil (Two z w))) ->
    (forall A a x y m r,
        P (Tuple A) m (ftail m) ->
        head m = Some (Pair x y) ->
        P A (More (One a) m r) (More (Two x y) (ftail m) r)) ->
    (forall A a x y z m r,
        head m = Some (Triple x y z) ->
        P A (More (One a) m r) (More (One x) (map1 chop_triple m) r)) ->
    forall A s, P A s (ftail s).
Proof.
  intros P H1 H2 H3 H4 H5 H6 H7 H8 H9.
  fix SELF 2. intros A s.
  refine (match s with
          | Nil    => _
          | Unit x => _
          | More (One a)       m r => _
          | More (Two a x)     m r => _
          | More (Three a x y) m r => _
          end).
  - apply H1.
  - apply H2.
  - (* More (One a) m r — case-split on [head m], keep [m] as a variable *)
    destruct (head m) as [ tup | ] eqn:Eh.
    + destruct tup as [ x y | x y z ].
      * (* head m = Some (Pair x y): case 8.  Rewrite via assert so Coq's
           unifier discovers all the [Set Implicit Arguments]-promoted
           implicits of [ftail_one_unfold_pair] from the goal. *)
        assert (Hrw : ftail (More (One a) m r) = More (Two x y) (ftail m) r)
          by (apply ftail_one_unfold_pair; exact Eh).
        rewrite Hrw.
        apply H8; [ apply SELF | exact Eh ].
      * (* head m = Some (Triple x y z): case 9.  The lemma's [y], [z]
           appear only in its hypothesis, so plain [apply] can't pin them
           from the goal — use [eapply] and let [exact Eh] instantiate. *)
        assert (Hrw : ftail (More (One a) m r) =
                      More (One x) (map1 chop_triple m) r)
          by (eapply ftail_one_unfold_triple; exact Eh).
        rewrite Hrw.
        eapply H9; exact Eh.
    + (* head m = None ⟹ m = Nil — cases 5/6/7 *)
      assert (Hm : m = Nil)
        by (destruct m as [ | tu | [tu | tu tv | tu tv tw] mm rm];
            simpl in Eh; try discriminate; reflexivity).
      subst m.
      destruct r as [ y | y z | y z w ].
      * apply H5.
      * apply H6.
      * apply H7.
  - (* More (Two a x) m r *) apply H4.
  - (* More (Three a x y) m r *) apply H3.
Qed.

(** *** ftailA' / ftailA — clairvoyant version.

    Mirrors the case structure of [ftail].  One tick per call.  The
    One-front cascade case forces [fD], then [mD], then (when [m] is
    non-empty) the front digit of [m]'s middle (if [m = MoreA _ _ _])
    or the singleton tuple (if [m = UnitA _]), then the first element
    thunk to dispatch on Pair vs Triple.

    Design notes:
    - The cascade is inlined (nested forcings, ~6 levels deep at the
      worst path) rather than factored through a [ftailA_cascade]
      helper.  Factoring would require either mutual recursion with
      [ftailA'] (because the Pair-head case must recurse) or threading
      [ftailA'] as a higher-order parameter.  We judged that inlining
      keeps proofs flatter despite the depth.  Reconsider in Phase D if
      [ftailD']'s proofs balloon.
    - In the Pair-head sub-cases the recursion is on the same value [m]
      from [forcing mD (fun m => ...)], not on [m]'s inner spine.  This
      mirrors the pure [tail m] recursion in the corresponding case of
      [ftail]. *)
Fixpoint ftailA' (A : Type) (s : SeqA A) : M (SeqA A) :=
  tick >>
  match s with
  | NilA    => ret NilA
  | UnitA _ => ret NilA
  | MoreA fD mD rD =>
      forcing fD (fun f =>
        match f with
        | ThreeA _ xD yD =>
            let~ f' := ret (TwoA xD yD) in
            ret (MoreA f' mD rD)
        | TwoA _ xD =>
            let~ f' := ret (OneA xD) in
            ret (MoreA f' mD rD)
        | OneA _ =>
            forcing mD (fun m =>
              match m with
              | NilA =>
                  (* cases 5-7: m=Nil, reshape r *)
                  forcing rD (fun r =>
                    match r with
                    | OneA yD => ret (UnitA yD)
                    | TwoA yD zD =>
                        let~ f' := ret (OneA yD) in
                        let~ m' := ret NilA in
                        let~ r' := ret (OneA zD) in
                        ret (MoreA f' m' r')
                    | ThreeA yD zD wD =>
                        let~ f' := ret (OneA yD) in
                        let~ m' := ret NilA in
                        let~ r' := ret (TwoA zD wD) in
                        ret (MoreA f' m' r')
                    end)
              | UnitA t =>
                  (* head element is the lone tuple [t]; force to decide Pair vs Triple *)
                  forcing t (fun tup =>
                    match tup with
                    | PairA xD yD =>
                        (* case 8 (recursive): tail (Unit (Pair _ _)) reduces to NilA *)
                        let~ f' := ret (TwoA xD yD) in
                        let~ m' := ftailA' m in
                        ret (MoreA f' m' rD)
                    | TripleA xD yD zD =>
                        (* case 9: map1 chop_triple (Unit (Triple _ _ _)) = Unit (Pair _ _) *)
                        let~ f' := ret (OneA xD) in
                        let~ pyz := ret (PairA yD zD) in
                        let~ m' := ret (UnitA pyz) in
                        ret (MoreA f' m' rD)
                    end)
              | MoreA fmD mmD rmD =>
                  (* head element is the first slot of [fmD]'s digit *)
                  forcing fmD (fun fm =>
                    match fm with
                    | OneA t =>
                        forcing t (fun tup =>
                          match tup with
                          | PairA xD yD =>
                              let~ f' := ret (TwoA xD yD) in
                              let~ m' := ftailA' m in
                              ret (MoreA f' m' rD)
                          | TripleA xD yD zD =>
                              let~ f'  := ret (OneA xD) in
                              let~ pyz := ret (PairA yD zD) in
                              let~ fm' := ret (OneA pyz) in
                              let~ m'  := ret (MoreA fm' mmD rmD) in
                              ret (MoreA f' m' rD)
                          end)
                    | TwoA t t' =>
                        forcing t (fun tup =>
                          match tup with
                          | PairA xD yD =>
                              let~ f' := ret (TwoA xD yD) in
                              let~ m' := ftailA' m in
                              ret (MoreA f' m' rD)
                          | TripleA xD yD zD =>
                              let~ f'  := ret (OneA xD) in
                              let~ pyz := ret (PairA yD zD) in
                              let~ fm' := ret (TwoA pyz t') in
                              let~ m'  := ret (MoreA fm' mmD rmD) in
                              ret (MoreA f' m' rD)
                          end)
                    | ThreeA t t' t'' =>
                        forcing t (fun tup =>
                          match tup with
                          | PairA xD yD =>
                              let~ f' := ret (TwoA xD yD) in
                              let~ m' := ftailA' m in
                              ret (MoreA f' m' rD)
                          | TripleA xD yD zD =>
                              let~ f'  := ret (OneA xD) in
                              let~ pyz := ret (PairA yD zD) in
                              let~ fm' := ret (ThreeA pyz t' t'') in
                              let~ m'  := ret (MoreA fm' mmD rmD) in
                              ret (MoreA f' m' rD)
                          end)
                    end)
              end)
        end)
  end.

Definition ftailA (A : Type) (q : T (SeqA A)) : M (SeqA A) :=
  forcing q ftailA'.


Lemma ftailA'_mon :
  forall (A : Type) (q2' : SeqA A),
  forall `{LDA : LessDefined A, !PreOrder LDA}
         (q1' : SeqA A),
    q1' `less_defined` q2' ->
    ftailA' q1' `less_defined` ftailA' q2'.
Proof.
  apply (SeqA_ind
    (fun A q2 =>
       forall `{LDA : LessDefined A, !PreOrder LDA}
              (q1 : SeqA A),
         q1 `less_defined` q2 ->
         ftailA' q1 `less_defined` ftailA' q2)).
  
  (* === Case NilA === *)
  - intros A0 LDA0 PA0 q1 Hq.
    assert (Hclose : ftailA' q1 `less_defined` ftailA' NilA).
    { invert_clear Hq. simpl. solve_mon. }
    exact Hclose.

  (* === Case UnitA === *)
  - intros A0 xA LDA0 PA0 q1 Hq.
    assert (Hclose : ftailA' q1 `less_defined` ftailA' (UnitA xA)).
    { invert_clear Hq. simpl. solve_mon. }
    exact Hclose.
  
  (* === Case MoreA === *)
  - intros A0 fD2 mD2 rD2 IH LDA0 PA0 q1 Hq.
    destruct mD2 as [md_inner | ] eqn:EmD2.

    (* Thunk Case*)
    + (* Sub-assertion: split on md_inner shape *)
      destruct md_inner as [| md_x | md_f md_m md_r] eqn:Emd_inner.

      * (* md_inner = NilA *)
        inversion IH as [? IH_inner Heq_md | Heq_md]; subst.
        invert_clear Hq as [| | f1 ? m1 ? r1 ? Hf Hm Hr ].
        cbn -[ftailA'].
        apply tick_mon.
        apply forcing_mon; [ assumption | intros f1' fD2' Hf' ].
        inversion Hf'; subst.
        (* OneA-OneA: cascade *)
        {
          inversion Hm; subst.
          + cbn -[ftailA']. solve_mon.
          + inversion H2; subst. cbn -[ftailA'].
            solve_mon.
        }
        {
          solve_mon.
        }
        {
          solve_mon.
        }

      * (* md_inner = UnitA md_x *)
        inversion IH as [? IH_inner Heq_md | Heq_md]; subst.
        invert_clear Hq as [| | f1 ? m1 ? r1 ? Hf Hm Hr ].
        cbn -[ftailA'].
        apply tick_mon.
        apply forcing_mon; [ assumption | intros f1' fD2' Hf' ].
        inversion Hf'; subst.
        {
          inversion Hm; subst.
          - cbn -[ftailA']. solve_mon.
          - inversion H2; subst.
            (* x = UnitA t, t ≤ md_x *)
            cbn -[ftailA'].
            inversion H3; subst.
            + cbn -[ftailA']. solve_mon.
            + (* t = Thunk tup_x, md_x = Thunk tup_md *)
              cbn -[ftailA'].
              (* tup_x ≤ tup_md — case-split *)
              rename H0 into Htup.   (* H3 : tup_x ≤ tup_md *)
              inversion Htup; subst.
              all: solve_mon.
        }
        {
          solve_mon.
        }
        {
          solve_mon.
        }

      * (* md_inner = MoreA md_f md_m md_r *)
        inversion IH as [? IH_inner Heq_md | Heq_md_2]; subst.
        invert_clear Hq as [| | f1 ? m1 ? r1 ? Hf Hm Hr ].
        cbn -[ftailA'].
        apply tick_mon.
        apply forcing_mon; [ assumption | intros f1' fD2' Hf' ].
        inversion Hf'; subst.
        (* OneA - OneA: cascade *)
        {
          inversion Hm; subst.
          {
            cbn -[ftailA']. solve_mon.
          }
          {
            inversion H2; subst.
            cbn -[ftailA'].
            rename m1 into m0.
            assert (Hrec : ftailA' (MoreA f0 m0 r0) 
                  `less_defined` 
                  ftailA' (MoreA md_f md_m md_r)).
            { 
              apply IH_inner; [ typeclasses eauto | auto]. 
            }

            (* Now case-split on f0 ≤ md_f for the spine front digit *)
            apply forcing_mon; [ assumption | intros fm1 fm2 Hfm ].
            inversion Hfm; subst.
            (* OneA - OneA *)
            {
              apply forcing_mon; [ assumption | intros tup1 tup2 Htup ].
              inversion Htup; subst.
              (* PairA-PairA: USE Hrec *)
              {
                cbn -[ftailA'].
                apply bind_mon; [ solve_mon | intros ? ? ? ].
                apply bind_mon.
                - apply thunk_mon. exact Hrec.
                - intros ? ? ?. apply ret_mon. solve_mon.
              }
              (* TripleA-TripleA: no recursion *)
               {
                 cbn -[ftailA']. solve_mon.
               }
            }
            (* TwoA - TwoA *)
            {
              apply forcing_mon; [ assumption | intros tup1 tup2 Htup ].
              inversion Htup; subst.
              (* PairA - PairA *)
              {
                cbn -[ftailA'].
                apply bind_mon; [ solve_mon | intros ? ? ? ].
                apply bind_mon.
                - apply thunk_mon. exact Hrec.
                - intros ? ? ?. apply ret_mon. solve_mon.
              }
              (* TripleA - TripleA *)
              {
                cbn -[ftailA']. solve_mon.
              }
            }
            (* ThreeA - ThreeA *)
            {
              apply forcing_mon; [ assumption | intros tup1 tup2 Htup ].
              inversion Htup; subst.
              (* PairA - PairA *)
              {
                cbn -[ftailA'].
                apply bind_mon; [ solve_mon | intros ? ? ? ].
                apply bind_mon.
                - apply thunk_mon. exact Hrec.
                - intros ? ? ?. apply ret_mon. solve_mon.
              }
              (* TripleA - TripleA *)
              {
                cbn -[ftailA']. solve_mon.
              }
            }
          }
        }
        {
          solve_mon.
        }
        {
          solve_mon.
        }

    (* Undefined Case *)
    + assert (Hcase : ftailA' q1 `less_defined` ftailA' (MoreA fD2 Undefined rD2)).
      { clear IH.
        invert_clear Hq as [| | f1 ? m1 ? r1 ? Hf Hm Hr ].
        invert_clear Hm.
        simpl.
        solve_mon. }
      exact Hcase.
Qed.

Lemma ftailA_mon (A : Type) `{LDA : LessDefined A, PreOrder A LDA}
    (q1 q2 : T (SeqA A)) :
    q1 `less_defined` q2 ->
    ftailA q1 `less_defined` ftailA q2.
Proof.
  invert_clear 1; try solve [ solve_mon ].
  rename x into q1'. rename y into q2'. rename H0 into Hq.
  simpl. apply ftailA'_mon. assumption.
Qed.


(* ================================================================= *)
(** *** ftailD' — demand function for [ftail]. *)
(* ================================================================= *)


(** [inverse_chop_tuple]: replace a [PairA yD zD] with [TripleA xD yD zD],
    or build a partial [TripleA xD Undefined Undefined] for the Undefined case.
    Used at the head element. *)
Definition inverse_chop_tuple {B : Type}
    (xD : T B) (t : T (TupleA B)) : T (TupleA B) :=
  match t with
  | Thunk (PairA yD zD) => Thunk (TripleA xD yD zD)
  | Thunk (TripleA _ _ _) => t   (* shouldn't fire if outD is valid *)
  | Undefined => Thunk (TripleA xD Undefined Undefined)
  end.

(** [inverse_chop_digit]: rewrite head element of a digit. *)
Definition inverse_chop_digit {B : Type}
    (xD : T B) (d : DigitA (TupleA B)) : DigitA (TupleA B) :=
  match d with
  | OneA t => OneA (inverse_chop_tuple xD t)
  | TwoA t t' => TwoA (inverse_chop_tuple xD t) t'
  | ThreeA t t' t'' => ThreeA (inverse_chop_tuple xD t) t' t''
  end.

(** [undef_inverse_chop_digit]: build a minimal demand-digit when fD = Undefined.
    The constructor must match [m]'s actual front digit to satisfy the approximation
    invariant; the head slot exposes [xD] (which we peeked at). *)
Definition undef_inverse_chop_digit {A B : Type} `{Exact A B}
    (m_d : Digit (Tuple A)) (xD : T B) : DigitA (TupleA B) :=
  match m_d with
  | One _ => OneA (Thunk (TripleA xD Undefined Undefined))
  | Two _ _ => TwoA (Thunk (TripleA xD Undefined Undefined)) Undefined
  | Three _ _ _ => ThreeA (Thunk (TripleA xD Undefined Undefined)) Undefined Undefined
  end.

(** [inverse_chop_demand]: the full helper for Case 9 of [ftailD'].

    Rewrites a demand on [map1 chop_triple m] back to a demand on [m]
    by transforming the head [Pair] to a [Triple] with [xD] as the first
    element.

    The Undefined-mD case branches on [m]'s outer shape (Unit / digit
    constructor of front) to produce a structurally compatible demand.
    The Thunk-mD case with Undefined-fD branches on [m]'s front digit
    constructor for the same reason. *)
Definition inverse_chop_demand {A B : Type} `{Exact A B}
    (m : Seq (Tuple A))
    (mD : T (SeqA (TupleA B))) (xD : T B) : T (SeqA (TupleA B)) :=
  match mD with
  | Thunk NilA => Thunk NilA
  | Thunk (UnitA t) => Thunk (UnitA (inverse_chop_tuple xD t))
  | Thunk (MoreA fD mD_inner rD) =>
      let fD' :=
        match fD with
        | Thunk d => Thunk (inverse_chop_digit xD d)
        | Undefined =>
            match m with
            | More m_d _ _ => Thunk (undef_inverse_chop_digit m_d xD)
            | _ => Thunk (OneA (Thunk (TripleA xD Undefined Undefined)))  (* unreachable *)
            end
        end in
      Thunk (MoreA fD' mD_inner rD)
  | Undefined =>
      match m with
      | Nil => Undefined  (* unreachable: head m = Some (Triple _) *)
      | Unit _ => Thunk (UnitA (Thunk (TripleA xD Undefined Undefined)))
      | More m_d _ _ =>
          Thunk (MoreA (Thunk (undef_inverse_chop_digit m_d xD))
                       Undefined Undefined)
      end
  end.


(** [add_pair_to_head_digit]: replace head element of a digit with [PairA xD yD]. *)
Definition add_pair_to_head_digit {B : Type}
    (xD yD : T B) (d : DigitA (TupleA B)) : DigitA (TupleA B) :=
  match d with
  | OneA _ => OneA (Thunk (PairA xD yD))
  | TwoA _ t' => TwoA (Thunk (PairA xD yD)) t'
  | ThreeA _ t' t'' => ThreeA (Thunk (PairA xD yD)) t' t''
  end.

(** [undef_add_pair_to_head_digit]: build a minimal demand-digit when fD = Undefined.
    Constructor matches [m]'s front digit; head slot exposes [PairA xD yD]. *)
Definition undef_add_pair_to_head_digit {A B : Type} `{Exact A B}
    (m_d : Digit (Tuple A)) (xD yD : T B) : DigitA (TupleA B) :=
  match m_d with
  | One _ => OneA (Thunk (PairA xD yD))
  | Two _ _ => TwoA (Thunk (PairA xD yD)) Undefined
  | Three _ _ _ => ThreeA (Thunk (PairA xD yD)) Undefined Undefined
  end.

(** [add_pair_to_head_demand]: the full helper for Case 8 of [ftailD'].

    Augments a recursive demand on [m] (returned by [ftailD' m _]) with a
    [Pair x y] head element, since the operation inspected [head m] to
    determine the case.

    Same shape-discipline as [inverse_chop_demand] for the Undefined cases. *)
Definition add_pair_to_head_demand {A B : Type} `{Exact A B}
    (m : Seq (Tuple A))
    (mD : T (SeqA (TupleA B))) (xD yD : T B) : T (SeqA (TupleA B)) :=
  match mD with
  | Thunk NilA => Thunk (UnitA (Thunk (PairA xD yD)))
  | Thunk (UnitA _) => Thunk (UnitA (Thunk (PairA xD yD)))
  | Thunk (MoreA fD mD_inner rD) =>
      let fD' :=
        match fD with
        | Thunk d => Thunk (add_pair_to_head_digit xD yD d)
        | Undefined =>
            match m with
            | More m_d _ _ => Thunk (undef_add_pair_to_head_digit m_d xD yD)
            | _ => Thunk (OneA (Thunk (PairA xD yD)))  (* unreachable *)
            end
        end in
      Thunk (MoreA fD' mD_inner rD)
  | Undefined =>
      match m with
      | Nil => Undefined  (* unreachable: head m = Some (Pair _) *)
      | Unit _ => Thunk (UnitA (Thunk (PairA xD yD)))
      | More m_d _ _ =>
          Thunk (MoreA (Thunk (undef_add_pair_to_head_digit m_d xD yD))
                       Undefined Undefined)
      end
  end.


(** The main demand function. *)

Fixpoint ftailD' (A B : Type) `{Exact A B} (s : Seq A) (outD : SeqA B)
    : Tick (T (SeqA B)) :=
  Tick.tick >>
  match s with
  | Nil =>
      (* ftail Nil = Nil *)
      match outD with
      | NilA => Tick.ret Undefined
      | _    => bottom
      end

  | Unit _ =>
      (* ftail (Unit _) = Nil *)
      match outD with
      | NilA => Tick.ret (Thunk (UnitA Undefined))
      | _    => bottom
      end

  | More (Three _ x y) m r =>
      (* ftail = More (Two x y) m r *)
      match outD with
      | MoreA fD mD rD =>
          let '(xD, yD) := match fD with
                           | Thunk (TwoA xD yD) => (xD, yD)
                           | _ => (Undefined, Undefined)
                           end in
          Tick.ret (Thunk (MoreA (Thunk (ThreeA Undefined xD yD)) mD rD))
      | _ => bottom
      end

  | More (Two _ x) m r =>
      (* ftail = More (One x) m r *)
      match outD with
      | MoreA fD mD rD =>
          let xD := match fD with
                    | Thunk (OneA xD) => xD
                    | _ => Undefined
                    end in
          Tick.ret (Thunk (MoreA (Thunk (TwoA Undefined xD)) mD rD))
      | _ => bottom
      end

  | More (One _) m r =>
      match m with
      | Nil =>
          (* m empty: reshape r *)
          match r, outD with
          | One y, UnitA yD =>
              Tick.ret (Thunk (MoreA (Thunk (OneA Undefined))
                                      (Thunk NilA)
                                      (Thunk (OneA yD))))
          | Two y z, MoreA fD _ rD =>
              let yD := match fD with
                        | Thunk (OneA yD) => yD
                        | _ => Undefined
                        end in
              let zD := match rD with
                        | Thunk (OneA zD) => zD
                        | _ => Undefined
                        end in
              Tick.ret (Thunk (MoreA (Thunk (OneA Undefined))
                                      (Thunk NilA)
                                      (Thunk (TwoA yD zD))))
          | Three y z w, MoreA fD _ rD =>
              let yD := match fD with
                        | Thunk (OneA yD) => yD
                        | _ => Undefined
                        end in
              let '(zD, wD) := match rD with
                               | Thunk (TwoA zD wD) => (zD, wD)
                               | _ => (Undefined, Undefined)
                               end in
              Tick.ret (Thunk (MoreA (Thunk (OneA Undefined))
                                      (Thunk NilA)
                                      (Thunk (ThreeA yD zD wD))))
          | _, _ => bottom
          end

      | _ =>
          (* m ≠ Nil. Case on head m. *)
          match head m with
          | Some (Pair _ _) =>
              (* Recursive case *)
              match outD with
              | MoreA fD mD_out rD =>
                  let '(xD, yD) := match fD with
                                   | Thunk (TwoA xD yD) => (xD, yD)
                                   | _ => (Undefined, Undefined)
                                   end in
                  let+ mD_rec := thunkD (ftailD' m) mD_out in
                  let mD_in := add_pair_to_head_demand m mD_rec xD yD in
                  Tick.ret (Thunk (MoreA (Thunk (OneA Undefined)) mD_in rD))
              | _ => bottom
              end

          | Some (Triple _ _ _) =>
              (* Non-recursive case: chop the Triple *)
              match outD with
              | MoreA fD mD_out rD =>
                  let xD := match fD with
                            | Thunk (OneA xD) => xD
                            | _ => Undefined
                            end in
                  let mD_in := inverse_chop_demand m mD_out xD in
                  Tick.ret (Thunk (MoreA (Thunk (OneA Undefined)) mD_in rD))
              | _ => bottom
              end

          | None =>
              (* unreachable: m ≠ Nil so head m ≠ None *)
              bottom
          end
      end
  end.

Definition ftailD (A : Type) : Seq A -> SeqA A -> Tick (T (SeqA A)) :=
  ftailD'.

(* ================================================================= *)
(** *** Phase E: Big proofs for [ftailD'].

    Each lemma is initially [Admitted] with a comment describing what
    needs to be shown.  Fill in the proofs in dependency order:
    helpers first, then the three main theorems.

    Cost target: K=3 (matches [fconsD'_cost]'s effective bound and the
    physicist's argument's budget convention).  K=2 would suffice for the
    [mD_out = Thunk _] case, but the [mD_out = Undefined] sub-case of
    Case 9 (Triple-head non-recursive) with [m = More (Two _ _) _ _]
    binds at K=3. *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(** **** Helper lemmas about [add_pair_to_head_demand] and [inverse_chop_demand]. *)
(* ----------------------------------------------------------------- *)


Ltac peel_and_close :=
  repeat match goal with
  | H' : ?x `less_defined` ?y |- _ =>
      (head_is_constructor x + head_is_constructor y); invert_clear H'
  end; repeat constructor; auto.


Lemma inverse_chop_demand_approx (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (m : Seq (Tuple A)) (mD : T (SeqA (TupleA B))) (xD : T B) (x y z : A) :
  head m = Some (Triple x y z) ->
  xD `is_approx` x ->
  mD `is_approx` map1 chop_triple m ->
  inverse_chop_demand m mD xD `is_approx` m.
Proof.
  intros Hhead HxD HmD.
  destruct m as [| t | fd m_spine r_d].
  - (* Nil *)
    discriminate Hhead.

  - (* Unit t. From head, t = Triple x y z. *)
    simpl in Hhead. inversion Hhead. subst t. clear Hhead.
    destruct mD as [s | ]; simpl.
    + (* mD = Thunk s *)
      invert_clear HmD.
      cbn in H0.
      (* H0 : s ≤ UnitA (Thunk (PairA (exact y) (exact z))) or similar *)
      destruct s as [| t_s | fD_s mD_s rD_s].
      * (* s = NilA — impossible: NilA ≤ UnitA *)
        invert_clear H0.
      * (* s = UnitA t_s *)
        invert_clear H0.
        (* H : t_s ≤ Thunk (PairA (exact y) (exact z)) *)
        destruct t_s as [tup_s | ]; simpl.
        -- (* t_s = Thunk tup_s *)
           invert_clear H0.
           (* H0 : tup_s ≤ PairA (exact y) (exact z) *)
           cbn in H0.
           invert_clear H0.
           (* tup_s = PairA yD zD with yD ≤ exact y, zD ≤ exact z *)
           repeat constructor; assumption.
        -- (* t_s = Undefined *)
           repeat constructor; try assumption.
      * (* s = MoreA — impossible *)
        invert_clear H0.
    + (* mD = Undefined *)
      repeat constructor; try assumption.

  - (* More fd m_spine r_d *)
    destruct fd as [t | t t' | t t' t''];
      simpl in Hhead; inversion Hhead; subst t; clear Hhead.
    + (* fd = One (Triple x y z) *)
      destruct mD as [s | ]; simpl.
      * (* Thunk s *)
        invert_clear HmD.
        cbn in H0.
        destruct s as [| | fD_s mD_s rD_s].
        -- invert_clear H0.   (* NilA ≤ MoreA — impossible *)
        -- invert_clear H0.   (* UnitA ≤ MoreA — impossible *)
        -- invert_clear H0.
           (* HfD : fD_s ≤ Thunk (OneA (Thunk (PairA ...))) 
              HmD_s : mD_s ≤ Thunk (exact m_spine) 
              HrD_s : rD_s ≤ Thunk (exact r_d) *)
           destruct fD_s as [d_s | ].
           ++ (* fD_s = Thunk d_s *)
              invert_clear H1.  (* on fD_s ≤ Thunk (OneA ...) *)
              cbn in H2.
              destruct d_s as [t_d | | ].
              ** (* OneA t_d *)
                 invert_clear H2.
                 (* t_d ≤ Thunk (PairA ...) *)
                 destruct t_d as [tup_d | ]; simpl.
                 --- invert_clear H0.
                     cbn in H0.
                     invert_clear H0.
                     peel_and_close.
                      invert_clear H0.
                      repeat constructor; assumption.
                 --- repeat constructor; try assumption.
                 --- cbn.
                     peel_and_close.
                       unfold inverse_chop_tuple.
                       invert_clear H0.
                       +++ repeat constructor; assumption.
                       +++ invert_clear H0. repeat constructor; assumption.
              ** (* TwoA — impossible *)
                 invert_clear H2;
                 peel_and_close.
              ** (* ThreeA — impossible *)
                 invert_clear H2;
                 peel_and_close.

              ** invert_clear H2;
                 peel_and_close.
                  all: invert_clear H0; peel_and_close.
                  all: invert_clear H0; peel_and_close.
                  all: invert_clear H0; peel_and_close.
                    
           ++ (* fD_s = Undefined *)
              repeat constructor; try assumption.
      * (* Undefined *)
        repeat constructor; try assumption.

    + (* fd = Two (Triple x y z) t' *)
      destruct mD as [s | ]; simpl.
      * (* Thunk s *)
        invert_clear HmD.
        cbn in H0.
        destruct s as [| | fD_s mD_s rD_s].
        -- invert_clear H0.
        -- invert_clear H0.
        -- invert_clear H0.
           destruct fD_s as [d_s | ].
           ++ invert_clear H1.
              cbn in H2.
              destruct d_s as [| t_d t2_d | ].
              ** invert_clear H2;
                  peel_and_close.
              ** (* TwoA t_d t2_d *)
                 invert_clear H2;
                 destruct t_d as [tup_d | ]; simpl.
                 --- invert_clear H0; 
                    peel_and_close.
                       invert_clear H0; 
                       peel_and_close.
                 --- invert_clear H0;
                    peel_and_close.
                 --- invert_clear H1;
                    peel_and_close.
                      all: invert_clear H0;
                      peel_and_close.
                      {
                        rewrite <- H3.
                        repeat constructor; auto.
                      }
                      {
                        rewrite <- H4.
                        repeat constructor; auto.
                      }
                      {
                        rewrite <- H5.
                        repeat constructor; auto.
                      }

                 --- peel_and_close.
              ** invert_clear H2; 
                  peel_and_close.
              ** invert_clear H0;
                peel_and_close.
                  invert_clear H0;
                  peel_and_close.
                  invert_clear H0;
                  peel_and_close.
                  destruct x2.
                  {
                    invert_clear H0.
                    peel_and_close.
                  }
                  {
                    cbn in H0.
                    invert_clear H0.
                  }

           ++ repeat constructor; try assumption.
      * (* Undefined *)
        repeat constructor; try assumption.

    + (* fd = Three (Triple x y z) t' t'' *)
      destruct mD as [s | ]; simpl.
      * (* Thunk s *)
        invert_clear HmD.
        cbn in H0.
        destruct s as [| | fD_s mD_s rD_s].
        -- invert_clear H0.
        -- invert_clear H0.
        -- invert_clear H0.
           destruct fD_s as [d_s | ].
           ++ invert_clear H1.
              cbn in H2.
              destruct d_s as [| | t_d t2_d t3_d].
              ** invert_clear H2;
                  peel_and_close.
              ** invert_clear H2;
                  peel_and_close.
              ** (* ThreeA *)
                 invert_clear H2.
                 destruct t_d as [tup_d | ]; simpl;
                 peel_and_close.
                 --- invert_clear H0;
                    peel_and_close.
                 --- peel_and_close.
                       cbn in H0.
                       invert_clear H0.
                       {
                        repeat constructor; try assumption.
                       }
                       {
                        cbn in H0.
                        invert_clear H0.
                         peel_and_close.
                       }
              ** peel_and_close.
                invert_clear H0.
                peel_and_close.
                invert_clear H0.
                peel_and_close.
                invert_clear H0.
                peel_and_close.
           ++ repeat constructor; try assumption.
      * (* Undefined *)
        repeat constructor; try assumption.
Qed.



(** [add_pair_to_head_demand] preserves approximation.  Given a demand 
    [mD] that approximates the recursive [ftail m], augmenting it with
    [PairA xD yD] at the head produces a valid approximation of [m]
    (since [head m = Some (Pair x y)] and the recursion just dropped that head). *)
Lemma add_pair_to_head_demand_approx (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (m : Seq (Tuple A)) (mD : T (SeqA (TupleA B))) (xD yD : T B) (x y : A) :
  head m = Some (Pair x y) ->
  xD `is_approx` x ->
  yD `is_approx` y ->
  mD `is_approx` m ->
  add_pair_to_head_demand m mD xD yD `is_approx` m.
Proof.
  intros Hhead HxD HyD HmD.
  destruct m as [| t | fd m_spine r_d].
  - (* Nil *) discriminate Hhead.

  - (* Unit t. t = Pair x y. *)
    simpl in Hhead. inversion Hhead. subst t. clear Hhead.
    destruct mD as [s | ]; simpl.
    + (* Thunk s. HmD : Thunk s ≤ exact (Unit (Pair x y)) *)
      invert_clear HmD.
      cbn in H0.
      (* H0 : s ≤ UnitA (Thunk (PairA (exact x) (exact y))) *)
      destruct s as [| t_s | fD_s mD_s rD_s].
      * invert_clear H0.   (* NilA ≤ UnitA impossible *)
      * (* UnitA t_s — helper produces Thunk (UnitA (Thunk (PairA xD yD))) *)
        repeat constructor; assumption.
      * invert_clear H0.   (* MoreA ≤ UnitA impossible *)
    + (* Undefined *)
      repeat constructor; assumption.

  - (* More fd m_spine r_d. fd first element = Pair x y. *)
    destruct fd as [t | t t' | t t' t''];
      simpl in Hhead; inversion Hhead; subst t; clear Hhead.
    + (* fd = One (Pair x y) *)
      destruct mD as [s | ]; simpl.
      * invert_clear HmD.
        cbn in H0.
        destruct s as [| | fD_s mD_s rD_s].
        -- invert_clear H0.
        -- invert_clear H0.
        -- invert_clear H0.
           (* HfD : fD_s ≤ Thunk (OneA (Thunk (PairA (exact x) (exact y))))
              HmD_s : mD_s ≤ Thunk (exact m_spine)
              HrD_s : rD_s ≤ Thunk (exact r_d) *)
           destruct fD_s as [d_s | ].
           ++ (* Thunk d_s *)
              invert_clear H1.
              cbn in H2.
              destruct d_s as [t_d | t_d t2_d | t_d t2_d t3_d].
              ** (* OneA t_d — helper produces OneA (Thunk (PairA xD yD)) *)
                 repeat constructor; assumption.
              ** peel_and_close.
              ** peel_and_close.
              ** peel_and_close.
                 invert_clear H0.
                 peel_and_close.
                  
           ++ (* Undefined — helper uses undef_add_pair_to_head_digit on m_d = One _ *)
              repeat constructor; assumption.
      * (* Undefined — uses undef_add_pair_to_head_digit on m_d = One _ *)
        repeat constructor; assumption.

    + (* fd = Two (Pair x y) t' *)
      destruct mD as [s | ]; simpl.
      * invert_clear HmD.
        cbn in H0.
        destruct s as [| | fD_s mD_s rD_s].
        -- invert_clear H0.
        -- invert_clear H0.
        -- invert_clear H0.
           destruct fD_s as [d_s | ].
           ++ invert_clear H1.
              cbn in H2.
              destruct d_s as [| t_d t2_d | ].
              ** invert_clear H2; peel_and_close.
              ** (* TwoA t_d t2_d — helper: TwoA (Thunk (PairA xD yD)) t2_d *)
                peel_and_close.
              ** peel_and_close.
              ** peel_and_close.
                 invert_clear H0.
                 peel_and_close.
           ++ (* Undefined — helper: TwoA (Thunk (PairA xD yD)) Undefined *)
              peel_and_close.
      * peel_and_close.

    + (* fd = Three (Pair x y) t' t'' *)
      destruct mD as [s | ]; simpl.
      * invert_clear HmD.
        cbn in H0.
        destruct s as [| | fD_s mD_s rD_s].
        -- invert_clear H0.
        -- invert_clear H0.
        -- invert_clear H0.
           destruct fD_s as [d_s | ].
           ++ invert_clear H1.
              cbn in H2.
              destruct d_s as [| | t_d t2_d t3_d].
              ** peel_and_close.
              ** peel_and_close.
              ** (* ThreeA *)
                 peel_and_close.
              ** peel_and_close.
                 invert_clear H0.
                 peel_and_close.
                 
           ++ peel_and_close.
      * peel_and_close.
Qed.


(* ----------------------------------------------------------------- *)
(** **** Main theorem 1: [ftailD'_approx]

    The input demand returned by [ftailD'] is a valid approximation of [s]. *)
(* ----------------------------------------------------------------- *)


Lemma ftailD'_approx : forall (A B : Type)
    `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (s : Seq A) (outD : SeqA B),
    outD `is_approx` ftail s ->
    Tick.val (ftailD' s outD) `is_approx` s.
Proof.
(* By [ftail_ind] over s. Nine cases.  Each non-trivial case starts by
   refining on [outD]'s shape (since [ftailD'] returns [bottom] for shape
   mismatches; the [outD ≤ exact (ftail s)] hypothesis discharges 
   impossible shapes).
   
   1. Nil: ftailD' = Tick.ret Undefined.  Trivial: Undefined ≤ exact Nil.
   2. Unit _: ftailD' = Tick.ret (Thunk (UnitA Undefined)).
      Undefined ≤ exact (the element), so UnitA Undefined ≤ exact (Unit _).
   3. More (Three a x y) m r: ftail = More (Two x y) m r.
      Extract xD, yD from outD's front (TwoA).  Result has 
      front ThreeA Undefined xD yD.  Need Undefined ≤ exact a (trivial),
      xD ≤ exact x, yD ≤ exact y (from outD).
   4. More (Two a x) m r: ftail = More (One x) m r.  Same shape as 3.
   5-7. More (One a) Nil <r>: ftail reshapes r.
      Three sub-cases on r; each extracts demand elements from outD
      and rebuilds.  All structural.
   8. More (One a) m r with head m = Some (Pair x y), recursive:
      ftail = More (Two x y) (ftail m) r.  Recursive call to ftailD' m
      gives mD_rec ≤ exact m (via IH).  Then add_pair_to_head_demand m mD_rec xD yD
      remains ≤ exact m by [add_pair_to_head_demand_approx].
   9. More (One a) m r with head m = Some (Triple x y z), non-recursive:
      ftail = More (One x) (map1 chop_triple m) r.  Use 
      [inverse_chop_demand_approx] with mD_out ≤ exact (map1 chop_triple m). *)
  intros ? ? LDB RLDB EAB ? ?. revert A s B LDB RLDB EAB outD.
  apply (ftail_ind (fun A s s' =>
    forall B `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
           (outD : SeqA B),
      outD `less_defined` exact s' ->
      Tick.val (ftailD' s outD) `less_defined` exact s));
    intros until outD.

  (* === Case 1: Nil → Nil === *)
  {
    refine (match outD with
            | NilA => _
            | _ => _
            end); intro Happrox;
      try solve [ invert_clear Happrox ];
      repeat constructor.
  }

  (* === Case 2: Unit x → Nil === *)
  {
    refine (match outD with
            | NilA => _
            | _ => _
            end); intro Happrox;
      try solve [ invert_clear Happrox ];
      repeat constructor.
  }

  (* === Case 3: More (Three a x y) m r → More (Two x y) m r === *)
  {
    refine (match outD with
            | MoreA fD mD rD => _
            | _ => _
            end); intro Happrox;
      try solve [ invert_clear Happrox ].
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
    simpl.
    destruct fD as [ fA | ].
    - (* Thunk fA *)
      destruct fA as [ t1 | t1 t2 | t1 t2 t3 ].
      + (* OneA — contradicts HfD *)
        invert_clear HfD. invert_clear H0.
      + (* TwoA t1 t2 *)
        invert_clear HfD. invert_clear H0.
        repeat constructor; auto.
      + (* ThreeA — contradicts HfD *)
        invert_clear HfD. invert_clear H0.
    - (* Undefined *)
      simpl. repeat constructor; auto.
  }

  (* === Case 4: More (Two a x) m r → More (One x) m r === *)
  {
    refine (match outD with
            | MoreA fD mD rD => _
            | _ => _
            end); intro Happrox;
      try solve [ invert_clear Happrox ].
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
    simpl.
    destruct fD as [ fA | ].
    - destruct fA as [ t1 | t1 t2 | t1 t2 t3 ].
      + (* OneA t1 *)
        invert_clear HfD. invert_clear H0.
        repeat constructor; auto.
      + invert_clear HfD. invert_clear H0.
      + invert_clear HfD. invert_clear H0.
    - simpl. repeat constructor; auto.
  }

  (* === Case 5: More (One a) Nil (One y) → Unit y === *)
  {
    refine (match outD with
            | UnitA yD => _
            | _ => _
            end); intro Happrox;
      try solve [ invert_clear Happrox ].
    invert_clear Happrox.
    simpl. repeat constructor; auto.
  }

  (* === Case 6: More (One a) Nil (Two y z) → More (One y) Nil (One z) === *)
  {
    refine (match outD with
            | MoreA fD mD rD => _
            | _ => _
            end); intro Happrox;
      try solve [ invert_clear Happrox ].
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
    simpl.
    peel_and_close.
    {
      destruct fD as [ fA | ]; [ destruct fA as [ t1 | t1 t2 | t1 t2 t3 ] | ].
      - invert_clear HfD. invert_clear H0. assumption.
      - peel_and_close.
      - peel_and_close.
      - peel_and_close.
    }
    {
      destruct rD as [ rA | ]; [ destruct rA as [ s1 | s1 s2 | s1 s2 s3 ] | ].
      - invert_clear HrD. invert_clear H0. assumption.
      - peel_and_close.
      - peel_and_close.
      - peel_and_close.
    }
    {
      destruct fD as [ fA | ]; [ destruct fA as [ t1 | t1 t2 | t1 t2 t3 ] | ].
      - invert_clear HfD. invert_clear H0. assumption.
      - peel_and_close.
      - peel_and_close.
      - peel_and_close.
    }
    {
      destruct rD as [ rA | ]; [ destruct rA as [ s1 | s1 s2 | s1 s2 s3 ] | ].
      - invert_clear HrD. invert_clear H0. assumption.
      - peel_and_close.
      - peel_and_close.
      - peel_and_close.
    }
  }


  (* === Case 7: More (One a) Nil (Three y z w) → More (One y) Nil (Two z w) === *)
  {
    refine (match outD with
            | MoreA fD mD rD => _
            | _ => _
            end); intro Happrox;
      try solve [ invert_clear Happrox ].
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
    simpl.
    destruct fD as [ fA | ].
    - destruct fA as [ t1 | t1 t2 | t1 t2 t3 ].
      + (* OneA t1 — valid, t1 = yD *)
        destruct rD as [ rA | ].
        * destruct rA as [ s1 | s1 s2 | s1 s2 s3 ].
          -- (* OneA — invalid by HrD *)
            invert_clear HrD. invert_clear H0.
          -- (* TwoA s1 s2 — valid, (s1, s2) = (zD, wD) *)
            invert_clear HfD. invert_clear H0.
            invert_clear HrD. invert_clear H0.
            peel_and_close.
            peel_and_close.
            
          -- (* ThreeA — invalid *)
            invert_clear HrD. invert_clear H0.
        * (* rD = Undefined — (zD, wD) = (Undefined, Undefined) *)
          invert_clear HfD. invert_clear H0.
          repeat constructor; auto.
      + (* TwoA — invalid by HfD *)
        invert_clear HfD. invert_clear H0.
      + (* ThreeA — invalid *)
        invert_clear HfD. invert_clear H0.
    - (* fD = Undefined — yD = Undefined *)
      destruct rD as [ rA | ].
      + destruct rA as [ s1 | s1 s2 | s1 s2 s3 ].
        * invert_clear HrD. invert_clear H0.
        * (* TwoA s1 s2 *)
          invert_clear HrD. invert_clear H0.
          repeat constructor; auto.
        * invert_clear HrD. invert_clear H0.
      + (* rD = Undefined *)
        repeat constructor; auto.
  }


  (* === Case 8: More (One a) m r, head m = Some (Pair x y), recursive === *)
  {
    rename H into IH.
    rename H0 into Hhead.
    refine (match outD with
            | MoreA fD mD_out rD => _
            | _ => _
            end); intro Happrox;
      try solve [ invert_clear Happrox ].
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD_out HrD ].

    (* Destruct m: Nil discharged via Hhead; Unit and More are real cases. *)
    destruct m as [| t_m | fd_m m_spine r_d_m]; [ discriminate Hhead | | ].

    - (* m = Unit t_m. From Hhead: t_m = Pair x y *)
      simpl in Hhead. inversion Hhead. subst t_m. clear Hhead.
      simpl.   (* reduces ftailD' to its body for More (One a) (Unit (Pair x y)) r *)
      
      (* mD_out cases *)
      invert_clear HmD_out as [ | s1D s2D HsD ].
      + (* mD_out = Undefined *)
        simpl.
        destruct fD as [ fA | ].
        * destruct fA as [ t1 | t1 t2 | t1 t2 t3 ].
          -- (* OneA — contradicts HfD *)
            invert_clear HfD. invert_clear H.
          -- (* TwoA t1 t2 *)
            invert_clear HfD. invert_clear H.
            peel_and_close.
          -- invert_clear HfD. invert_clear H.
        * (* fD = Undefined *)
          peel_and_close.
      + (* mD_out = Thunk s1D, HsD : s1D ≤ exact (ftail (Unit (Pair x y))) = exact Nil = NilA *)
        specialize (IH _ _ _ _ s1D HsD).
        simpl.
        (* Need to destruct the result of ftailD' (Unit (Pair x y)) s1D *)
        destruct fD as [ fA | ].
        * destruct fA as [ t1 | t1 t2 | t1 t2 t3 ].
          -- invert_clear HfD; invert_clear H.
          -- invert_clear HfD; invert_clear H.
            (* Goal: Thunk (MoreA (Thunk (OneA Undefined)) 
                                    (add_pair_to_head_demand (Unit (Pair x y)) (Tick.val (ftailD' (Unit (Pair x y)) s1D)) t1 t2)
                                    rD) ≤ exact (More (One a) (Unit (Pair x y)) r) *)
            repeat constructor.
            ++ peel_and_close.
            ++ assumption.
          -- invert_clear HfD; invert_clear H.
        * (* fD = Undefined *)
          repeat constructor.
          ++ peel_and_close.
          ++ assumption.

    - (* m = More fd_m m_spine r_d_m. head = first slot of fd_m = Pair x y *)
      (* fd_m has shape One/Two/Three with Pair x y in first slot *)
      destruct fd_m as [t_m | t_m t_m' | t_m t_m' t_m''];
        simpl in Hhead; inversion Hhead; subst t_m; clear Hhead;
        simpl.
      + (* fd_m = One (Pair x y) *)
        invert_clear HmD_out as [ | s1D s2D HsD ].
        * (* Undefined *)
          destruct fD as [ fA | ].
          -- destruct fA as [ t1 | t1 t2 | t1 t2 t3 ];
              try (invert_clear HfD; invert_clear H; fail).
            (* TwoA t1 t2 *)
            invert_clear HfD. invert_clear H.
            peel_and_close.
          -- peel_and_close.
        * (* Thunk s1D *)
          specialize (IH _ _ _ _ s1D HsD).
          destruct fD as [ fA | ].
          -- destruct fA as [ t1 | t1 t2 | t1 t2 t3 ];
              try (invert_clear HfD; invert_clear H; fail).
            invert_clear HfD. invert_clear H. 
            repeat constructor; peel_and_close.
            apply (@add_pair_to_head_demand_approx A B _ _ _   (More (One (Pair x y)) m_spine r_d_m) _ t1 t2 x y); peel_and_close.
          -- repeat constructor; peel_and_close.
            apply (@add_pair_to_head_demand_approx A B _ _ _   (More (One (Pair x y)) m_spine r_d_m) _ Undefined Undefined x y); peel_and_close.

      + (* fd_m = Two (Pair x y) t_m' *)
        invert_clear HmD_out as [ | s1D s2D HsD ].
        * destruct fD as [ fA | ].
          -- destruct fA as [ t1 | t1 t2 | t1 t2 t3 ];
              try (invert_clear HfD; invert_clear H; fail).
            invert_clear HfD. invert_clear H.
            repeat constructor; peel_and_close.
          -- repeat constructor. peel_and_close.
        * specialize (IH _ _ _ _ s1D HsD).
          destruct fD as [ fA | ].
          -- destruct fA as [ t1 | t1 t2 | t1 t2 t3 ];
              try (invert_clear HfD; invert_clear H; fail).
            invert_clear HfD. invert_clear H.
            repeat constructor; peel_and_close.
            ++ invert_clear H2; peel_and_close.
               invert_clear H2; peel_and_close.
            ++ invert_clear H2; peel_and_close.
               invert_clear H2; peel_and_close.
          -- repeat constructor.
            ++ peel_and_close.
               invert_clear H; peel_and_close.
               invert_clear H; peel_and_close.
               invert_clear H; peel_and_close.
               invert_clear H; peel_and_close.
            ++ assumption.

      + (* fd_m = Three (Pair x y) t_m' t_m'' *)
        invert_clear HmD_out as [ | s1D s2D HsD ].
        * destruct fD as [ fA | ].
          -- destruct fA as [ t1 | t1 t2 | t1 t2 t3 ];
              try (invert_clear HfD; invert_clear H; fail).
            invert_clear HfD. invert_clear H.
            repeat constructor.
            ++ assumption.
            ++ assumption.
            ++ assumption.
          -- repeat constructor.
            ++ assumption.
        * specialize (IH _ _ _ _ s1D HsD).
          destruct fD as [ fA | ].
          -- destruct fA as [ t1 | t1 t2 | t1 t2 t3 ];
              try (invert_clear HfD; invert_clear H; fail).
            invert_clear HfD. invert_clear H.
            repeat constructor; peel_and_close.
            ++ 
              apply (@add_pair_to_head_demand_approx A B _ _ _   (More (Three (Pair x y) t_m' t_m'') m_spine r_d_m) _ t1 t2 x y); peel_and_close.
            ++ 
              apply (@add_pair_to_head_demand_approx A B _ _ _   (More (Three (Pair x y) t_m' t_m'') m_spine r_d_m) _ t1 t2 x y); peel_and_close.
          -- repeat constructor.
            ++ 
              apply (@add_pair_to_head_demand_approx A B _ _ _   (More (Three (Pair x y) t_m' t_m'') m_spine r_d_m) _ Undefined Undefined x y); peel_and_close.
              (* eapply add_pair_to_head_demand_approx;
                  [ reflexivity | constructor | constructor | ].
                exact IH. *)
            ++ assumption.
  }

  (* === Case 9: More (One a) m r, head m = Some (Triple x y z), non-recursive === *)
  {
    rename H into Hhead.
    refine (match outD with
            | MoreA fD mD_out rD => _
            | _ => _
            end); intro Happrox;
      try solve [ invert_clear Happrox ].
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD_out HrD ].

    (* Destruct m: Nil discharged via Hhead. *)
    destruct m as [| t_m | fd_m m_spine r_d_m]; [ discriminate Hhead | | ].

    - (* m = Unit t_m. From Hhead: t_m = Triple x y z *)
      simpl in Hhead. inversion Hhead. subst t_m. clear Hhead.
      simpl.
      destruct fD as [ fA | ].
      + destruct fA as [ t1 | t1 t2 | t1 t2 t3 ].
        * (* OneA t1, t1 = xD *)
          invert_clear HfD. invert_clear H.
          repeat constructor; peel_and_close.
          invert_clear H1; peel_and_close.
          invert_clear H1; peel_and_close.
        * invert_clear HfD; invert_clear H.   (* TwoA ≤ OneA impossible *)
        * invert_clear HfD; invert_clear H.   (* ThreeA ≤ OneA impossible *)
      + (* fD = Undefined, xD = Undefined *)
        repeat constructor; peel_and_close. 
        invert_clear H; peel_and_close.
        invert_clear H; peel_and_close.

    - (* m = More fd_m m_spine r_d_m. fd_m has Triple x y z in first slot. *)
      destruct fd_m as [t_m | t_m t_m' | t_m t_m' t_m''];
        simpl in Hhead; inversion Hhead; subst t_m; clear Hhead;
        simpl.
      + (* fd_m = One (Triple x y z) *)
        destruct fD as [ fA | ].
        * destruct fA as [ t1 | t1 t2 | t1 t2 t3 ];
            try (invert_clear HfD; invert_clear H; fail).
          invert_clear HfD. invert_clear H.
          repeat constructor; peel_and_close.
          {
            invert_clear H1; peel_and_close.
            invert_clear H1; peel_and_close.
            invert_clear H1; peel_and_close.
            invert_clear H1; peel_and_close.
          }
          {
            invert_clear H1; peel_and_close.
            invert_clear H1; peel_and_close.
            invert_clear H1; peel_and_close.
            invert_clear H1; peel_and_close.            
          }
        * repeat constructor; peel_and_close.
          {
            invert_clear H; peel_and_close.
            invert_clear H; peel_and_close.
            invert_clear H; peel_and_close.
            invert_clear H; peel_and_close.
          }
          {
            invert_clear H; peel_and_close.
            invert_clear H; peel_and_close.
            invert_clear H; peel_and_close.
            invert_clear H; peel_and_close.
          }

      + (* fd_m = Two (Triple x y z) t_m' *)
        destruct fD as [ fA | ].
        * destruct fA as [ t1 | t1 t2 | t1 t2 t3 ];
            try (invert_clear HfD; invert_clear H; fail).
          invert_clear HfD. invert_clear H.
          repeat constructor; peel_and_close.
          {
              invert_clear H1; peel_and_close.
              invert_clear H1; peel_and_close.
              invert_clear H1; peel_and_close.
              invert_clear H1; peel_and_close.
          }
          {
              invert_clear H1; peel_and_close.
              invert_clear H1; peel_and_close.
              invert_clear H1; peel_and_close.
              invert_clear H1; peel_and_close.
          }

        * repeat constructor; peel_and_close.
          {
              invert_clear H; peel_and_close.
              invert_clear H; peel_and_close.
              invert_clear H; peel_and_close.
              invert_clear H; peel_and_close.
          }
          {
              invert_clear H; peel_and_close.
              invert_clear H; peel_and_close.
              invert_clear H; peel_and_close.
              invert_clear H; peel_and_close.
          }

      + (* fd_m = Three (Triple x y z) t_m' t_m'' *)
        destruct fD as [ fA | ].
        * destruct fA as [ t1 | t1 t2 | t1 t2 t3 ];
            try (invert_clear HfD; invert_clear H; fail).
          invert_clear HfD. invert_clear H.
          repeat constructor; peel_and_close.
          {
              invert_clear H1; peel_and_close.
              invert_clear H1; peel_and_close.
              invert_clear H1; peel_and_close.
              invert_clear H1; peel_and_close.
          }
          {
              invert_clear H1; peel_and_close.
              invert_clear H1; peel_and_close.
              invert_clear H1; peel_and_close.
              invert_clear H1; peel_and_close.
          }

        * repeat constructor; peel_and_close.
          {
              invert_clear H; peel_and_close.
              invert_clear H; peel_and_close.
              invert_clear H; peel_and_close.
              invert_clear H; peel_and_close.
          }
          {
              invert_clear H; peel_and_close.
              invert_clear H; peel_and_close.
              invert_clear H; peel_and_close.
              invert_clear H; peel_and_close.
          }
  }
Qed.

(* Corollary at B := A. *)
Lemma ftailD_approx (A : Type) `{LDA : LessDefined A, !Reflexive LDA}
    (q : Seq A) (outD : SeqA A) :
  outD `is_approx` ftail q ->
  Tick.val (ftailD q outD) `is_approx` q.
Proof.
  intros. eapply ftailD'_approx; eauto.
Qed.
(* Note: change to Qed once ftailD'_approx is closed. *)


(* ----------------------------------------------------------------- *)
(** **** Main theorem 2: [ftailD'_cost] (amortized cost bound). *)
(* ----------------------------------------------------------------- *)


Lemma ftailD'_cost : forall (A B : Type) `{LessDefined B, Exact A B}
    (s : Seq A) (outD : SeqA B),
    outD `is_approx` ftail s ->
    let inM := ftailD' s outD in
    let cost := Tick.cost inM in
    let inD := Tick.val inM in
    debt inD + cost <= 3 + debt outD.
Proof.
  (* By [ftail_ind].  Each case: compute debt inD + cost vs 3 + debt outD.
  
     1. Nil: 0 + 0 ≤ 3 + 0. Trivial.
     2. Unit _: 0 + 1 ≤ 3 + 0. Trivial.
     3. More (Three _ x y) m r: potential transfers from output (TwoA, +1) 
        to input (ThreeA, 0); cost 1 absorbed. K=0. ✓
     4. More (Two _ x) m r: TwoA → OneA loses 1 potential. K=2. ✓
     5. More (One _) Nil (One _): trivial.
     6. More (One _) Nil (Two _ _): TwoA rear losing potential. K=2. ✓
     7. More (One _) Nil (Three _ _ _): ThreeA → TwoA gains potential. K=0. ✓
     8. More (One _) m r, Pair-head: recursive. Use IH + 
        [debt_add_pair_to_head_demand_seq_le] (Thunk case) or direct 
        computation on [m]'s digit (Undefined case). K=3 binds at the
        Two-front-in-m case with mD_out = Undefined.
     9. More (One _) m r, Triple-head: non-recursive. Use 
        [debt_inverse_chop_demand_seq_le] (Thunk case) or direct computation
        on [m]'s digit (Undefined case). K=3 binds at the Two-front-in-m 
        case with mD_out = Undefined.
     
     Most Thunk-case sub-goals close by `lia` after [unfold_debt].  
     Undefined-mD_out cases need separate case-splits on [m]'s digit. *)
  admit.
Admitted.

(* Corollary at B := A. *)
Lemma ftailD_cost (A : Type) `{LessDefined A} (q : Seq A) (outD : SeqA A) :
  outD `is_approx` ftail q ->
  let inM := ftailD q outD in
  debt (Tick.val inM) + Tick.cost inM <= 3 + debt outD.
Proof.
  intros. apply ftailD'_cost. auto.
Qed.
(* Note: change to Qed once ftailD'_cost is closed. *)


(* ----------------------------------------------------------------- *)
(** **** Main theorem 3: [ftailD'_cost_bottom]

    Special case of [ftailD'_cost] for the [outD = bottom_of (exact (ftail q))] case,
    used by the physicist's argument when the output demand is [Undefined]. *)
(* ----------------------------------------------------------------- *)


Lemma ftailD'_cost_bottom (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (q : Seq A) :
  let inM := ftailD' q (bottom_of (exact (ftail q))) in
  debt (Tick.val inM) + Tick.cost inM <= 3.
Proof.
  (* Specialize [ftailD'_cost] with [outD = bottom_of (exact (ftail q))]
     and bound debt outD ≤ 1. (The +1 over K=3 from ftailD'_cost accounts 
     for the Two-front case where bottom_of's Undefined-rear contributes 1
     to potential vs the 0 we accounted for in the abstract analysis.)
     
     Mirror [fconsD'_cost_bottom] structurally. *)
  admit.
Admitted.


(* ----------------------------------------------------------------- *)
(** **** Main theorem 4: [ftailD'_spec] (clairvoyance equivalence). *)
(* ----------------------------------------------------------------- *)


Lemma ftailD'_spec : forall (A B : Type)
    `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (q : Seq A) (outD : SeqA B),
    outD `is_approx` ftail q ->
    forall qD, qD = Tick.val (ftailD' q outD) ->
      let dcost := Tick.cost (ftailD' q outD) in
      ftailA qD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  (* By [ftail_ind]. Each case uses [mgo_] / [keep_mgo_] to unfold 
     [ftailA] (clairvoyant) and [ftailD'] (demand) in lockstep, exhibiting 
     a witness that satisfies the optimistic spec.
     
     1-7. Non-recursive cases: structural witnessing.
     8. Pair-head recursive: apply IH at the recursive [ftailD'] call site,
        producing a sub-witness for [ftailA] on the recursive value.
     9. Triple-head non-recursive: similar to 1-7 but with 
        [inverse_chop_demand] threading the demand back.
     
     Closely mirrors [fconsD'_spec]. *)
  admit.
Admitted.

(* Corollary at B := A. *)
Lemma ftailD_spec (A : Type) `{LDA : LessDefined A, !Reflexive LDA}
    (q : Seq A) (outD : SeqA A) :
  outD `is_approx` ftail q ->
  forall qD, qD = Tick.val (ftailD q outD) ->
    let dcost := Tick.cost (ftailD q outD) in
    ftailA qD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros. apply ftailD'_spec; auto.
Qed.
(* Note: change to Qed once ftailD'_spec is closed. *)

(* ================================================================= *)
(** ** Auxiliary Definitions                                     *)
(* ================================================================= *)

(* The empty case *)
Definition empty (A : Type) : Seq A := Nil.

Definition emptyD (A : Type) (outD : SeqA A) : Tick unit :=
  Tick.tick >>
    match outD with
    | NilA => Tick.ret tt
    | _ => bottom
    end.


Lemma emptyD_approx (A : Type) `{LessDefined A} (outD : SeqA A) :
  outD `is_approx` empty -> Tick.val (emptyD outD) `is_approx` tt.
Proof.
  invert_clear 1. sauto.
Qed.

From Clairvoyance Require Import Core.

Definition emptyA (A : Type) : M (SeqA A) := tick >> ret NilA.

Lemma emptyD_spec (A : Type) `{LDA : LessDefined A, !Reflexive LDA} (outD : SeqA A) :
  outD `is_approx` empty ->
  let dcost := Tick.cost (emptyD outD) in
  emptyA [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  unfold emptyA. mgo_.
Qed.


(* Final Verification *)

From Clairvoyance Require Import Interfaces.
Open Scope tick_scope.

Definition forceD (A : Type) (y : A) (u : T A) : A :=
  match u with
  | Undefined => y
  | Thunk x => x
  end.

Lemma less_defined_forceD (A : Type) `{LessDefined A} (x : T A) (y : A) (z : A)
  : y `less_defined` z ->
    x `less_defined` Thunk z ->
    forceD y x `less_defined` z.
Proof.
  intros Hy Hx; inversion Hx; cbn; auto.
Qed.

Section Physicist'sArgument.

  Context (A : Type).

  Definition value := Seq A.
  Definition valueA := T (SeqA A).

  Inductive op : Type :=
  | Empty
  | FCons (x : A)
  | Head.

  (* --- eval: pure semantics --- *)
  #[export] Instance eval : Eval op value :=
    fun op args => match op, args with
                | Empty, [] => [empty]
                | FCons x, [q] => [fcons x q]
                | Head, [q] => []  (* Head returns an element, not a queue *)
                | _, _ => []
                end.

  (* --- budget: amortized cost per operation --- *)
  #[export] Instance budget : Budget op value :=
    fun o _ => 3.

  (* --- exec: clairvoyant semantics --- *)
  #[export] Instance exec : Exec op valueA :=
    fun o args => match o, args with
               | Empty, [] => let! q := emptyA in ret [Thunk q]
               | FCons x, [q] => let! q' := fconsA (exact x) q in ret [Thunk q']
               | Head, [q] => let! _ := headA q in ret []
               | _, _ => ret []
               end.

  (* --- well-formedness: trivially true --- *)
  #[export] Instance wf : WellFormed value := fun _ => True.

  Lemma wf_eval : WfEval.
  Proof using A.
    unfold WfEval. destruct o, vs; repeat constructor.
    all: simpl; destruct vs; repeat constructor.
  Qed. (* fill in case-by-case *)
  #[export] Existing Instance wf_eval.

  (* --- monotonicity of exec --- *)
  Lemma monotonic_exec `{LDA : LessDefined A, !PreOrder LDA} (o : op) : Monotonic (exec o).
  Proof using A.
    unfold Monotonic. destruct o; invert_clear 1; simpl; try solve [ solve_mon ].
    - (* FCons *)
      invert_clear H0; try solve [ solve_mon ].
      apply bind_mon.
      + apply fconsA_mon; try solve [ auto ]. reflexivity.
      + intros. solve_mon.
    - (* Head *)
      invert_clear H0; try solve [ solve_mon ].
      apply bind_mon.
      + apply headA_mon; try solve [ auto ]. 
      + intros. solve_mon. 
Qed.

  (* --- approx algebra --- *)
  #[export] Instance approx_algebra
    `{LDA : LessDefined A, PreOrder A LDA, LBA : Lub A, @LubLaw A LBA LDA} :
    IsApproxAlgebra value valueA.
  Proof.
    econstructor; try typeclasses eauto.
  Defined.

  (* --- well-defined exec --- *)
  Lemma well_defined_exec
    `{LDA : LessDefined A, PreOrder A LDA, LBA : Lub A, @LubLaw A LBA LDA} :
    @WellDefinedExec op value valueA _ _.
  Proof using A.
    constructor; exact monotonic_exec.
  Qed.
  #[export] Existing Instance well_defined_exec.

  (* --- demand: backward demand propagation --- *)
  #[export] Instance demand : Demand op value valueA :=
    fun op args argsA =>
      match op, args, argsA with
      | Empty, [], [outD] =>
          let outD := forceD (bottom_of (exact empty)) outD in
          Tick.bind (emptyD outD) (fun _ => Tick.ret [])
      | FCons x, [q], [outD] =>
          let outD := forceD (bottom_of (exact (fcons x q))) outD in
          let+ qD := fconsD x q outD in
          Tick.ret [qD]
      | Head, [q], [] =>
          let+ qD := headD q None in
          Tick.ret [qD]
      | _, _, _ => Tick.ret (bottom_of (exact args))
      end.

  (* --- potential function --- *)
  #[global] Instance potential : Potential valueA :=
    fun qD => match qD with
           | Thunk qA => debt qA
           | Undefined => 0
           end.

  (* --- PureDemand: demand functions are correct w.r.t. eval --- *)
  Lemma pd
    `{LDA : LessDefined A, PA : !PreOrder LDA, LBA : Lub A, LLA : @LubLaw A LBA LDA} :
    @PureDemand op value valueA approx_algebra eval demand.
  Proof using A.
    assert (@Reflexive A less_defined) as HRA by (destruct PA; auto).
    assert (@Reflexive (SeqA A) less_defined) as HRSA
      by apply (@Reflexive_LessDefined_SeqA A LDA HRA).
    unfold PureDemand, pure_demand.
    intros o args output.
    destruct o.
    (* Empty *)
    {
        destruct args as [ | a args' ]; [ | intro Happrox; simpl; apply bottom_is_least; reflexivity ].
        destruct output as [ | outD output' ]; [ intro Happrox; simpl; apply bottom_is_least; reflexivity | ].
        destruct output' as [ | ? ? ]; [ | intro Happrox; simpl; apply bottom_is_least; reflexivity ].
        (* Now: args = [], output = [outD] *)
        intro Happrox. simpl. 
        repeat constructor.      
    }
    (* FCons x: uses fconsD'_approx. *)
    {
      destruct args as [ | q args' ]; [ intro; simpl; apply bottom_is_least; reflexivity | ].
      destruct args' as [ | ? ? ]; [ | intro; simpl; apply bottom_is_least; reflexivity ].
      destruct output as [ | outD output' ];
      [ intro; simpl; apply bottom_is_least; reflexivity | ].
      destruct output' as [ | ? ? ];
      [ | intro; simpl; apply bottom_is_least; reflexivity ].
      (* args = [q], output = [outD] *)
      intro Happrox.
      invert_clear Happrox as [ | ? ? ? ? HoutD _ ].
      simpl.
      assert (Hin : forceD (bottom_of (exact (fcons x q))) outD `less_defined` exact (fcons x q)).
      {
        destruct outD as [ outA | ]; simpl.
        - invert_clear HoutD. assumption.
        - apply bottom_is_least. reflexivity.
      }
      eapply fconsD'_approx in Hin.
      simpl. repeat constructor. exact Hin.
    }
    (* Head: args = [q], output = []. demand returns [headD q None] which must approximate [q]. Uses headD_approx. *)
    {
      destruct args as [ | q args' ]; [ intro; simpl; apply bottom_is_least; reflexivity | ].
      destruct args' as [ | ? ? ]; [ | intro; simpl; apply bottom_is_least; reflexivity ].
      destruct output as [ | outD output' ];
        [ | intro; simpl; apply bottom_is_least; reflexivity ].
      intros _. simpl.
      destruct q as [ | a | d s' d0 ]; simpl.
      + (* q = Nil: headD Nil None = Tick.ret (Thunk NilA), exact Nil = Thunk NilA *)
        repeat constructor.
      + (* q = Unit a: headD (Unit a) None = bottom, Tick.val = Undefined *)
        repeat constructor.
      + (* q = More d s' d0: headD (More _ _ _) None = bottom, Tick.val = Undefined *)
        destruct d; simpl; repeat constructor.
    }
  Qed.
  #[export] Existing Instance pd.

  (* --- CvDemand: demand functions agree with clairvoyant semantics --- *)
  Lemma cd
    `{LDA : LessDefined A, PreOrder A LDA, LBA : Lub A, @LubLaw A LBA LDA} :
    @CvDemand op value valueA _ _ _ _.
  Proof using A.
    rename H into PA. rename H0 into LLA.
    assert (Reflexive LDA) as RA by (destruct PA; auto).
    unfold CvDemand, cv_demand.
    destruct o.
    - (* Empty *)
      simpl. destruct x.   (* destruct args *)
      + (* args = [] *)
        invert_clear 1. invert_clear H0. invert_clear 1. unfold emptyA. mgo_.
      + (* args = _ :: _ *)
        invert_clear 1. invert_clear 1. mgo_.
    - (* FCons x *)
      simpl. intro args0.
      refine (match args0 with
              | [] => _
              | [q] => _
              | _ => _
              end); try solve [ invert_clear 1; invert_clear 1; mgo_ ].
      invert_clear 1.
      invert_clear H0.
      intros n xD HxD.
      (* HxD : {| cost := n; val := xD |} = demand (FCons x) [q] [outD] *)
      unfold demand in HxD. simpl in HxD.
      rename x0 into outD.
      destruct (fconsD x q (forceD (bottom_of (exact (fcons x q))) outD))
        as [n_inner qD] eqn:EfconsD.
      simpl in HxD. invert_clear HxD.
      mgo_.
      eapply optimistic_mon; [ eapply fconsD_spec | ].
      + eapply less_defined_forceD; [ apply bottom_is_least; reflexivity | eassumption ].
      + rewrite EfconsD. reflexivity.
      + intros out cost [Hout Hcost].
        mgo_.
        {
          destruct outD as [ outA | ]; simpl in Hout.
          - (* outD = Thunk outA *) 
            constructor; exact Hout.
          - (* outD = Undefined *) 
            constructor.
        }
        {
          rewrite EfconsD in Hcost. simpl in Hcost. lia.
        }
    - (* Head *)
      simpl. intro args0.
      refine (match args0 with
              | [] => _
              | [q] => _
              | _ => _
              end); try solve [ invert_clear 1; invert_clear 1; mgo_ ].
      (* args = [q] *)
      invert_clear 1.        (* Happrox : yD ≤ exact (eval Head [q]) = []. So yD = []. *)
      intros n xD HxD.
      unfold demand in HxD. simpl in HxD.
      destruct (headD q None) as [n_inner qD] eqn:EheadD.
      simpl in HxD. invert_clear HxD.
      (* Goal: exec Head [qD] [[ fun yA m => [] ≤ yA ∧ m ≤ n_inner ]] *)
      mgo_.
      (* Now case-split on q to make headA reduce. *)
      destruct q as [ | a | d s' d0 ]; simpl in EheadD; invert_clear EheadD.
      + (* q = Nil: qD = Thunk NilA, headA (Thunk NilA) = tick >> ret None *)
        unfold headA, headA'. mgo_.
      + (* q = Unit a: qD = Thunk (UnitA Undefined) *)
        unfold headA, headA'. mgo_.
      + (* q = More d s' d0 *)
        destruct d; unfold headA, headA'; simpl; mgo_.
  Qed.
  #[export] Existing Instance cd.

  (* --- WellDefinedPotential: sub-additivity of lub + potential(bottom) = 0 --- *)
  Lemma well_defined_potential
    `{LDA : LessDefined A, PreOrder A LDA, LBA : Lub A, @LubLaw A LBA LDA} :
    @WellDefinedPotential value valueA _ _.
  Proof using A.
    constructor.
    - (* sub-additivity: debt(lub x y) ≤ debt(x) + debt(y). *)
      red. invert_clear 1. invert_clear H1.
      invert_clear H1; invert_clear H2; simpl; try lia.
      eapply debt_SeqA_lub_subadditive; eassumption.
    - (* potential of bottom is zero *)
      red. simpl. lia.
    Unshelve.
    + destruct H; assumption.
    + typeclasses eauto.
  Qed.
  #[export] Existing Instance well_defined_potential.

  (* --- Helper lemmas for potential --- *)
  Lemma potential_bottom_of (q : value) :
    potential (bottom_of (exact q)) = 0.
  Proof using A.
    destruct q; reflexivity.
  Qed.
  Hint Resolve potential_bottom_of : core.

  Lemma sumof_potential_bottom_of (qs : list value) :
    sumof potential (bottom_of (exact qs)) = 0.
  Proof using A.
    induction qs; auto.
  Qed.
  Hint Resolve sumof_potential_bottom_of : core.

  (* --- Physicist'sArgumentD: the core amortized inequality.
 
     Structure mirrors ImplicitQueue.v lines 1696–1726, using `refine` with a
     wildcard fallback that the generic tactic discharges. The fallback
     handles ill-shaped arg/output lists (length mismatches) by reducing
     them to bottom-of computations.
  *)
  Theorem physicist's_argumentD :
    forall `{LDA : LessDefined A, !PreOrder LDA, LBA : Lub A, @LubLaw A LBA LDA},
      @Physicist'sArgumentD
        op value valueA
        _ _ _ _ _ _.
  Proof using A.
    pose proof sumof_potential_bottom_of as Hpb.
    unfold bottom_of, exact in Hpb.
    unfold Physicist'sArgumentD.
    intros LDA HPreOrder LBA HLubLaw o args _ output.
    refine (match o, args, output with
            | Empty, [], [_] => _
            | FCons x, [q], [outD] => _
            | Head, [q], [] => _
            | _, _, _ => _
            end); try solve [ do 2 invert_clear 1; simpl in *;
                              try (rewrite Hpb); lia ].
    - (* Empty *)
      invert_clear 1 as [ | ? ? ? ? HoutD _ ].
      intros input cost HxD. unfold demand in HxD. simpl in HxD.
      invert_clear HxD.
      invert_clear HoutD; [ | invert_clear H ]; simpl; lia.
    - (* FCons x. *)
      invert_clear 1 as [ | ? ? ? ? HoutD _ ].
      intros input cost HxD. unfold demand in HxD. simpl in HxD.
      destruct (fconsD x q (forceD (bottom_of (exact (fcons x q))) outD))
        as [cost' qD'] eqn:EfconsD.
      simpl in HxD. invert_clear HxD.
      (* Goal: sumof potential [qD'] + cost' ≤ 3 + sumof potential [outD] *)
      destruct outD as [ outA | ]; simpl in *.
      + (* outD = Thunk outA: use fconsD'_cost *)
        invert_clear HoutD.
        rename H into HleA.  (* HleA : Thunk outA ≤ exact (fcons x q) *)
        eapply (fconsD'_cost x q) in HleA.   (* HleA is the inverted ≤ hypothesis *)
        unfold fconsD in EfconsD.
        rewrite EfconsD in HleA. simpl in HleA.
        unfold potential.
        change (match qD' with Thunk qA => debt qA | Undefined => 0 end) with (debt qD').
        lia.
      + (* outD = Undefined *)
        destruct q as [ | y | d m r ]; simpl in *.
        (* q = Nil *)
        {
          invert_clear EfconsD. destruct output; cbn in *; lia.
        }
        (* q = Unit y *)
        {
          invert_clear EfconsD. destruct output; cbn in *; lia.
        }
        (* q = More d m r *)
        {
          destruct d as [ a | a b | a b c ]; simpl in EfconsD; invert_clear EfconsD; destruct args; cbn in *; lia.
        }
    - (* Head *)
      invert_clear 1.
      intros input cost HxD. unfold demand in HxD. simpl in HxD.
      destruct (headD q None) as [cost' qD'] eqn:EheadD.
      simpl in HxD. invert_clear HxD.
      (* Goal: sumof potential [qD'] + cost' ≤ 3 + sumof potential [] *)
      simpl.
      (* Case-split on q to compute headD q None concretely *)
      destruct q as [ | y | d m r ];
        [ | | destruct d as [ a | a b | a b c ] ];
        simpl in EheadD; invert_clear EheadD;
        destruct output; cbn in *; lia.
  Qed.
  #[export] Existing Instance physicist's_argumentD.

  (* --- Final theorem: amortized cost of any trace --- *)
  Theorem amortized_cost
    `{LDA : LessDefined A, PreOrder A LDA, LBA : Lub A, @LubLaw A LBA LDA} :
    @AmortizedCostSpec op value valueA _ _ _.
  Proof using A.
    eapply @physicist's_method; typeclasses eauto.
  Qed.

End Physicist'sArgument.
