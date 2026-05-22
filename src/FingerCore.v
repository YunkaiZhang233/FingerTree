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

