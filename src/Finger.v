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
      apply optimistic_thunk_go. mgo_.
      admit.
    }
  }

Admitted.

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

(** *** snoc — insert at the rear

    Symmetric to [cons].  Overflow on the rear digit [Three a b c]
    bundles [a] and [b] into [Pair a b] and snocs it into the middle,
    keeping [Two c x] as the new rear. *)

Fixpoint snoc {A : Type} (s : Seq A) (x : A) : Seq A :=
  match s with
  | Nil              => Unit x
  | Unit y           => More (One y) Nil (One x)
  | More f m (One a)       => More f m (Two a x)
  | More f m (Two a b)     => More f m (Three a b x)
  | More f m (Three a b c) => More f (snoc m (Pair a b)) (Two c x)
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

(** *** Non-recursive spine helpers

    These four O(1) functions enable [uncons]/[unsnoc] to avoid a
    recursive spine removal when the head (or last) tuple is a [Triple].

    [chop] / [chopLast] trim a [Triple] to a [Pair] by dropping the
    first or last element respectively.  They are only ever called on
    [Triple]s; the [Pair] branch is unreachable but needed for totality.

    [map1] / [mapLast] apply [f] to only the first (or last) element of
    a [Seq], without touching the spine.  They are O(1) because they
    match only the outermost constructor. *)

Definition chop {A : Type} (t : Tuple A) : Tuple A :=
  match t with
  | Triple _ y z => Pair y z
  | p            => p
  end.

Definition chopLast {A : Type} (t : Tuple A) : Tuple A :=
  match t with
  | Triple a b _ => Pair a b
  | p            => p
  end.

Definition map1 {A : Type} (f : A -> A) (s : Seq A) : Seq A :=
  match s with
  | Nil                    => Nil
  | Unit x                 => Unit (f x)
  | More (One x) q u       => More (One (f x)) q u
  | More (Two x y) q u     => More (Two (f x) y) q u
  | More (Three x y z) q u => More (Three (f x) y z) q u
  end.

Definition mapLast {A : Type} (f : A -> A) (s : Seq A) : Seq A :=
  match s with
  | Nil                    => Nil
  | Unit x                 => Unit (f x)
  | More u q (One x)       => More u q (One (f x))
  | More u q (Two x y)     => More u q (Two x (f y))
  | More u q (Three x y z) => More u q (Three x y (f z))
  end.

(** *** uncons — remove from the front (Claessen's [tail] + [more0])

    [Three] / [Two]: shrink the front digit directly.  O(1).
    [One]: front empties; refill from the spine via three sub-cases.

    Sub-cases when spine is non-empty (paper's [more0]):
      - Head is [Pair a b]:     install [Two a b] (safe) as new front;
          remove the pair by recursing into the spine.
      - Head is [Triple a _ _]: install [One a] (dangerous) as new front;
          transform the Triple to a Pair in-place with [map1 chop].
          No recursive removal — O(1) for this case.

    The [Pair] case is the only recursion.  The [Triple] case is O(1)
    because [map1] never enters the spine. *)

Fixpoint uncons {A : Type} (s : Seq A) : option (A * Seq A) :=
  match s with
  | Nil => None
  | Unit x => Some (x, Nil)
  | More (Three x a b) m r => Some (x, More (Two a b) m r)
  | More (Two x a) m r     => Some (x, More (One a) m r)
  | More (One x) m r =>
      match head m with
      | None =>
          match r with
          | One a       => Some (x, Unit a)
          | Two a b     => Some (x, More (One a) Nil (One b))
          | Three a b c => Some (x, More (One a) Nil (Two b c))
          end
      | Some (Pair a b) =>
          match uncons m with
          | Some (_, m') => Some (x, More (Two a b) m' r)
          | None         => None
          end
      | Some (Triple a _ _) =>
          Some (x, More (One a) (map1 chop m) r)
      end
  end.

(** *** unsnoc — remove from the rear (symmetric to [uncons])

    Sub-cases when spine is non-empty:
      - Last is [Pair a b]:     install [Two a b] (safe) as new rear;
          remove by recursing.
      - Last is [Triple _ _ c]: install [One c] (dangerous) as new rear;
          transform the Triple to a Pair in-place with [mapLast chopLast]. *)

Fixpoint unsnoc {A : Type} (s : Seq A) : option (Seq A * A) :=
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
          | None         => None
          end
      | Some (Triple _ _ c) =>
          Some (More f (mapLast chopLast m) (One c), x)
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
(** ** Section 3: Demand Functions                                     *)
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

(** *** map1D' — demand back-propagation through [map1 chop]

    [map1 chop m] applies [chop] to the first element of [m]'s front digit.
    [chop (Triple _ b c) = Pair b c] (drops first slot) and
    [chop (Pair a b) = Pair a b] (identity).

    Given output demand [mD] on [map1 chop m], [map1D' m mD] returns the
    corresponding demand on [m].  For a [Triple] front element, a demand
    [PairA bD cD] on the [chop] result becomes [TripleA Undefined bD cD]
    on the original triple (the dropped slot is not needed).
    For a [Pair] front element, the demand passes through unchanged. *)

(* Definition map1D' {A A : Type} (m : Seq (Tuple A)) (mD : T (SeqA (TupleA A)))
    : T (SeqA (TupleA A)) :=
  let chop_back (t : Tuple A) (tD : T (TupleA A)) : T (TupleA A) :=
    match t with
    | Triple _ _ _ => match tD with
                      | Thunk (PairA xD yD) => Thunk (TripleA Undefined xD yD)
                      | _                   => Undefined
                      end
    | Pair _ _     => tD
    end in
  let front_back (t : Tuple A) (fD : T (DigitA (TupleA A))) : T (DigitA (TupleA A)) :=
    match fD with
    | Thunk (OneA tD)           => Thunk (OneA   (chop_back t tD))
    | Thunk (TwoA tD rest)      => Thunk (TwoA   (chop_back t tD) rest)
    | Thunk (ThreeA tD r1 r2)   => Thunk (ThreeA (chop_back t tD) r1 r2)
    | _                         => fD
    end in
  match mD with
  | Undefined => Undefined
  | Thunk mDA =>
      Thunk (match m, mDA with
             | Nil,                _              => mDA
             | Unit t,             UnitA tD       => UnitA (chop_back t tD)
             | More (One t) _ _,   MoreA fD sp rD => MoreA (front_back t fD) sp rD
             | More (Two t _) _ _, MoreA fD sp rD => MoreA (front_back t fD) sp rD
             | More (Three t _ _) _ _, MoreA fD sp rD =>
                 MoreA (front_back t fD) sp rD
             | _,                  _              => mDA
             end)
  end.

(** *** mapLastD' — demand back-propagation through [mapLast chopLast]

    Symmetric to [map1D'].  [chopLast (Triple a b _) = Pair a b] drops the
    last slot; [chopLast (Pair a b) = Pair a b] is the identity.
    A demand [PairA aD bD] on the [chopLast] result becomes
    [TripleA aD bD Undefined] on the original triple. *)

Definition mapLastD' {A B : Type} (m : Seq (Tuple A)) (mD : T (SeqA (TupleA B)))
    : T (SeqA (TupleA B)) :=
  let chopLast_back (t : Tuple A) (tD : T (TupleA B)) : T (TupleA B) :=
    match t with
    | Triple _ _ _ => match tD with
                      | Thunk (PairA xD yD) => Thunk (TripleA xD yD Undefined)
                      | _                   => Undefined
                      end
    | Pair _ _     => tD
    end in
  let rear_back (t : Tuple A) (rD : T (DigitA (TupleA B))) : T (DigitA (TupleA B)) :=
    match rD with
    | Thunk (OneA tD)         => Thunk (OneA   (chopLast_back t tD))
    | Thunk (TwoA r1 tD)      => Thunk (TwoA   r1 (chopLast_back t tD))
    | Thunk (ThreeA r1 r2 tD) => Thunk (ThreeA r1 r2 (chopLast_back t tD))
    | _                       => rD
    end in
  match mD with
  | Undefined => Undefined
  | Thunk mDA =>
      Thunk (match m, mDA with
             | Nil,                    _              => mDA
             | Unit t,                 UnitA tD       => UnitA (chopLast_back t tD)
             | More _ _ (One t),       MoreA fD sp rD => MoreA fD sp (rear_back t rD)
             | More _ _ (Two _ t),     MoreA fD sp rD => MoreA fD sp (rear_back t rD)
             | More _ _ (Three _ _ t), MoreA fD sp rD => MoreA fD sp (rear_back t rD)
             | _,                      _              => mDA
             end)
  end.

(** *** consD' — demand function for [cons x s]

    Mirrors [cons] case by case, back-propagating the output demand [outD]
    on [cons x s] to produce the demanded approximation of [s].
    The element [x] is always demanded exactly: [exact x].

    The cascade case [More (Three a b c) m r] is the only recursive one:
    [cons (Pair b c) m] is demanded via [thunkD], and the resulting demand
    on [Pair b c] supplies [bD] and [cD] for the returned [ThreeA aD bD cD].

    Follows [pushD'] in ImplicitQueue.v; the extra cases are [Two] / [Three]
    front digits, which are non-recursive (no cascade). *)

Fixpoint consD' (A B : Type) `{Exact A B} (x : A) (s : Seq A) (outD : SeqA B) :
    Tick (T (SeqA B)) :=
  Tick.tick >>
  match s with
  | Nil =>
      Tick.ret (Thunk NilA)
  | Unit y =>
      let yD :=
        match outD with
        | MoreA _ _ (Thunk (OneA yD)) => yD
        | _                           => bottom
        end in
      Tick.ret (Thunk (UnitA yD))
  | More (One a) m r =>
      let '(aD, mD, rD) :=
        match outD with
        | MoreA (Thunk (TwoA _ aD)) mD rD => (aD, mD, rD)
        | _                               => bottom
        end in
      Tick.ret (Thunk (MoreA (Thunk (OneA aD)) mD rD))
  | More (Two a b) m r =>
      let '(aD, bD, mD, rD) :=
        match outD with
        | MoreA (Thunk (ThreeA _ aD bD)) mD rD => (aD, bD, mD, rD)
        | _                                    => bottom
        end in
      Tick.ret (Thunk (MoreA (Thunk (TwoA aD bD)) mD rD))
  | More (Three a b c) m r =>
      let '(aD, mD, rD) :=
        match outD with
        | MoreA (Thunk (TwoA _ aD)) mD rD => (aD, mD, rD)
        | _                               => bottom
        end in
      let+ mD_in := thunkD (consD' (Pair b c) m) mD in
      Tick.ret (Thunk (MoreA (Thunk (ThreeA aD (exact b) (exact c))) mD_in rD))
  end.

Definition consD (A : Type) : A -> Seq A -> SeqA A -> Tick (T (SeqA A)) :=
  consD'.
 *)


(* Final Verification *)

From Coq Require Import List.
Import ListNotations.
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
  | Cons (x : A)
  | Tail.

  #[export] Instance eval : Eval op value :=
    fun op args => match op, args with
                | Empty, [] => [empty]
                | Cons x, [q] => [fcons x q]
                (* | Tail, [q] => match tail q with
                             | Some q' => [q']
                             | _ => []
                             end *)
                | Tail, [q] => [] (* PlaceHolder *)
                | _, _ => []
                end.
  
  (* TODO: Change amount of operational budget!! *)
  #[export] Instance budget : Budget op value :=
    fun _ _ => 3.
  
  #[export] Instance exec : Exec op valueA :=
    fun o args => match o, args with
               | Empty, [] => let! q := emptyA in ret [Thunk q]
               | Cons x, [q] => let! q' := consA q (Thunk x) in ret [Thunk q']
               (* | Tail, [q] => let! p := tailA q in
                            match p with
                            | Some (Thunk (pairA x q)) => ret [q]
                            | Some Undefined => ret [Undefined]
                            | _ => ret []
                            end *)
               | Tail, [q] => ret [] (* PlaceHolder *)
               | _, _ => ret []
               end.
End Physicist'sArgument.
