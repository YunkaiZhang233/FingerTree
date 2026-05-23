(** * FingerConcat — Claessen's [glue] / concatenation operation

    This file implements the worst-case [O(log min(n1, n2))] concatenation
    operation for the simplified finger tree following Claessen 2020 §7.

    Unlike [fcons]/[fsnoc]/[ftail] (which are amortized constant), [glue]
    is **worst-case** logarithmic.  No new debit machinery is needed:
    [Debitable_T], [Debitable_SeqA], [safe_DigitA], [safe_T], and their
    sub-additivity lemmas are imported from [FingerCore.v].

    Structure (mirrors the cons/snoc/tail files where possible):
      Section 1: Pure helpers ([depth], [toTuples]).
      Section 2: Pure [glue] function + custom induction principle.
      Section 3: Clairvoyant version [glueA'] + monotonicity.
      Section 4: Demand function [glueD'] + [glueD'_approx].
      Section 5: Spec [glueD'_spec] and cost [glueD'_cost] lemmas.

    See [finger_concat_plan.md] for the implementation plan. *)

From Coq Require Import Arith Psatz Relations RelationClasses List.
From Clairvoyance Require Import Core Approx ApproxM Tick Prod Option.
From Hammer Require Import Tactics.
From Clairvoyance Require Import FingerCore FingerCons FingerSnoc.

Import ListNotations.
Import Tick.Notations.
Open Scope tick_scope.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

#[local] Existing Instance Exact_id | 1.



(* ================================================================= *)
(** ** Section 1: Pure helpers                                         *)
(* ================================================================= *)

(** *** [depth]: structural depth of a sequence's spine. *)
Fixpoint depth {A : Type} (s : Seq A) : nat :=
  match s with
  | Nil        => 0
  | Unit _     => 0
  | More _ m _ => S (depth m)
  end.

(** *** [digitToList]: convert a [Digit A] to a list of 1..3 elements.

    Note: [FingerCore.v] may already define this under [toListWith] or
    similar.  If so, use that instead and delete this. *)
Definition digitToList {A : Type} (d : Digit A) : list A :=
  match d with
  | One   x     => [x]
  | Two   x y   => [x; y]
  | Three x y z => [x; y; z]
  end.

(** *** [toTuples]: convert a list of size 2..9 to a list of 1..3 [Tuple]s.

    Following Claessen 2020 §7.  The function is partial on size 1 input
    (see footnote 2 of the paper); we return [[]] in that case as a
    fallback, but [glue] is designed never to call it on size-1 inputs.

    Sizes:  2 → 1,  3 → 1,  4 → 2,  5 → 2,  6 → 2,  7 → 3,  8 → 3,  9 → 3.  *)
Fixpoint toTuples {A : Type} (xs : list A) : list (Tuple A) :=
  match xs with
  | []            => []
  | [x; y]        => [Pair x y]
  | [x; y; z; w]  => [Pair x y; Pair z w]
  | x :: y :: z :: rest => Triple x y z :: toTuples rest
  | _             => []   (* unreachable on size 2..9 *)
  end.


(* ================================================================= *)
(** ** Section 2: Pure [glue] function                                 *)
(* ================================================================= *)

(** *** [glue]: generalized concatenation with a middle list of size 0..3.

    Follows Claessen 2020 §7 (Try 4, adapted for Try 5 sizes in §8).

    Five cases:
    - [Nil, _, q2]: prepend all of [as_] onto [q2] via [fcons].
    - [q1, _, Nil]: append all of [as_] onto [q1] via [fsnoc].
    - [Unit x, _, q2]: add [x] to the front of [as_], then prepend.
    - [q1, _, Unit y]: add [y] to the back of [as_], then append.
    - [More u1 m1 v1, _, More u2 m2 v2]: the deep case.  Bundle
      [digitToList v1 ++ as_ ++ digitToList u2] (size 2..9) into 1..3
      Tuples via [toTuples], then recurse on [(m1, tuples, m2)] one
      level deeper.

    Termination: recurses on [m1] which is structurally smaller than
    [More u1 m1 v1].  Uses [{struct s1}] annotation. *)
Fixpoint glue {A : Type} (s1 : Seq A) (as_ : list A) (s2 : Seq A) {struct s1} : Seq A :=
  match s1, s2 with
  | Nil, _              => List.fold_right fcons s2 as_
  | _, Nil              => List.fold_left fsnoc as_ s1
  | Unit x, _           => List.fold_right fcons s2 (x :: as_)
  | _, Unit y           => List.fold_left fsnoc (as_ ++ [y]) s1
  | More u1 m1 v1, More u2 m2 v2 =>
      More u1
        (glue m1 (toTuples (digitToList v1 ++ as_ ++ digitToList u2)) m2)
        v2
  end.

(** Top-level concat: glue with empty middle. *)
Definition concat {A : Type} (s1 s2 : Seq A) : Seq A := glue s1 [] s2.


(** *** Custom induction principle for [glue].

    Exposes the 5 case shapes.  The recursive case provides an IH
    at the deeper [Tuple A] level. *)
Lemma glue_ind :
  forall (P : forall (A : Type), Seq A -> list A -> Seq A -> Seq A -> Prop),
    (* Case 1: Nil, _, _ — covers all s2 *)
    (forall A (as_ : list A) (s2 : Seq A),
        P A Nil as_ s2 (List.fold_right fcons s2 as_)) ->
    (* Case 2: Unit x, _, Nil *)
    (forall A (x : A) (as_ : list A),
        P A (Unit x) as_ Nil (List.fold_left fsnoc as_ (Unit x))) ->
    (* Case 3: More u m v, _, Nil *)
    (forall A (u : Digit A) (m : Seq (Tuple A)) (v : Digit A) (as_ : list A),
        P A (More u m v) as_ Nil
          (List.fold_left fsnoc as_ (More u m v))) ->
    (* Case 4: Unit x, _, s2 (s2 non-Nil; merges Unit-Unit and Unit-More) *)
    (forall A (x : A) (as_ : list A) (s2 : Seq A),
        s2 <> Nil ->
        P A (Unit x) as_ s2
          (List.fold_right fcons s2 (x :: as_))) ->
    (* Case 5: More u1 m1 v1, _, Unit y *)
    (forall A (u1 : Digit A) (m1 : Seq (Tuple A)) (v1 : Digit A)
            (as_ : list A) (y : A),
        P A (More u1 m1 v1) as_ (Unit y)
          (List.fold_left fsnoc (as_ ++ [y]) (More u1 m1 v1))) ->
    (* Case 6: More-More, deep recursion *)
    (forall A (u1 : Digit A) (m1 : Seq (Tuple A)) (v1 : Digit A)
            (as_ : list A)
            (u2 : Digit A) (m2 : Seq (Tuple A)) (v2 : Digit A),
        P (Tuple A) m1
          (toTuples (digitToList v1 ++ as_ ++ digitToList u2))
          m2
          (glue m1 (toTuples (digitToList v1 ++ as_ ++ digitToList u2)) m2) ->
        P A (More u1 m1 v1) as_ (More u2 m2 v2)
          (More u1
            (glue m1 (toTuples (digitToList v1 ++ as_ ++ digitToList u2)) m2)
            v2)) ->
    forall A (s1 : Seq A) (as_ : list A) (s2 : Seq A),
      P A s1 as_ s2 (glue s1 as_ s2).
Proof.
  intros ? H1 H2 H3 H4 H5 H6.
  fix SELF 2.
  intros A s1.
  refine (
    match s1 as s1'
      return forall as_ s2, P A s1' as_ s2 (glue s1' as_ s2)
    with
    | Nil           => fun as_ s2 => _
    | Unit x        => fun as_ s2 => _
    | More u1 m1 v1 => fun as_ s2 => _
    end).
  - (* s1 = Nil. glue Nil as_ s2 = fold_right fcons s2 as_. *)
    simpl. apply H1.
  - (* s1 = Unit x. *)
    refine (
      match s2 as s2'
        return P A (Unit x) as_ s2' (glue (Unit x) as_ s2')
      with
      | Nil           => _
      | Unit y        => _
      | More u m v    => _
      end).
    + (* s2 = Nil. glue (Unit x) as_ Nil = fold_left fsnoc as_ (Unit x). *)
      simpl. apply H2.
    + (* s2 = Unit y. glue (Unit x) as_ (Unit y) goes through Case 3 in body:
         "Unit x, _" clause = fold_right fcons (Unit y) (x :: as_). *)
      simpl. apply H4. discriminate.
    + (* s2 = More u m v. glue (Unit x) as_ (More u m v) goes through
         "Unit x, _" clause = fold_right fcons (More u m v) (x :: as_). *)
      simpl. apply H4. discriminate.
  - (* s1 = More u1 m1 v1. *)
    refine (
      match s2 as s2'
        return P A (More u1 m1 v1) as_ s2' (glue (More u1 m1 v1) as_ s2')
      with
      | Nil           => _
      | Unit y        => _
      | More u2 m2 v2 => _
      end).
    + (* s2 = Nil. glue (More u1 m1 v1) as_ Nil = fold_left fsnoc as_ (More u1 m1 v1). *)
      simpl. apply H3.
    + (* s2 = Unit y. *)
      simpl. apply H5.
    + (* s2 = More u2 m2 v2. *)
      simpl. apply H6. apply SELF.
Qed.

(* NOTE: glue_ind above is sketched — depending on how Coq's pattern matching
   reduces glue, the actual induction principle may need different
   preconditions or a different structure.  Refine when proving glueD'_approx. *)


(* ================================================================= *)
(** ** Section 3: Clairvoyant version [glueA']                         *)
(* ================================================================= *)

(** *** Helper: convert a [DigitA A] to a list of [T A] (1..3 elements). *)
Definition digitToListA {A : Type} (d : DigitA A) : list (T A) :=
  match d with
  | OneA   x     => [x]
  | TwoA   x y   => [x; y]
  | ThreeA x y z => [x; y; z]
  end.

(** *** Helper: convert a list of [T A] (size 2..9) to a list of [T (TupleA A)] (size 1..3). *)
Fixpoint toTuplesA {A : Type} (xs : list (T A)) : list (T (TupleA A)) :=
  match xs with
  | []            => []
  | [x; y]        => [Thunk (PairA x y)]
  | [x; y; z; w]  => [Thunk (PairA x y); Thunk (PairA z w)]
  | x :: y :: z :: rest => Thunk (TripleA x y z) :: toTuplesA rest
  | _             => []
  end.
Arguments toTuplesA : simpl nomatch.

From Clairvoyance Require Import Core.

(** *** Clairvoyant glue. *)
Fixpoint glueA' (A : Type) (q1 : SeqA A) (as_ : list (T A)) (q2 : SeqA A) {struct q1} : M (SeqA A) :=
  tick >>
  (match q1, q2 with
   | NilA, _ =>
       (* foldr fconsA q2 as_ — fold the list into q2 from the right *)
       List.fold_right
         (fun x acc => let! q := acc in fconsA x (Thunk q))
         (ret q2) as_
   | _, NilA =>
       (* foldl fsnocA q1 as_ — fold the list into q1 from the left *)
       List.fold_left
         (fun acc x => let! q := acc in fsnocA (Thunk q) x)
         as_ (ret q1)
   | UnitA x, _ =>
       (* foldr fconsA q2 (x :: as_) *)
       List.fold_right
         (fun x acc => let! q := acc in fconsA x (Thunk q))
         (ret q2) (x :: as_)
   | _, UnitA y =>
       (* foldl fsnocA q1 (as_ ++ [y]) *)
       List.fold_left
         (fun acc x => let! q := acc in fsnocA (Thunk q) x)
         (as_ ++ [y]) (ret q1)
   | MoreA fD1 mD1 rD1, MoreA fD2 mD2 rD2 =>
       let! v1 := force rD1 in
       let! u2 := force fD2 in
       let middle := digitToListA v1 ++ as_ ++ digitToListA u2 in
       let tuples := toTuplesA middle in
       let~ m' := forcing mD1 (fun m1' =>
                  forcing mD2 (fun m2' => glueA' m1' tuples m2')) in
       ret (MoreA fD1 m' rD2)
   end).

(** Top-level wrapper: forces both arguments then dispatches. *)
Definition glueA (A : Type) (q1 : T (SeqA A)) (as_ : list (T A)) (q2 : T (SeqA A)) : M (SeqA A) :=
  forcing q1 (fun q1 => forcing q2 (fun q2 => glueA' q1 as_ q2)).

(* 
==============
Some Helper Functions
==============
*)

(** Helper for the base cases: folding fconsA over a list is monotone. *)
Lemma fold_fconsA_mon (A : Type) `{LDA : LessDefined A, PreOrder A LDA}
    (as'_ as_ : list (T A)) (m'_acc m_acc : M (SeqA A)) :
    Forall2 less_defined as'_ as_ ->
    m'_acc `less_defined` m_acc ->
    List.fold_right (fun x acc => let! q := acc in fconsA x (Thunk q)) m'_acc as'_
    `less_defined`
    List.fold_right (fun x acc => let! q := acc in fconsA x (Thunk q)) m_acc as_.
Proof.
  intro Hforall. induction Hforall as [| x' x as'_ as_ Hx Has IH]; intros Hacc.
  - (* nil *) simpl. exact Hacc.
  - (* cons *) 
    Local Opaque fconsA. 
    simpl.
    apply bind_mon.
    + apply IH. exact Hacc.
    + intros q' q Hq.
      apply fconsA_mon; [exact Hx | apply LessDefined_Thunk; exact Hq].
    Local Transparent fconsA.
Qed.

Lemma fold_fsnocA_mon (A : Type) `{LDA : LessDefined A, PreOrder A LDA}
    (as'_ as_ : list (T A)) (m'_acc m_acc : M (SeqA A)) :
    Forall2 less_defined as'_ as_ ->
    m'_acc `less_defined` m_acc ->
    List.fold_left (fun acc x => let! q := acc in fsnocA (Thunk q) x) as'_ m'_acc
    `less_defined`
    List.fold_left (fun acc x => let! q := acc in fsnocA (Thunk q) x) as_ m_acc.
Proof.
  intros Hforall. revert m'_acc m_acc.
  induction Hforall as [| x' x as'_ as_ Hx Has IH]; intros m'_acc m_acc Hacc.
  - simpl. exact Hacc.
  - Local Opaque fsnocA.
    simpl. apply IH.
    apply bind_mon; [exact Hacc | ].
    intros q' q Hq.
    apply fsnocA_mon; [exact Hx |apply LessDefined_Thunk; exact Hq].
    Local Transparent fsnocA.
Qed.

Lemma toTuplesA_mon (A : Type) `{LDA : LessDefined A}
    (xs' xs : list (T A)) :
    Forall2 less_defined xs' xs ->
    Forall2 less_defined (toTuplesA xs') (toTuplesA xs).
Proof.
  intro H. 
  (* Strong induction on the length of xs *)
  remember (length xs') as n.
  revert xs' xs H Heqn.
  induction n as [n IH] using lt_wf_ind.
  intros xs' xs H Hn.
  destruct H as [| x' x xs1' xs1 Hx Hxs1].
  - (* both empty *) simpl. constructor.
  - (* both have ≥ 1 *)
    destruct Hxs1 as [| y' y xs2' xs2 Hy Hxs2].
    + (* size 1: xs' = [x'], xs = [x]. toTuplesA returns []. *)
      simpl. constructor.
    + (* size ≥ 2 *)
      destruct Hxs2 as [| z' z xs3' xs3 Hz Hxs3].
      * (* size 2 *)
        simpl. constructor; [constructor; constructor; assumption | constructor].
      * (* size ≥ 3 *)
        destruct Hxs3 as [| w' w xs4' xs4 Hw Hxs4].
        -- (* size 3 *)
           simpl. constructor; [constructor; constructor; assumption | constructor].
        -- (* size ≥ 4 *)
           destruct Hxs4 as [| v' v xs5' xs5 Hv Hxs5].
           ++ (* size 4 *)
              simpl. constructor; [constructor; constructor; assumption | ].
              constructor; [constructor; constructor; assumption | constructor].
            ++ (* size ≥ 5 *)
              replace (toTuplesA (x' :: y' :: z' :: w' :: v' :: xs5'))
                with (Thunk (TripleA x' y' z') :: toTuplesA (w' :: v' :: xs5')) by reflexivity.
              replace (toTuplesA (x :: y :: z :: w :: v :: xs5))
                with (Thunk (TripleA x y z) :: toTuplesA (w :: v :: xs5)) by reflexivity.
              constructor.
              ** constructor; constructor; assumption.
              ** apply (IH (length (w' :: v' :: xs5'))).
                --- subst n. simpl. lia.
                --- constructor; [exact Hw | (constructor; [exact Hv | exact Hxs5])].
                --- reflexivity.
Qed.


(** *** Monotonicity of [glueA']. *)
Lemma glueA'_mon :
  forall (A : Type) (q1 : SeqA A),
  forall `{LDA : LessDefined A, !PreOrder LDA}
         (q1' : SeqA A) (as'_ as_ : list (T A)) (q2' q2 : SeqA A),
    q1' `less_defined` q1 ->
    Forall2 less_defined as'_ as_ ->
    q2' `less_defined` q2 ->
    glueA' q1' as'_ q2' `less_defined` glueA' q1 as_ q2.
Proof.
Admitted.
(* Proof.
  apply (SeqA_ind
    (fun A q1 =>
       forall `{LDA : LessDefined A, !PreOrder LDA}
              (q1' : SeqA A) (as'_ as_ : list (T A)) (q2' q2 : SeqA A),
         q1' `less_defined` q1 ->
         Forall2 less_defined as'_ as_ ->
         q2' `less_defined` q2 ->
         glueA' q1' as'_ q2' `less_defined` glueA' q1 as_ q2)).

  - (* NilA case *)
    intros A0 LDA0 PA0 q1' as'_ as_ q2' q2 Hq1 Has Hq2.
    invert_clear Hq1.
    simpl glueA'.
    apply tick_mon.
    apply fold_fconsA_mon; [exact Has | apply ret_mon; exact Hq2].

  - (* q1 = UnitA x1 *)
    intros A0 x1 LDA0 PA0 q1' as'_ as_ q2' q2 Hq1 Has Hq2.
    invert_clear Hq1 as [| ? ? Hxx | ].
    rename x0 into x1''. (* q1' = UnitA x1'', x1'' ≤ x1; rename if Coq doesn't already *)
    destruct q2 as [| y2 | u2 m2 v2].
    + (* q2 = NilA *)
      invert_clear Hq2.
      simpl glueA'.
      apply tick_mon.
      apply fold_fsnocA_mon;
        [exact Has | apply ret_mon; constructor; assumption].
    + (* q2 = UnitA y2 *)
      invert_clear Hq2 as [| ? ? Hyy | ].
      Local Opaque fconsA.
      simpl glueA'.
      apply tick_mon.
      apply bind_mon.
      apply fold_fconsA_mon.
      * assumption.
      * apply ret_mon. constructor; assumption.
      * intros. apply fconsA_mon; auto.
    + (* q2 = MoreA u2 m2 v2 *)
      invert_clear Hq2 as [| | ? ? ? ? ? ? Hu2 Hm2 Hv2].
      simpl glueA'.
      apply tick_mon.
      apply bind_mon.
      apply fold_fconsA_mon.
      * assumption.
      * apply ret_mon. constructor; assumption.
      * intros. apply fconsA_mon; auto.

  - (* q1 = MoreA u1 m1 v1 *)
    intros A0 u1 m1 v1 IHm1 LDA0 PA0 q1' as'_ as_ q2' q2 Hq1 Has Hq2.
    invert_clear Hq1 as [| | ? ? ? ? ? ? Hu1 Hm1 Hv1].
    rename f1 into u1''. rename m0 into m1''. rename r1 into v1''.
    (* Better: just use the auto-named hypotheses; rename if Coq picks something obscure *)
    destruct q2 as [| y2 | u2 m2 v2].
    + (* q2 = NilA *)
      invert_clear Hq2.
      simpl glueA'.
      apply tick_mon.
      apply fold_fsnocA_mon;
        [exact Has | apply ret_mon; constructor; assumption].
    + (* q2 = UnitA y2 *)
      invert_clear Hq2 as [| ? ? Hyy | ].
      simpl glueA'.
      apply tick_mon.
      apply fold_fsnocA_mon.
      * apply Forall2_app; [exact Has | (constructor; [exact Hyy | constructor])].
      * apply ret_mon. constructor; assumption.
    + (* q2 = MoreA u2 m2 v2 — DEEP CASE *)
      invert_clear Hq2 as [| | ? ? ? ? ? ? Hu2 Hm2 Hv2].
      simpl glueA'.
      apply tick_mon.
      (* Goal: bind for forcing rD1' ≤ bind for forcing rD1 *)
      apply bind_mon.
      * (* force rD1' ≤ force rD1 *)
        apply force_mon. assumption.   (* uses Hv1 *)
      * intros v1A' v1A Hv1A.
        apply bind_mon.
        ** apply force_mon. assumption.   (* uses Hu2 *)
        ** intros u2A' u2A Hu2A.
           (* Now we have v1A', v1A : DigitA A and u2A', u2A : DigitA A,
              and demands v1A' ≤ v1A, u2A' ≤ u2A. *)
           apply bind_mon.
           --- (* Inside thunk: forcing mD1' (fun ... forcing mD2' (fun ... glueA' ...)) *)
               apply thunk_mon.
               (* Goal: forcing m1'' (fun m1A' => forcing m2'' (fun m2A' => glueA' m1A' tuples' m2A'))
                          ≤ forcing m1 (fun m1A => forcing m2 (fun m2A => glueA' m1A tuples m2A)) *)
               inversion Hm1; try solve [solve_mon].
               (* m1'' = Thunk m1A_inner', m1 = Thunk m1A_inner, m1A_inner' ≤ m1A_inner *)
               inversion Hm2; try solve [solve_mon].
               (* similar for m2 *)
               simpl forcing.
               invert_clear IHm1 as [? IH |]; try solve [solve_mon].
               {
                admit.
               }
               simpl.
               invert_clear IHm1.
               apply IHm1.
               +++ assumption.   (* m1A_inner' ≤ m1A_inner *)
               +++ (* Need: Forall2 less_defined 
                      (toTuplesA (digitToListA v1A' ++ as'_ ++ digitToListA u2A'))
                      (toTuplesA (digitToListA v1A ++ as_ ++ digitToListA u2A))     *)
                   apply toTuplesA_mon.
                   apply Forall2_app; [apply digitToListA_mon; exact Hv1A | ].
                   apply Forall2_app; [exact Has | apply digitToListA_mon; exact Hu2A].
               +++ assumption.   (* m2A_inner' ≤ m2A_inner *)
           --- intros m'_res m_res Hm_res.
               apply ret_mon. constructor; assumption.
Qed. *)

(** *** Monotonicity of [glueA] (wrapper). *)
Lemma glueA_mon (A : Type) `{LDA : LessDefined A, PreOrder A LDA}
    (q1' q1 : T (SeqA A)) (as'_ as_ : list (T A)) (q2' q2 : T (SeqA A))
  : q1' `less_defined` q1 ->
    Forall2 less_defined as'_ as_ ->
    q2' `less_defined` q2 ->
    glueA q1' as'_ q2' `less_defined` glueA q1 as_ q2.
Proof.
  (* TODO: unfold glueA and apply glueA'_mon under the forcings. *)
Admitted.


(* ================================================================= *)
(** ** Section 4: Demand function [glueD']                             *)
(* ================================================================= *)

(** *** The demand return type.

    Given a demand on [glue s1 as_ s2]'s output, we produce demands on:
    - [s1] (as a [T (SeqA B)]),
    - the middle list (per-element demands as [list (T B)]),
    - [s2] (as a [T (SeqA B)]).

    Wrapped in a [Tick] for cost tracking. *)

(** *** Helper: split a list of demands on [TupleA] back into demands on elements.

    Given demands on the rebundled tuples (output of [toTuplesA] of size 1..3)
    and the original lengths [n_v1] (1..3), [n_as] (0..3), [n_u2] (1..3),
    produce three lists of element demands matching those lengths.

    This is the "unbundle" step — the demand-side inverse of [toTuplesA].
    TODO: define carefully; the logic depends on the specific bundling
    pattern in [toTuples] (which differs for sizes 2..9). *)
Definition unbundle {B : Type}
    (tuplesD : list (T (TupleA B)))
    (n_v1 n_as n_u2 : nat) :
    list (T B) * list (T B) * list (T B) :=
  (* TODO *)
  ([], [], []).


(** *** [glueD']: the demand function. *)
Fixpoint glueD' (A B : Type) `{Exact A B}
    (s1 : Seq A) (as_ : list A) (s2 : Seq A) (outD : SeqA B)
    {struct s1} : Tick (T (SeqA B) * list (T B) * T (SeqA B)) :=
  Tick.tick >>
  match s1, s2 with
  | Nil, _ =>
      (* outD `is_approx` foldr fcons s2 as_;
         walk through as_ and back-propagate demands via fconsD'. *)
      (* TODO *)
      bottom
  | _, Nil =>
      (* outD `is_approx` foldl fsnoc as_ s1;
         walk through as_ and back-propagate via fsnocD'. *)
      (* TODO *)
      bottom
  | Unit x, _ =>
      (* TODO *)
      bottom
  | _, Unit y =>
      (* TODO *)
      bottom
  | More u1 m1 v1, More u2 m2 v2 =>
      (* outD : SeqA B should be MoreA u1D m'D v2D where m'D demands
         the recursive glue's output. *)
      match outD with
      | MoreA u1D m'D v2D =>
          let+ (m1D_in, tuplesD_in, m2D_in) :=
              thunkD (glueD' m1 (toTuples (digitToList v1 ++ as_ ++ digitToList u2)) m2) m'D in
          (* Unbundle [tuplesD_in] back into demands on [v1], [as_], [u2]. *)
          let '(v1D_elts, asD, u2D_elts) :=
              unbundle tuplesD_in (length (digitToList v1))
                                  (length as_)
                                  (length (digitToList u2)) in
          (* Reassemble v1D as a DigitA demand and u2D as a DigitA demand. *)
          (* TODO: reassemble logic depends on whether v1, u2 are One/Two/Three. *)
          Tick.ret (Thunk (MoreA u1D m1D_in (Thunk (OneA Undefined))),  (* placeholder *)
                    asD,
                    Thunk (MoreA (Thunk (OneA Undefined)) m2D_in v2D))   (* placeholder *)
      | _ => bottom
      end
  end.

(** Top-level wrapper. *)
Definition glueD (A : Type) : Seq A -> list A -> Seq A -> SeqA A
                            -> Tick (T (SeqA A) * list (T A) * T (SeqA A)) :=
  glueD'.


(** *** [glueD'_approx]: the demand is an approximation of the inputs. *)
Lemma glueD'_approx : forall (A B : Type)
    `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (s1 : Seq A) (as_ : list A) (s2 : Seq A) (outD : SeqA B),
    outD `is_approx` glue s1 as_ s2 ->
    let '(s1D, asD, s2D) := Tick.val (glueD' s1 as_ s2 outD) in
    s1D `less_defined` exact s1 /\
    Forall2 less_defined asD (List.map exact as_) /\
    s2D `less_defined` exact s2.
Proof.
  (* TODO: induction on s1 (using glue_ind once it's correctly stated, or
     direct structural induction).  Each base case uses fconsD'_approx
     or fsnocD'_approx repeatedly through the fold.  The deep case uses IH. *)
Admitted.


(** *** [glueD'_exact]: when the output demand is exact, the input demand is too. *)
Lemma glueD'_exact (A B : Type) `{Exact A B}
    (s1 : Seq A) (as_ : list A) (s2 : Seq A) :
  let '(s1D, asD, s2D) := Tick.val (glueD' s1 as_ s2 (exact (glue s1 as_ s2))) in
  s1D = exact s1 /\
  asD = List.map exact as_ /\
  s2D = exact s2.
Proof.
  (* TODO *)
Admitted.


(* ================================================================= *)
(** ** Section 5: Spec and cost lemmas                                 *)
(* ================================================================= *)

#[local] Existing Instance Reflexive_LessDefined_T.
#[local] Existing Instance Reflexive_LessDefined_prodA.

(** *** [glueD'_spec]: the clairvoyant semantics dominates the demand semantics.

    Mirrors [fconsD'_spec], [fsnocD'_spec], [ftailD'_spec].  Five cases
    matching [glue]'s structure. *)
Lemma glueD'_spec (A B : Type) :
  forall `{LDB : LessDefined B, !Reflexive LDB, !Transitive LDB, Exact A B}
    (s1 : Seq A) (as_ : list A) (s2 : Seq A) (outD : SeqA B),
    outD `is_approx` glue s1 as_ s2 ->
    forall s1D asD s2D,
      (s1D, asD, s2D) = Tick.val (glueD' s1 as_ s2 outD) ->
      let dcost := Tick.cost (glueD' s1 as_ s2 outD) in
      glueA s1D asD s2D
      [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  (* TODO: structural induction on s1.  Five cases.
     - Base cases (NilA, UnitA on either side): the demand chain through
       foldr fconsD' or foldl fsnocD' aligns with the clairvoyant
       foldr fconsA / foldl fsnocA by element-wise fconsD'_spec /
       fsnocD'_spec.
     - MoreA-MoreA: invoke IH for the deeper-level glueD'_spec via
       optimistic_corelax + glueA'_mon. *)
Admitted.


(** *** [glueD'_cost]: worst-case [O(log min(depth s1, depth s2))] cost bound.

    Cost is linear in the smaller spine depth, plus a constant.
    Constants [c, c'] determined during the proof. *)
Lemma glueD'_cost : forall (A B : Type) `{LessDefined B, Exact A B}
    (s1 : Seq A) (as_ : list A) (s2 : Seq A) (outD : SeqA B),
    outD `is_approx` glue s1 as_ s2 ->
    let inM := glueD' s1 as_ s2 outD in
    let cost := Tick.cost inM in
    cost <= 5 * Nat.min (depth s1) (depth s2) + 10.   (* placeholder constants *)
Proof.
  (* TODO: structural induction on s1.
     - Base cases bound by the constant (foldr / foldl over bounded list
       of fcons / fsnoc).
     - MoreA-MoreA case: cost = 1 (tick) + inner cost.  Inner cost is
       bounded by IH at one level deeper; both depth s1 and depth s2
       decrement, so Nat.min (depth m1) (depth m2) = Nat.min (depth s1) (depth s2) - 1. *)
Admitted.


(* ================================================================= *)
(** ** End of FingerConcat                                              *)
(* ================================================================= *)
