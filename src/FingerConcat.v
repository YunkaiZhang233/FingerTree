(** * FingerConcat — Claessen's [glue] / concatenation operation

    This file implements the concatenation operation for the simplified
    finger tree, following Claessen 2020 §7.

    Unlike [fcons]/[fsnoc]/[ftail] (amortized constant), [glue] is
    **worst-case** logarithmic.  No new debit machinery is needed:
    [Debitable_T], [Debitable_SeqA], [safe_DigitA], [safe_T], and their
    sub-additivity lemmas are imported from [FingerCore.v].

    Structure:
      Section 1: Pure helpers ([depth], [digitToList], [toTuples]).
      Section 2: Pure [glue] function + custom induction principle.
      Section 3: Clairvoyant [glueA'] + monotonicity helpers.
      Section 4: Demand function [glueD'] (Claim 1 scope only).
      Section 5: Cost lemma [glueD'_cost] and corollary [concatD_cost].
      Section 6: Stubs for future work ([glueD'_approx], [glueD'_spec]).

    SCOPE NOTE: this file is currently set up for **Claim 1 only**
    (worst-case [O(log n)] cost bound on [concat], proved as a standalone
    lemma).  The [unbundle] helper is stubbed for cost-only analysis;
    a correct implementation is required for [glueD'_approx] / [glueD'_spec].
    See [claim1_design.md] for the scope rationale.  *)

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

(** *** [digitToList]: convert a [Digit A] to a list of 1..3 elements. *)
Definition digitToList {A : Type} (d : Digit A) : list A :=
  match d with
  | One   x     => [x]
  | Two   x y   => [x; y]
  | Three x y z => [x; y; z]
  end.

(** *** [toTuples]: convert a list of size 2..9 to a list of 1..3 [Tuple]s.

    Following Claessen 2020 §7.  The function is partial on size 1 input
    (see footnote 2 of the paper); we return [[]] in that case as a
    fallback.  In [glue]'s recursive case the input always has size ≥ 2. *)
Fixpoint toTuples {A : Type} (xs : list A) : list (Tuple A) :=
  match xs with
  | []            => []
  | [x; y]        => [Pair x y]
  | [x; y; z; w]  => [Pair x y; Pair z w]
  | x :: y :: z :: rest => Triple x y z :: toTuples rest
  | _             => []   (* unreachable for inputs of size 2..9 *)
  end.

(** Block [simpl] from over-eagerly unfolding [toTuples]. *)
Arguments toTuples : simpl nomatch.


(* ================================================================= *)
(** ** Section 2: Pure [glue] function                                 *)
(* ================================================================= *)

(** *** [glue]: generalized concatenation with a middle list of size 0..3.

    See Claessen 2020 §7.  Termination via [{struct s1}]: each recursive
    call peels a [More] from [s1], with the element type changing from
    [A] to [Tuple A] (polymorphic recursion).  *)
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

    Exposes the 6 case shapes (cases 2, 3 are split by [s_1]'s shape;
    case 4 covers both Unit-Unit and Unit-More).  The deep case
    provides an IH at the [Tuple A] level. *)
Lemma glue_ind :
  forall (P : forall (A : Type), Seq A -> list A -> Seq A -> Seq A -> Prop),
    (* Case 1: Nil, _, _ *)
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
  - simpl. apply H1.
  - refine (
      match s2 as s2'
        return P A (Unit x) as_ s2' (glue (Unit x) as_ s2')
      with
      | Nil           => _
      | Unit y        => _
      | More u m v    => _
      end).
    + simpl. apply H2.
    + simpl. apply H4. discriminate.
    + simpl. apply H4. discriminate.
  - refine (
      match s2 as s2'
        return P A (More u1 m1 v1) as_ s2' (glue (More u1 m1 v1) as_ s2')
      with
      | Nil           => _
      | Unit y        => _
      | More u2 m2 v2 => _
      end).
    + simpl. apply H3.
    + simpl. apply H5.
    + simpl. apply H6. apply SELF.
Qed.


(* ================================================================= *)
(** ** Section 3: Clairvoyant version [glueA']                         *)
(* ================================================================= *)

(** Convert a [DigitA A] to a list of [T A] (1..3 elements). *)
Definition digitToListA {A : Type} (d : DigitA A) : list (T A) :=
  match d with
  | OneA   x     => [x]
  | TwoA   x y   => [x; y]
  | ThreeA x y z => [x; y; z]
  end.

(** Convert a list of [T A] (size 2..9) to a list of [T (TupleA A)] (size 1..3). *)
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


(** Clairvoyant glue. *)
Fixpoint glueA' (A : Type) (q1 : SeqA A) (as_ : list (T A)) (q2 : SeqA A) {struct q1} : M (SeqA A) :=
  tick >>
  (match q1, q2 with
   | NilA, _ =>
       List.fold_right
         (fun x acc => let! q := acc in fconsA x (Thunk q))
         (ret q2) as_
   | _, NilA =>
       List.fold_left
         (fun acc x => let! q := acc in fsnocA (Thunk q) x)
         as_ (ret q1)
   | UnitA x, _ =>
       List.fold_right
         (fun x acc => let! q := acc in fconsA x (Thunk q))
         (ret q2) (x :: as_)
   | _, UnitA y =>
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


(** *** Monotonicity helpers (kept for future use; NOT needed for Claim 1) *)

Lemma fold_fconsA_mon (A : Type) `{LDA : LessDefined A, PreOrder A LDA}
    (as'_ as_ : list (T A)) (m'_acc m_acc : M (SeqA A)) :
    Forall2 less_defined as'_ as_ ->
    m'_acc `less_defined` m_acc ->
    List.fold_right (fun x acc => let! q := acc in fconsA x (Thunk q)) m'_acc as'_
    `less_defined`
    List.fold_right (fun x acc => let! q := acc in fconsA x (Thunk q)) m_acc as_.
Proof.
  intro Hforall. induction Hforall as [| x' x as'_ as_ Hx Has IH]; intros Hacc.
  - simpl. exact Hacc.
  - Local Opaque fconsA. simpl.
    apply bind_mon.
    + apply IH. exact Hacc.
    + intros q' q Hq. apply fconsA_mon. 
      * exact Hx.
      * apply LessDefined_Thunk. exact Hq.
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
  - Local Opaque fsnocA. simpl.
    apply IH.
    apply bind_mon; [exact Hacc | ].
    intros q' q Hq. apply fsnocA_mon.
    + assumption.
    + apply LessDefined_Thunk. exact Hq.
Qed.

Lemma toTuplesA_mon (A : Type) `{LDA : LessDefined A}
    (xs' xs : list (T A)) :
    Forall2 less_defined xs' xs ->
    Forall2 less_defined (toTuplesA xs') (toTuplesA xs).
Proof.
  intro H.
  remember (length xs') as n eqn:Hn.
  revert xs' xs H Hn.
  induction n as [n IH] using lt_wf_ind.
  intros xs' xs H Hn.
  (* Case on the first few elements of xs' / xs in lockstep using Forall2 *)
  destruct H as [| x' x xs1' xs1 Hx Hxs1].
  - (* both empty *)
    simpl. constructor.
  - destruct Hxs1 as [| y' y xs2' xs2 Hy Hxs2].
    + (* size 1: xs' = [x'], xs = [x] *)
      simpl. constructor.
    + destruct Hxs2 as [| z' z xs3' xs3 Hz Hxs3].
      * (* size 2: xs' = [x'; y'], xs = [x; y] *)
        simpl. constructor; [ | constructor].
        constructor. constructor; assumption.
      * destruct Hxs3 as [| w' w xs4' xs4 Hw Hxs4].
        -- (* size 3: xs' = [x'; y'; z'] *)
           simpl. constructor; [ | constructor].
           constructor. constructor; assumption.
        -- destruct Hxs4 as [| v' v xs5' xs5 Hv Hxs5].
           ++ (* size 4: xs' = [x'; y'; z'; w'] *)
              simpl. constructor.
              ** constructor. constructor; assumption.
              ** constructor; [ | constructor].
                 constructor. constructor; assumption.
           ++ (* size ≥ 5: recurse via IH on xs2 (length n-3) *)
              (* Unfold ONE step of toTuplesA, exposing Triple + recursive call. *)
              replace (toTuplesA (x' :: y' :: z' :: w' :: v' :: xs5'))
                with (Thunk (TripleA x' y' z') :: toTuplesA (w' :: v' :: xs5'))
                by reflexivity.
              replace (toTuplesA (x :: y :: z :: w :: v :: xs5))
                with (Thunk (TripleA x y z) :: toTuplesA (w :: v :: xs5))
                by reflexivity.
              constructor.
              ** constructor. constructor; assumption.
              ** (* Apply IH on (w' :: v' :: xs5'), (w :: v :: xs5).
                    Length is length xs5' + 2, which is < length xs' = length xs5' + 5. *)
                 apply (IH (length (w' :: v' :: xs5'))).
                 --- simpl. simpl in Hn. lia.
                 --- constructor; [exact Hw | (constructor; [exact Hv | exact Hxs5])].
                 --- reflexivity.
Qed.

(* Lemma glueA'_mon :
  forall (A : Type) (q1 : SeqA A),
  forall `{LDA : LessDefined A, !PreOrder LDA}
         (q1' : SeqA A) (as'_ as_ : list (T A)) (q2' q2 : SeqA A),
    q1' `less_defined` q1 ->
    Forall2 less_defined as'_ as_ ->
    q2' `less_defined` q2 ->
    glueA' q1' as'_ q2' `less_defined` glueA' q1 as_ q2.
Proof.
  (* TODO: apply (SeqA_ind ...) following ftailA'_mon pattern. *)
Admitted. *)

(* Lemma glueA_mon (A : Type) `{LDA : LessDefined A, PreOrder A LDA}
    (q1' q1 : T (SeqA A)) (as'_ as_ : list (T A)) (q2' q2 : T (SeqA A)) :
    q1' `less_defined` q1 ->
    Forall2 less_defined as'_ as_ ->
    q2' `less_defined` q2 ->
    glueA q1' as'_ q2' `less_defined` glueA q1 as_ q2.
Proof.
  (* TODO: unfold glueA, apply forcing_mon twice, then glueA'_mon. *)
Admitted. *)


(* ================================================================= *)
(** ** Section 4: Demand function [glueD'] (Claim 1 scope)             *)
(* ================================================================= *)

(** *** Helper: unbundle demands on tuples back to demands on elements.

    For Claim 1 (cost only), this is stubbed as returning [Undefined] /
    empty / [Undefined].  The demand outputs are then incorrect in the
    strong sense (they do not approximate the inputs), but cost analysis
    is unaffected because [unbundle] is a pure function with no [tick].

    A correct implementation requires careful case analysis on the input
    list lengths and the bundling pattern of [toTuples]. *)
Definition unbundle {B : Type}
    (tuplesD : list (T (TupleA B)))
    (n_v1 n_as n_u2 : nat) :
    T (DigitA B) * list (T B) * T (DigitA B) :=
  (Undefined, [], Undefined).


(** *** Helper: demand-side fold-right for [fcons]. *)
Fixpoint foldr_fconsD' (A B : Type) `{Exact A B}
    (as_ : list A) (s_2 : Seq A) (outD : SeqA B)
    : Tick (T (SeqA B)) :=
  match as_ with
  | [] =>
      Tick.ret (Thunk outD)
  | x :: as' =>
      let+ innerD := fconsD' x (List.fold_right fcons s_2 as') outD in
      let innerD_forced := match innerD with
                           | Thunk q => q
                           | Undefined => bottom_of (exact (List.fold_right fcons s_2 as'))
                           end in
      foldr_fconsD' as' s_2 innerD_forced
  end.

(** *** Helper: demand-side fold-left for [fsnoc].

    Recursion is on [as_] directly: [foldl fsnoc s_1 (x :: as') =
    foldl fsnoc (fsnoc s_1 x) as'].  Demand inversion: first invert the
    rest of the fold (on [as'] with accumulator [fsnoc s_1 x]), then
    invert the one [fsnoc] step. *)
Fixpoint foldl_fsnocD' (A B : Type) `{Exact A B}
    (as_ : list A) (s_1 : Seq A) (outD : SeqA B)
    {struct as_} : Tick (T (SeqA B)) :=
  match as_ with
  | [] =>
      Tick.ret (Thunk outD)
  | x :: as' =>
      let+ innerD := foldl_fsnocD' as' (fsnoc s_1 x) outD in
      let innerD_forced := match innerD with
                           | Thunk q => q
                           | Undefined => bottom_of (exact (fsnoc s_1 x))
                           end in
      let+ s1D := fsnocD' s_1 x innerD_forced in
      Tick.ret s1D
  end.


(** *** [glueD']: the demand function for [glue].

    Six cases mirroring [glue]'s structure.  The deep case uses
    [unbundle] (stubbed) to split the recursive middle demand back into
    demands on [v1], [as_], [u2]. *)
Fixpoint glueD' (A B : Type) `{Exact A B}
    (s1 : Seq A) (as_ : list A) (s2 : Seq A) (outD : SeqA B)
    {struct s1} : Tick (T (SeqA B) * list (T B) * T (SeqA B)) :=
  Tick.tick >>
  match s1, s2 with
  | Nil, _ =>
      (* glue Nil as_ s_2 = foldr fcons s_2 as_ *)
      let+ s2D := foldr_fconsD' as_ s2 outD in
      Tick.ret (Thunk NilA, List.map (fun _ => Undefined) as_, s2D)

  | Unit x, Nil =>
      (* glue (Unit x) as_ Nil = foldl fsnoc (Unit x) as_ *)
      let+ s1D := foldl_fsnocD' as_ (Unit x) outD in
      Tick.ret (s1D, List.map (fun _ => Undefined) as_, Thunk NilA)

  | More u1 m1 v1, Nil =>
      (* glue (More u_1 m_1 v_1) as_ Nil = foldl fsnoc (More u_1 m_1 v_1) as_ *)
      let+ s1D := foldl_fsnocD' as_ (More u1 m1 v1) outD in
      Tick.ret (s1D, List.map (fun _ => Undefined) as_, Thunk NilA)

  | Unit x, _ =>
      (* glue (Unit x) as_ s_2 = foldr fcons s_2 (x :: as_) *)
      let+ s2D := foldr_fconsD' (x :: as_) s2 outD in
      Tick.ret (Thunk (UnitA Undefined), List.map (fun _ => Undefined) as_, s2D)

  | More u1 m1 v1, Unit y =>
      (* glue (More u_1 m_1 v_1) as_ (Unit y) = foldl fsnoc (More u_1 m_1 v_1) (as_ ++ [y]) *)
      let+ s1D := foldl_fsnocD' (as_ ++ [y]) (More u1 m1 v1) outD in
      Tick.ret (s1D, List.map (fun _ => Undefined) as_, Thunk (UnitA Undefined))

  | More u1 m1 v1, More u2 m2 v2 =>
      match outD with
      | MoreA u1D m'D v2D =>
          let n_v1 := List.length (digitToList v1) in
          let n_as := List.length as_ in
          let n_u2 := List.length (digitToList u2) in
          let middle := toTuples (digitToList v1 ++ as_ ++ digitToList u2) in
          let m'D_forced := match m'D with
                            | Thunk q => q
                            | Undefined => bottom_of (exact (glue m1 middle m2))
                            end in
          let+ (m1D, middleD, m2D) := glueD' m1 middle m2 m'D_forced in
          let '(v1D, asD, u2D) := unbundle middleD n_v1 n_as n_u2 in
          Tick.ret (Thunk (MoreA u1D m1D v1D), asD, Thunk (MoreA u2D m2D v2D))
      | _ =>
          Tick.ret (Undefined, List.map (fun _ => Undefined) as_, Undefined)
      end
  end.

(** Top-level wrapper. *)
Definition glueD (A : Type) : Seq A -> list A -> Seq A -> SeqA A
                            -> Tick (T (SeqA A) * list (T A) * T (SeqA A)) :=
  glueD'.

(** Top-level concat demand. *)
Definition concatD (A : Type) (q1 q2 : Seq A) (outD : SeqA A)
    : Tick (T (SeqA A) * list (T A) * T (SeqA A)) :=
  glueD' q1 [] q2 outD.

Arguments glueD' : simpl nomatch.


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


(* ================================================================= *)
(** ** Section 5: Cost lemma and corollary                             *)
(* ================================================================= *)


(** Debt of a demand is bounded by twice the depth of its approximand. *)
Lemma debt_le_2depth (A : Type) (s : Seq A) :
  forall (B : Type) `{LessDefined B, Exact A B} (outD : SeqA B),
    outD `is_approx` s -> debt outD <= 2 * depth s.
Proof.
  revert s. revert A.
  apply (Seq_ind_poly
    (fun (A : Type) (s : Seq A) =>
      forall (B : Type) `{LessDefined B, Exact A B} (outD : SeqA B),
        outD `is_approx` s -> debt outD <= 2 * depth s)).
  - intros A0 B0 LDB0 EAB0 outD Happrox.
    invert_clear Happrox. simpl. unfold_debt. lia.
  - intros A0 x B0 LDB0 EAB0 outD Happrox.
    invert_clear Happrox. simpl. unfold_debt. lia.
  - intros A0 f m r IHm B0 LDB0 EAB0 outD Happrox.
    invert_clear Happrox as [| | fD ? mD ? rD ? Hf Hm Hr].
    unfold_debt.
    assert (Hsafe_f : T_rect _ safe_DigitA 1 fD <= 1).
    { 
      destruct fD as [d|]; simpl; [destruct d; simpl; lia | lia]. 
    }
    assert (Hsafe_r : T_rect _ safe_DigitA 1 rD <= 1).
    { 
      destruct rD as [d|]; simpl; [destruct d; simpl; lia | lia]. 
    }
    assert (Hm_bound : @Debitable_T _ (@Debitable_SeqA (TupleA B0)) mD <= 2 * depth m).
    {
      destruct mD as [m_inner | ].
      - invert_clear Hm as [| ? ? Hm_inner ].
        simpl. 
        apply (IHm (TupleA B0) _ _ m_inner Hm_inner).
      - simpl. lia.
    }
    simpl depth.
    lia.
Qed.

(** Depth of a foldr-fcons is bounded by depth + list length. *)
Lemma fcons_depth (A : Type) (x : A) (s : Seq A) :
  depth (fcons x s) <= depth s + 1.
Proof.
  (* Structural induction on s, with case on front digit for the More case. *)
  revert x.
  apply (Seq_ind_poly
    (fun (A : Type) (s : Seq A) =>
       forall (x : A), depth (fcons x s) <= depth s + 1)); intros.
  - (* Nil: fcons x Nil = Unit x, depth 0 *)
    simpl. lia.
  - (* Unit y: fcons x (Unit y) = More (One x) Nil (One y), depth 1 *)
    simpl. lia.
  - (* More f m r *)
    destruct f as [a | a b | a b c]; simpl.
    + (* One a: fcons x (More (One a) m r) = More (Two x a) m r, same depth *)
      lia.
    + (* Two a b: fcons x (More (Two a b) m r) = More (Three x a b) m r, same depth *)
      lia.
    + (* Three a b c: fcons x (More (Three a b c) m r) 
                   = More (Two x a) (fcons (Pair b c) m) r.
         New depth = S(depth (fcons (Pair b c) m)).
         By IH: depth (fcons (Pair b c) m) ≤ depth m + 1.
         So new depth ≤ S(depth m + 1) = depth m + 2 = depth (More _ m r) + 1. ✓ *)
      specialize (H (Pair b c)).   (* H is the IH from Seq_ind_poly *)
      lia.
Qed.

Lemma foldr_fcons_depth (A : Type) (as_ : list A) (s_2 : Seq A) :
  depth (List.fold_right fcons s_2 as_) <= depth s_2 + List.length as_.
Proof.
  induction as_ as [| x as' IH]; simpl.
  - lia.
  - pose proof (fcons_depth x (List.fold_right fcons s_2 as')) as Hf.
    lia.
Qed.
(** *** Cost of the demand-side fold-right.

    For [as_] of bounded length, the cost is linear in [depth s_2] with
    constants depending on [fconsD'_cost]. *)
Lemma foldr_fconsD'_cost (A B : Type) `{LDB: LessDefined B, !Reflexive LDB, Exact A B}
    (as_ : list A) (s_2 : Seq A) (outD : SeqA B) :
  outD `is_approx` List.fold_right fcons s_2 as_ ->
  Tick.cost (foldr_fconsD' as_ s_2 outD) <= 
    List.length as_ * (4 + 2 * depth s_2 + 2 * List.length as_).
Proof.
  revert s_2 outD.
  induction as_ as [| x as' IH]; intros s_2 outD Happrox.
  
  - (* Base case *)
    simpl. lia.
  
  - (* Step *)
    Local Opaque fconsD'.
    cbn [foldr_fconsD'].
    (* Tick.cost (let+ innerD := fconsD' x ... in foldr_fconsD' as' s_2 innerD_forced) *)
    (* = Tick.cost (fconsD' x ...) + Tick.cost (foldr_fconsD' as' s_2 innerD_forced) *)
    
    (* Apply fconsD'_cost to bound the first part *)
    pose proof (@fconsD'_cost A B _ _  x (List.fold_right fcons s_2 as') outD Happrox) as Hfcons.

    cbv zeta in Hfcons. (* should unfold the cost bound to 2 + debt outD - debt innerD *)

    pose proof (@debt_le_2depth A (List.fold_right fcons s_2 (x :: as')) B _ _ outD Happrox) as Hdebt.
    
    (* Bound depth(foldr fcons s_2 as') by depth s_2 + |as'| *)
    pose proof (foldr_fcons_depth as' s_2) as Hdepth.
    (* Hdepth : depth (foldr fcons s_2 as') <= depth s_2 + length as' *)
    
    (* Apply IH on the recursive call *)
    set (innerD := Tick.val (fconsD' x (List.fold_right fcons s_2 as') outD)) in *.
    set (innerD_forced := match innerD with
                          | Thunk q => q
                          | Undefined => bottom_of (exact (List.fold_right fcons s_2 as'))
                          end) in *.
    
    assert (Hinner_approx : innerD_forced `is_approx` List.fold_right fcons s_2 as').
    {
      unfold innerD_forced.
      destruct innerD as [ q | ] eqn:Eq.
      - Local Opaque fconsD'_approx.
        pose proof (@fconsD'_approx A B _ _ _ x (List.fold_right fcons s_2 as') outD Happrox) as Hap.
        unfold innerD in Eq. simpl in Hap. rewrite Eq in Hap.
        invert_clear Hap. assumption.
      - apply bottom_is_least. reflexivity.
    }
    
    specialize (IH s_2 innerD_forced Hinner_approx).
    (* IH : Tick.cost (foldr_fconsD' as' s_2 innerD_forced) <= 
            |as'| * (4 + 2 * depth s_2 + 2 * |as'|) *)
    
    simpl Tick.cost.   (* should reduce the bind structure *)
    (* Cost = Tick.cost(fconsD' x …) + Tick.cost(foldr_fconsD' as' s_2 innerD_forced) *)
    (* By Hfcons: Tick.cost(fconsD') ≤ 2 + debt outD - debt innerD ≤ 2 + debt outD ≤ 2 + 2*(depth s_2 + |as'|) *)
    (* By IH: rec cost ≤ |as'| * (4 + 2*depth s_2 + 2*|as'|) *)
    change (match Tick.val (fconsD' x (List.fold_right fcons s_2 as') outD) with
        | Thunk q => q
        | Undefined => bottom_of (exact (List.fold_right fcons s_2 as'))
        end) with innerD_forced.
    
    pose proof (foldr_fcons_depth (x :: as') s_2) as Hdepth_xs.
    simpl in Hdepth_xs.

    cbn [List.fold_right] in Hdebt.

    simpl length.
    (* Total: ≤ (2 + 2*depth s_2 + 2*|as'|) + |as'| * (4 + 2*depth s_2 + 2*|as'|)
            = (|as'| + 1) * (4 + 2*depth s_2 + 2*|as'|) - 2
            ≤ S |as'| * (4 + 2*depth s_2 + 2 * S |as'|) - 2
            ≤ S |as'| * (4 + 2*depth s_2 + 2 * S |as'|). *)
    
    lia.
Qed.


(** *** Cost of the demand-side fold-left. *)


Lemma foldl_fsnocD'_approx (A B : Type) `{LDB: LessDefined B, !Reflexive LDB, Exact A B}
    (as_ : list A) (s_1 : Seq A) (outD : SeqA B) :
  outD `is_approx` List.fold_left fsnoc as_ s_1 ->
  Tick.val (foldl_fsnocD' as_ s_1 outD) `is_approx` s_1.
Proof.
  revert s_1 outD.
  induction as_ as [| x as' IH]; intros s_1 outD Happrox.
  
  - (* Base: foldl_fsnocD' [] s_1 outD = Tick.ret (Thunk outD).
       Tick.val = Thunk outD.  Need: Thunk outD ≤ exact s_1.
       outD ≤ exact (fold_left fsnoc [] s_1) = exact s_1.  ✓ *)
    simpl. constructor. exact Happrox.
  
  - (* Step: foldl_fsnocD' (x :: as') s_1 outD =
       let+ innerD := foldl_fsnocD' as' (fsnoc s_1 x) outD in
       let innerD_forced := ... in
       let+ s1D := fsnocD' s_1 x innerD_forced in
       Tick.ret s1D.
       
       Goal: Tick.val (the above) ≤ exact s_1.
       Tick.val = Tick.val (fsnocD' s_1 x innerD_forced).
       
       Strategy: 
       - Use IH on the inner call: Tick.val(foldl_fsnocD' as' (fsnoc s_1 x) outD) ≤ exact (fsnoc s_1 x).
       - That gives innerD_forced ≤ exact (fsnoc s_1 x).
       - Then by fsnocD'_approx: Tick.val(fsnocD' s_1 x innerD_forced) ≤ exact s_1. *)
    
    cbn [List.fold_left] in Happrox.
    (* Happrox : outD ≤ exact (fold_left fsnoc as' (fsnoc s_1 x)) *)
    
    specialize (IH (fsnoc s_1 x) outD Happrox).
    (* IH : Tick.val (foldl_fsnocD' as' (fsnoc s_1 x) outD) ≤ exact (fsnoc s_1 x) *)
    
    Local Opaque fsnocD'.
    cbn [foldl_fsnocD'].
    
    set (innerD := Tick.val (foldl_fsnocD' as' (fsnoc s_1 x) outD)) in *.
    set (innerD_forced := match innerD with
                          | Thunk q => q
                          | Undefined => bottom_of (exact (fsnoc s_1 x))
                          end) in *.
    
    assert (Hinner_approx : innerD_forced `is_approx` fsnoc s_1 x).
    {
      unfold innerD_forced.
      destruct innerD as [ q | ] eqn:Eq.
      - invert_clear IH. assumption.
      - apply bottom_is_least. reflexivity.
    }
    
    pose proof (@fsnocD'_approx A B _ _ _ s_1 x innerD_forced Hinner_approx) as Hf.
    
    (* The body: let+ s1D := fsnocD' s_1 x innerD_forced in Tick.ret s1D.
       Tick.val of this = Tick.val (Tick.ret (Tick.val (fsnocD' s_1 x innerD_forced)))
                        = Tick.val (fsnocD' s_1 x innerD_forced).
       Wait, that's not right.  Let me think.
       
       Tick.bind has structure:
         Tick.val (Tick.bind m f) = Tick.val (f (Tick.val m)).
       
       Here: let+ s1D := fsnocD' s_1 x innerD_forced in Tick.ret s1D.
       This is Tick.bind (fsnocD' s_1 x innerD_forced) (fun s1D => Tick.ret s1D).
       Tick.val = Tick.val (Tick.ret (Tick.val (fsnocD' s_1 x innerD_forced)))
                = Tick.val (fsnocD' s_1 x innerD_forced).  ✓
    *)
    
    simpl Tick.val.
    change (match Tick.val (foldl_fsnocD' as' (fsnoc s_1 x) outD) with
            | Thunk q => q
            | Undefined => bottom_of (exact (fsnoc s_1 x))
            end) with innerD_forced.
    
    exact Hf.
Qed.


Lemma fsnoc_depth (A : Type) (s : Seq A) (x : A) :
  depth (fsnoc s x) <= depth s + 1.
Proof.
  revert x.
  apply (Seq_ind_poly
    (fun (A : Type) (s : Seq A) =>
       forall (x : A), depth (fsnoc s x) <= depth s + 1)); intros.
  - (* Nil: fsnoc Nil x = Unit x, depth 0 *)
    simpl. lia.
  - (* Unit y: fsnoc (Unit y) x = More (One y) Nil (One x), depth 1 *)
    simpl. lia.
  - (* More f m r — case on REAR digit r *)
    destruct r as [a | a b | a b c]; simpl.
    + (* One a: fsnoc (More f m (One a)) x = More f m (Two a x), same depth *)
      lia.
    + (* Two a b: fsnoc (More f m (Two a b)) x = More f m (Three a b x), same depth *)
      lia.
    + (* Three a b c: fsnoc (More f m (Three a b c)) x
                   = More f (fsnoc m (Pair a b)) (Two c x).
         By IH: depth (fsnoc m (Pair a b)) ≤ depth m + 1.
         So new depth = S(depth (fsnoc m _)) ≤ S(depth m + 1) = depth m + 2.
         Compare: depth (More f m (Three a b c)) + 1 = S(depth m) + 1 = depth m + 2. ✓ *)
      specialize (H (Pair a b)).   (* IH at type Tuple A *)
      lia.
Qed.


Lemma foldl_fsnocD'_cost (A B : Type) `{LDB: LessDefined B, !Reflexive LDB, Exact A B}
    (as_ : list A) (s_1 : Seq A) (outD : SeqA B) :
  outD `is_approx` List.fold_left fsnoc as_ s_1 ->
  Tick.cost (foldl_fsnocD' as_ s_1 outD) <= 
    List.length as_ * (4 + 2 * depth s_1 + 2 * List.length as_).
Proof.
  revert s_1 outD.
  induction as_ as [| x as' IH]; intros s_1 outD Happrox.
  
  - simpl. lia.
  
  - Local Opaque fsnocD'.
    cbn [foldl_fsnocD'].
    cbn [List.fold_left] in Happrox.
    (* Happrox : outD ≤ exact (fold_left fsnoc as' (fsnoc s_1 x)) *)
    
    specialize (IH (fsnoc s_1 x) outD Happrox).
    
    set (innerD := Tick.val (foldl_fsnocD' as' (fsnoc s_1 x) outD)) in *.
    set (innerD_forced := match innerD with
                          | Thunk q => q
                          | Undefined => bottom_of (exact (fsnoc s_1 x))
                          end) in *.
    
    assert (Hinner_approx : innerD_forced `is_approx` fsnoc s_1 x).
    {
      unfold innerD_forced.
      destruct innerD as [ q | ] eqn:Eq.
      - pose proof (@foldl_fsnocD'_approx A B _ _ _ as' (fsnoc s_1 x) outD Happrox) as Hap.
        unfold innerD in Eq. rewrite Eq in Hap. invert_clear Hap. assumption.
      - apply bottom_is_least. reflexivity.
    }
    
    pose proof (@fsnocD'_cost A B _ _ s_1 x innerD_forced Hinner_approx) as Hfsnoc.
    cbv zeta in Hfsnoc.
    
    pose proof (@debt_le_2depth A (fsnoc s_1 x) B _ _ innerD_forced Hinner_approx) as Hdebt.
    
    pose proof (fsnoc_depth s_1 x) as Hdepth_fsnoc.
    
    simpl Tick.cost.
    
    change (match Tick.val (foldl_fsnocD' as' (fsnoc s_1 x) outD) with
            | Thunk q => q
            | Undefined => bottom_of (exact (fsnoc s_1 x))
            end) with innerD_forced.
    
    simpl length.
    nia.
Qed.


(** *** Constants for the main cost bound. *)
Definition glue_cost_const_1 : nat := 8.
Definition glue_cost_const_2 : nat := 60.


(** *** [toTuples_length_bound]: output length is at most 3 for inputs of size ≤ 9.

    Used in the deep case of [glueD'_cost] to maintain the invariant that
    the middle list passed to the recursive call has length ≤ 3. *)
Lemma toTuples_length_bound (A : Type) (xs : list A) :
  List.length xs <= 9 ->
  List.length (toTuples xs) <= 3.
Proof.
  intro Hlen.
  destruct xs as [| x0 xs]; [simpl; lia | ].
  destruct xs as [| x1 xs]; [simpl; lia | ].
  destruct xs as [| x2 xs]; [simpl; lia | ].
  destruct xs as [| x3 xs]; [simpl; lia | ].
  destruct xs as [| x4 xs]; [simpl; lia | ].
  destruct xs as [| x5 xs]; [simpl; lia | ].
  destruct xs as [| x6 xs]; [simpl; lia | ].
  destruct xs as [| x7 xs]; [simpl; lia | ].
  destruct xs as [| x8 xs]; [simpl; lia | ].
  (* At this point length xs is at least 9.  If exactly 9, we have one more element. *)
  destruct xs as [| x9 xs]; [simpl; lia | ].
  (* Length is at least 10 here, contradicting Hlen *)
  simpl in Hlen. lia.
Qed.



(** *** Main cost theorem: [glueD'] cost is bounded by [c_1 * (d_1 + d_2) + c_2].

    Proved by structural induction on [s_1].  Maintains the invariant
    [length as_ ≤ 3] (since [toTuples] preserves this; see
    [toTuples_length_bound]).  *)
Lemma glueD'_cost :
  forall (A : Type) (s1 : Seq A),
  forall (B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (as_ : list A) (s2 : Seq A) (outD : SeqA B),
    outD `is_approx` glue s1 as_ s2 ->
    List.length as_ <= 3 ->
    Tick.cost (glueD' s1 as_ s2 outD) <=
      glue_cost_const_1 * (depth s1 + depth s2) + glue_cost_const_2.
Proof.
  apply (Seq_ind_poly
    (fun A s1 =>
      forall (B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
        (as_ : list A) (s2 : Seq A) (outD : SeqA B),
        outD `is_approx` glue s1 as_ s2 ->
        List.length as_ <= 3 ->
        Tick.cost (glueD' s1 as_ s2 outD) <=
          glue_cost_const_1 * (depth s1 + depth s2) + glue_cost_const_2)).
  
  (* === Case 1: s1 = Nil === *)
  - intros A0 B0 LDB0 Refl0 EAB0 as_ s2 outD Happrox Hlen.
    Local Opaque foldr_fconsD' foldl_fsnocD' fconsD' fsnocD'.
    cbn [glueD'].
    (* Goal: Tick.cost (let+ s2D := foldr_fconsD' as_ s2 outD in Tick.ret (...)) ≤ 8 * depth s2 + 60 *)
    pose proof (@foldr_fconsD'_cost A0 B0 _ _ _ as_ s2 outD Happrox) as Hfold.
    simpl Tick.cost.
    (* Cost = Tick.cost(Tick.tick) + Tick.cost(foldr_fconsD' …) + Tick.cost(Tick.ret) 
            = 1 + cost(fold) + 0 *)
    unfold glue_cost_const_1, glue_cost_const_2.
    simpl depth.
    nia.
  
  (* === Case 2: s1 = Unit x === *)
  - intros A0 x B0 LDB0 Refl0 EAB0 as_ s2 outD Happrox Hlen.
    Local Opaque foldr_fconsD' foldl_fsnocD' fconsD' fsnocD'.
    cbn [glueD'].
    destruct s2 as [| y | u2 m2 v2].
    + (* s2 = Nil: foldl_fsnocD' as_ (Unit x) *)
      cbn [glue] in Happrox.
      pose proof (@foldl_fsnocD'_cost A0 B0 _ _ _ as_ (Unit x) outD Happrox) as Hfold.
      simpl Tick.cost.
      unfold glue_cost_const_1, glue_cost_const_2.
      simpl depth.
      simpl.
      (* Step 1: Simplify depth *)
      simpl depth in Hfold.

      (* Step 2: Bound Hfold using Hlen *)
      assert (Hfold' : Tick.cost (foldl_fsnocD' as_ (Unit x) outD) <= 30).
      { etransitivity; [exact Hfold | ]. nia. }

      lia.
    + (* s2 = Unit y: foldr_fconsD' (x :: as_) (Unit y) *)
      cbn [glue] in Happrox.
      pose proof (@foldr_fconsD'_cost A0 B0 _ _ _ (x :: as_) (Unit y) outD Happrox) as Hfold.
      simpl Tick.cost.
      simpl depth in Hfold |- *.
      unfold glue_cost_const_1, glue_cost_const_2.
      assert (Hfold' : Tick.cost (foldr_fconsD' (x :: as_) (Unit y) outD) <= 48).
      { 
        etransitivity; [exact Hfold | ]. simpl in *. nia. 
      }
      lia.

    + (* s2 = More u2 m2 v2: foldr_fconsD' (x :: as_) (More u2 m2 v2) *)
      cbn [glue] in Happrox.
      pose proof (@foldr_fconsD'_cost A0 B0 _ _ _ (x :: as_) (More u2 m2 v2) outD Happrox) as Hfold.
      simpl Tick.cost.
      simpl depth in Hfold |- *.
      unfold glue_cost_const_1, glue_cost_const_2.
      assert (Hlen' : S (length as_) <= 4) by lia.
      assert (Hfold' : Tick.cost (foldr_fconsD' (x :: as_) (More u2 m2 v2) outD) <= 56 + 8 * depth m2).
      { 
        etransitivity; [exact Hfold | ]. simpl in *. nia. 
      }
      lia.
  
  (* === Case 3: s1 = More u1 m1 v1 === *)
  - intros A0 u1 m1 v1 IHm1 B0 LDB0 Refl0 EAB0 as_ s2 outD Happrox Hlen.
    Local Opaque foldr_fconsD' foldl_fsnocD' fconsD' fsnocD' glueD'.
    cbn [glueD'].
    destruct s2 as [| y | u2 m2 v2].
    + (* s2 = Nil *)
      cbn [glue] in Happrox.
      pose proof (@foldl_fsnocD'_cost A0 B0 _ _ _ as_ (More u1 m1 v1) outD Happrox) as Hfold.
      simpl Tick.cost.
      simpl depth in Hfold |- *.
      unfold glue_cost_const_1, glue_cost_const_2.
      assert (Hfold' : Tick.cost (foldl_fsnocD' as_ (More u1 m1 v1) outD) <= 36 + 6 * depth m1).
      { 
        etransitivity; [exact Hfold | ]. nia. 
      }
      lia.
    + (* s2 = Unit y *)
      cbn [glue] in Happrox.
      pose proof (@foldl_fsnocD'_cost A0 B0 _ _ _ (as_ ++ [y]) (More u1 m1 v1) outD Happrox) as Hfold.
      rewrite List.app_length in Hfold. simpl List.length in Hfold.
      simpl Tick.cost.
      simpl depth in Hfold |- *.
      unfold glue_cost_const_1, glue_cost_const_2.
      assert (Hlen' : length as_ + 1 <= 4) by lia.
      assert (Hfold' : Tick.cost (foldl_fsnocD' (as_ ++ [y]) (More u1 m1 v1) outD) <= 56 + 8 * depth m1).
      { 
        etransitivity; [exact Hfold | ]. nia. 
      }
      lia.
    + (* s2 = More u2 m2 v2 — DEEP CASE *)
      destruct outD as [| | u1D m'D v2D ].
      * (* outD = NilA: but outD ≤ exact (More …), contradiction *)
        cbn [glue] in Happrox. inversion Happrox.
      * (* outD = UnitA: similar contradiction *)
        cbn [glue] in Happrox. inversion Happrox.
      * (* outD = MoreA u1D m'D v2D *)
        (* Cost = 1 (outer tick) + cost(glueD' m1 (toTuples …) m2 m'D_forced) + 0 *)
        cbn [glue] in Happrox.
        invert_clear Happrox as [| | ? ? ? ? ? ? Hu1 Hm Hv2].
        (* Hm : m'D ≤ exact (glue m1 (toTuples …) m2) *)
        set (middle := toTuples (digitToList v1 ++ as_ ++ digitToList u2)) in *.
        set (m'D_forced := match m'D with
                           | Thunk q => q
                           | Undefined => bottom_of (exact (glue m1 middle m2))
                           end) in *.
        assert (Hm_forced : m'D_forced `is_approx` glue m1 middle m2).
        {
          unfold m'D_forced. destruct m'D as [ q | ] eqn:Eq.
          - invert_clear Hm. assumption.
          - apply bottom_is_least. reflexivity.
        }
        assert (Hmiddle_len : List.length middle <= 3).
        {
          unfold middle. apply toTuples_length_bound.
          rewrite !List.app_length.
          destruct v1, u2; simpl; lia.
        }
        specialize (IHm1 _ _ _ _ middle m2 m'D_forced Hm_forced Hmiddle_len).
        (* IHm1 : Tick.cost (glueD' m1 middle m2 m'D_forced) ≤ 8 * (depth m1 + depth m2) + 60 *)
        simpl Tick.cost.
        simpl depth.
        unfold glue_cost_const_1, glue_cost_const_2 in *.
        simpl.

        (* Goal: 1 + Tick.cost (glueD' m1 middle m2 m'D_forced) + 0 ≤ 8 * (S(depth m1) + S(depth m2)) + 60 
                = 8 * depth m1 + 8 * depth m2 + 16 + 60 = 8 * (depth m1 + depth m2) + 76. *)
        (* Destructure the Tick.val to expose the let *)
        destruct (Tick.val (glueD' m1 middle m2 m'D_forced)) as [ [m1D middleD] m2D] eqn:Eval.
        simpl Tick.cost.
        lia.
Qed.


(** *** Corollary: cost of top-level [concat]. *)
Corollary concatD_cost (A : Type) `{LDA: LessDefined A, Hrefl: !Reflexive LDA} (q1 q2 : Seq A) (outD : SeqA A) :
  outD `is_approx` concat q1 q2 ->
  Tick.cost (concatD q1 q2 outD) <=
    glue_cost_const_1 * (depth q1 + depth q2) + glue_cost_const_2.
Proof.
  intros Happrox.
  unfold concatD.
  apply (@glueD'_cost A _ A LDA Hrefl _).
  - exact Happrox.
  - simpl. lia.
Qed.


(** *** Asymptotic statement (informal, for thesis reference)

    For all finite [q1, q2 : Seq A]:
      Tick.cost (concatD q_1 q_2 outD) = O(log(|q_1| + |q_2|)).
    
    Proof: by [concatD_cost], cost ≤ 8 * (depth q_1 + depth q_2) + 60.
    By the size-depth relation [depth q ≤ log_3 |q|], we have
      depth q_1 + depth q_2 ≤ log_3 |q_1| + log_3 |q_2| = log_3 (|q_1| * |q_2|).
    For nontrivial inputs, this is bounded by 2 * log_3 (|q_1| + |q_2|).
    Hence cost = O(log(|q_1| + |q_2|)). *)


(* ================================================================= *)
(** ** Section 6: Future work — demand correctness & spec              *)
(* ================================================================= *)

(** These are placeholders for the full demand-side machinery, NOT
    needed for Claim 1.  Each requires a correct [unbundle], and the
    spec additionally requires extensive proofs analogous to
    [ftailD'_spec].  Left as future work; see [claim1_design.md] for
    scope rationale. *)


(** *** [glueD'_approx]: the demand approximates the inputs. *)
(* Lemma glueD'_approx : forall (A B : Type)
    `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (s1 : Seq A) (as_ : list A) (s2 : Seq A) (outD : SeqA B),
    outD `is_approx` glue s1 as_ s2 ->
    let '(s1D, asD, s2D) := Tick.val (glueD' s1 as_ s2 outD) in
    s1D `less_defined` exact s1 /\
    Forall2 less_defined asD (List.map exact as_) /\
    s2D `less_defined` exact s2.
Proof.
  (* Requires correct unbundle.  Not needed for Claim 1. *)
Admitted. *)


(** *** [glueD'_exact]: full-demand case. *)
(* Lemma glueD'_exact (A B : Type) `{Exact A B}
    (s1 : Seq A) (as_ : list A) (s2 : Seq A) :
  let '(s1D, asD, s2D) := Tick.val (glueD' s1 as_ s2 (exact (glue s1 as_ s2))) in
  s1D = exact s1 /\
  asD = List.map exact as_ /\
  s2D = exact s2.
Proof.
  (* Requires correct unbundle.  Not needed for Claim 1. *)
Admitted. *)


#[local] Existing Instance Reflexive_LessDefined_T.
#[local] Existing Instance Reflexive_LessDefined_prodA.

(** *** [glueD'_spec]: clairvoyant dominates demand. *)
(* Lemma glueD'_spec (A B : Type) :
  forall `{LDB : LessDefined B, !Reflexive LDB, !Transitive LDB, Exact A B}
    (s1 : Seq A) (as_ : list A) (s2 : Seq A) (outD : SeqA B),
    outD `is_approx` glue s1 as_ s2 ->
    forall s1D asD s2D,
      (s1D, asD, s2D) = Tick.val (glueD' s1 as_ s2 outD) ->
      let dcost := Tick.cost (glueD' s1 as_ s2 outD) in
      glueA s1D asD s2D
      [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  (* Requires correct unbundle + glueA'_mon.  Not needed for Claim 1. *)
Admitted. *)


(* ================================================================= *)
(** ** End of FingerConcat                                              *)
(* ================================================================= *)
