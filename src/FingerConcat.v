(** * FingerConcat — Claessen's [glue] / concatenation operation

    This file implements the concatenation operation for the simplified
    finger tree, following Claessen 2020 §7.

    Unlike [fcons]/[fsnoc]/[ftail] (amortized constant), [glue] is
    **worst-case** logarithmic.  No new debit machinery is needed:
    [Debitable_T], [Debitable_SeqA], [safe_DigitA], [safe_T], and their
    sub-additivity lemmas live in [FingerCore.v].

    Structure:
      Section 1: Pure helpers ([digitToList], [toTuples]).
      Section 2: Pure [glue] function + custom induction principle.
      Section 3: Clairvoyant [glueA'] + monotonicity helpers.
      Section 4: Demand function [glueD'].
      Section 5: Cost lemma [glueD'_cost] and corollary [concatD_cost].
      Section 6: Demand-correctness [glueD'_approx] (proved, axiom-free)
                 and the asymptotic [O(log n)] corollary.
      Section 7: Full specification [glueD'_spec] — IN PROGRESS.

    SCOPE: this is the single canonical concat development (it supersedes
    [FingerConcatAlt.v], which is being retired).  Fully proved and
    closed under the global context (axiom-free): the worst-case
    [O(log n)] cost bound on [concat] (Claim 1), and the demand-
    approximation obligation [glueD'_approx] / [concatD_approx], resting
    on the faithful [unbundle] inverse (agreement: [tupleArities_spec]).

    The demand function [glueD'] now records the *real* element demands in
    every arm (the deep arm via [unbundle]; the fold arms via
    [foldr_fcons_elems] / [foldl_fsnoc_elems], whose per-element demands are
    read off [outD] by [fcons_elemD] / [fsnoc_elemD]).  This is what makes
    [glueD'_spec] true at all: the earlier cost-only [glueD'] discarded those
    demands ([asD = map (fun _ => Undefined) as_]), so no clairvoyant run
    could reconstruct an [outD] that demanded a middle element.

    OPEN OBLIGATION (still [Admitted], the work of branch [concat-continue]):
    the full unbundled specification [glueD'_spec] (demand reconstruction +
    cost agreement).  Its kernel is the single-step lemma [fconsA_elemD_step]
    (extracted element demand + any [q >= spine demand] reconstructs [outD]);
    the deep [More]/[More] arm needs the [IHm] + [glueA'_mon] + [unbundle]
    roundtrip lockstep.  Nothing else depends on it, so the axiom-free
    results above are unaffected.  *)

From Coq Require Import Arith Psatz Relations RelationClasses List.
From Clairvoyance Require Import Core Approx ApproxM Tick Prod Option.
From Hammer Require Import Tactics.
From Clairvoyance Require Import FingerCore FingerCons FingerSnoc FingerSize.

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

Lemma digitToListA_mon (A : Type) `{LessDefined A} (d1 d2 : DigitA A) :
  d1 `less_defined` d2 ->
  Forall2 less_defined (digitToListA d1) (digitToListA d2).
Proof.
  intro Hd; invert_clear Hd; cbn [digitToListA];
    repeat first [ apply Forall2_cons | apply Forall2_nil ]; assumption.
Qed.

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

Local Opaque fconsA fsnocA toTuplesA.

Lemma glueA'_mon :
  forall (A : Type) (q1 : SeqA A),
  forall `{LDA : LessDefined A, !PreOrder LDA}
         (q1' : SeqA A) (as'_ as_ : list (T A)) (q2' q2 : SeqA A),
    q1' `less_defined` q1 ->
    Forall2 less_defined as'_ as_ ->
    q2' `less_defined` q2 ->
    glueA' q1' as'_ q2' `less_defined` glueA' q1 as_ q2.
Proof.
  apply (SeqA_ind
    (fun A q1 =>
       forall `{LDA : LessDefined A, !PreOrder LDA}
              (q1' : SeqA A) (as'_ as_ : list (T A)) (q2' q2 : SeqA A),
         q1' `less_defined` q1 ->
         Forall2 less_defined as'_ as_ ->
         q2' `less_defined` q2 ->
         glueA' q1' as'_ q2' `less_defined` glueA' q1 as_ q2)).

  (* ===== q1 = NilA ===== *)
  - intros A0 LDA0 PA0 q1' as'_ as_ q2' q2 Hq1 Has Hq2.
    invert_clear Hq1.                          (* q1' = NilA *)
    cbn -[glueA']. apply tick_mon.
    apply fold_fconsA_mon; [ exact Has | apply ret_mon; exact Hq2 ].

  (* ===== q1 = UnitA x ===== *)
  - intros A0 x LDA0 PA0 q1' as'_ as_ q2' q2 Hq1 Has Hq2.
    invert_clear Hq1 as [ | x1 ? Hx | ].        (* q1' = UnitA x1, Hx : x1 ≤ x *)
    inversion Hq2 as [ | y1 y2 Hy | fa fb ma mb ra rb Hfa Hma Hra ]; subst.
    + (* q2 = NilA : fold_left fsnoc over as_, base ret (UnitA x1) *)
      cbn -[glueA']. apply tick_mon.
      apply fold_fsnocA_mon; [ exact Has | apply ret_mon; constructor; exact Hx ].
    + (* q2 = UnitA y : fold_right fcons over x1::as_, base ret q2 *)
      cbn -[glueA']. apply tick_mon.
      apply fold_fconsA_mon;
        [ apply Forall2_cons; [ exact Hx | exact Has ] | apply ret_mon; exact Hq2 ].
    + (* q2 = MoreA … : same UnitA-front arm *)
      cbn -[glueA']. apply tick_mon.
      apply fold_fconsA_mon;
        [ apply Forall2_cons; [ exact Hx | exact Has ] | apply ret_mon; exact Hq2 ].

  (* ===== q1 = MoreA fD2 mD2 rD2 ===== *)
  - intros A0 fD2 mD2 rD2 IH LDA0 PA0 q1' as'_ as_ q2' q2 Hq1 Has Hq2.
    invert_clear Hq1 as [ | | f1 ? m1 ? r1 ? Hf Hm Hr ].
        (* q1' = MoreA f1 m1 r1;  Hf : f1≤fD2,  Hm : m1≤mD2,  Hr : r1≤rD2 *)
    inversion Hq2 as [ | y1 y2 Hy | fa fb ma mb ra rb Hfa Hma Hra ]; subst.

    + (* q2 = NilA : fold_left fsnoc over as_, base ret (MoreA f1 m1 r1) *)
      cbn -[glueA']. apply tick_mon.
      apply fold_fsnocA_mon;
        [ exact Has | apply ret_mon; constructor; [ exact Hf | exact Hm | exact Hr ] ].

    + (* q2 = UnitA y : fold_left fsnoc over as_ ++ [y], base ret (MoreA f1 m1 r1) *)
      cbn -[glueA']. apply tick_mon.
      apply fold_fsnocA_mon.
      * apply Forall2_app;
          [ exact Has | apply Forall2_cons; [ exact Hy | apply Forall2_nil ] ].
      * apply ret_mon; constructor; [ exact Hf | exact Hm | exact Hr ].

    + (* q2 = MoreA fb mb rb : the deep recursive arm *)
      cbn -[glueA']. cbv zeta.          (* expose `tuples := toTuplesA (…)` from the let *)
      apply tick_mon.
      apply bind_mon; [ solve_mon | intros v1a v1b Hv1 ].   (* force rD1 = r1 vs rD2 *)
      apply bind_mon; [ solve_mon | intros u2a u2b Hu2 ].   (* force fD2 = fa vs fb *)
      destruct mD2 as [ md2_inner | ].

      * (* mD2 = Thunk md2_inner *)
        inversion IH as [x IH_inner Heq | Haux]; subst.
            (* IH_inner :  forall q1' as'_ as_ q2' q2,
                 q1' ≤ md2_inner -> Forall2 as'_ as_ -> q2' ≤ q2 ->
                 glueA' q1' as'_ q2' ≤ glueA' md2_inner as_ q2 *)
        invert_clear Hm.

        -- (* m1 = Undefined : LHS middle is bottom *)
           cbn -[glueA']. solve_mon.

        -- (* m1 = Thunk x ,  with  (x ≤ md2_inner) in context *)
           cbn -[glueA'].
           apply bind_mon.
           ++ apply thunk_mon.
              apply forcing_mon; [ exact Hma | intros m2a m2b Hm2 ].
              apply IH_inner.
              ** typeclasses eauto. 
              ** assumption. (* x ≤ md2_inner *)
              ** apply toTuplesA_mon.
                 apply Forall2_app; [ apply digitToListA_mon; exact Hv1 | ].
                 apply Forall2_app; [ exact Has | apply digitToListA_mon; exact Hu2 ].
              ** exact Hm2.
           ++ intros t1 t2 Ht. apply ret_mon.
              constructor; [ exact Hf | exact Ht | exact Hra ].

      * (* mD2 = Undefined : Hm forces m1 = Undefined; both middles bottom *)
        invert_clear Hm.
        cbn -[glueA']. solve_mon.
Qed.

Lemma glueA_mon (A : Type) `{LDA : LessDefined A, PreOrder A LDA}
    (q1' q1 : T (SeqA A)) (as'_ as_ : list (T A)) (q2' q2 : T (SeqA A)) :
    q1' `less_defined` q1 ->
    Forall2 less_defined as'_ as_ ->
    q2' `less_defined` q2 ->
    glueA q1' as'_ q2' `less_defined` glueA q1 as_ q2.
Proof.
  intros Hq1 Has Hq2. unfold glueA.
  apply forcing_mon; [ exact Hq1 | intros s1' s1 Hs1 ].
  apply forcing_mon; [ exact Hq2 | intros s2' s2 Hs2 ].
  apply glueA'_mon; assumption.
Qed.

Local Transparent fconsA fsnocA toTuplesA.


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
(** *** Arity of a single tuple (number of elements it bundles). *)
Definition tupleArity {A : Type} (t : Tuple A) : nat :=
  match t with
  | Pair _ _     => 2
  | Triple _ _ _ => 3
  end.

(** *** [tupleArities n]: the widths [toTuples] assigns to a length-[n] list.

    Mirrors [toTuples]'s greedy bundling (Triple-first, with a length-4
    tail giving two Pairs).  Depends only on [n], so it is recoverable
    from the three length arguments even when the tuple demands are
    [Undefined].  Recursion peels 3 (one Triple) per step; the inner
    match catches the length-4 tail. *)
Fixpoint tupleArities (n : nat) : list nat :=
  match n with
  | S (S (S m)) =>
      match m with
      | S O => [2; 2]               (* n = 4 : two Pairs, no Triple *)
      | _   => 3 :: tupleArities m  (* n = 3 or n >= 5 : peel a Triple *)
      end
  | S (S O) => [2]                  (* n = 2 : one Pair *)
  | _       => []                   (* n = 0 or 1 (1 is degenerate) *)
  end.

(** *** Expand one tuple-demand to its element-demands.

    When the demand is a concrete [PairA]/[TripleA] its width is
    self-evident; when it is [Undefined] we emit [k] [Undefined]
    element-demands, where [k] is the arity known from position. *)
Definition unbundleTuple {B : Type} (k : nat) (t : T (TupleA B)) : list (T B) :=
  match t with
  | Thunk (PairA a b)     => [a; b]
  | Thunk (TripleA a b c) => [a; b; c]
  | Undefined             => List.repeat Undefined k
  end.

(** *** Rebuild a digit-demand from a length-1..3 element-demand list. *)
Definition listToDigitA {B : Type} (l : list (T B)) : T (DigitA B) :=
  match l with
  | [a]       => Thunk (OneA a)
  | [a; b]    => Thunk (TwoA a b)
  | [a; b; c] => Thunk (ThreeA a b c)
  | _         => Undefined   (* length 0 or >3: unreachable for v1/u2 *)
  end.

(** *** [unbundle]: split a tuple-level middle demand back into demands on
    [v1] (a digit), [as_] (a flat list), and [u2] (a digit).

    Expand each tuple to its known arity, concatenate, then cut at the
    [v1]/[as_]/[u2] boundaries.  Total — graceful on malformed input;
    the approximation lemma (Piece 3) supplies the hypotheses under which
    the slices land exactly. *)
Definition unbundle {B : Type}
    (tuplesD : list (T (TupleA B)))
    (n_v1 n_as n_u2 : nat)
    : T (DigitA B) * list (T B) * T (DigitA B) :=
  let n    := n_v1 + n_as + n_u2 in
  let flat := List.concat
                (List.map (fun '(k, t) => unbundleTuple k t)
                          (List.combine (tupleArities n) tuplesD)) in
  let v1D  := listToDigitA (List.firstn n_v1 flat) in
  let asD  := List.firstn n_as (List.skipn n_v1 flat) in
  let u2D  := listToDigitA (List.skipn (n_v1 + n_as) flat) in
  (v1D, asD, u2D).

Arguments unbundle : simpl never.

(** Boundary correctness: the expanded element list has length [n], so
    [firstn]/[skipn] at [n_v1] and [n_v1+n_as] hit the digit/list seams. *)
Lemma tupleArities_sum : forall n,
  2 <= n <= 9 -> List.fold_right Nat.add 0 (tupleArities n) = n.
Proof.
  intros n [Hlo Hhi].
  do 10 (destruct n; [ first [ reflexivity | lia ] | ]).
  lia.
Qed.

(** Agreement with [toTuples]: the recomputed arities are exactly the
    widths [toTuples] produced — element-type-agnostic, so it holds for
    the recursive [Tuple A] level too.  The round trip in Piece 3 hinges
    on this being the *same* arity list [toTuples] used. *)
Lemma tupleArities_spec : forall (X : Type) (l : list X),
  List.length l <= 9 ->
  tupleArities (List.length l) = List.map tupleArity (toTuples l).
Proof.
  intros X l Hlen.
  destruct l as [|?]; [reflexivity |].
  destruct l as [|?]; [reflexivity |].
  destruct l as [|?]; [reflexivity |].
  destruct l as [|?]; [reflexivity |].
  destruct l as [|?]; [reflexivity |].
  destruct l as [|?]; [reflexivity |].
  destruct l as [|?]; [reflexivity |].
  destruct l as [|?]; [reflexivity |].
  destruct l as [|?]; [reflexivity |].
  cbn in Hlen.
  assert (Hlen': length l <= 0) by lia.
  assert (Hlen'': length l = 0) by lia.
  assert (Hl : l = []).
  {
    destruct l.
    + reflexivity.
    + simpl in Hlen''. discriminate. 
  }
  simpl. rewrite Hlen''. simpl. rewrite Hl. simpl. reflexivity.
Qed.


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


(** *** Per-element demand extraction for the fold arms.

    [fconsD'] / [fsnocD'] compute the demand on the input element [x] but
    discard it, returning only the spine demand.  For the [glueD'_spec]
    direction we need those element demands back: they populate [asD] so the
    clairvoyant fold can reconstruct [outD].  [fcons_elemD] reads the demand on
    the front element of [fcons x s] straight out of [outD] (its position
    depends only on the front digit of [s], exactly as in [fconsD']);
    [fsnoc_elemD] does the dual at the rear. *)

Definition fcons_elemD {A B : Type} `{Exact A B} (s : Seq A) (outD : SeqA B) : T B :=
  match s, outD with
  | Nil,                    UnitA xD                          => xD
  | Unit _,                 MoreA (Thunk (OneA xD)) _ _       => xD
  | More (One _) _ _,       MoreA (Thunk (TwoA xD _)) _ _     => xD
  | More (Two _ _) _ _,     MoreA (Thunk (ThreeA xD _ _)) _ _ => xD
  | More (Three _ _ _) _ _, MoreA (Thunk (TwoA xD _)) _ _     => xD
  | _, _ => Undefined
  end.

Definition fsnoc_elemD {A B : Type} `{Exact A B} (s : Seq A) (outD : SeqA B) : T B :=
  match s, outD with
  | Nil,                    UnitA xD                          => xD
  | Unit _,                 MoreA _ _ (Thunk (OneA xD))       => xD
  | More _ _ (One _),       MoreA _ _ (Thunk (TwoA _ xD))     => xD
  | More _ _ (Two _ _),     MoreA _ _ (Thunk (ThreeA _ _ xD)) => xD
  | More _ _ (Three _ _ _), MoreA _ _ (Thunk (TwoA _ xD))     => xD
  | _, _ => Undefined
  end.

(** Element-demand lists, threaded identically to [foldr_fconsD'] /
    [foldl_fsnocD'].  Pure (no [Tick]) so they add no cost to [glueD']. *)

Fixpoint foldr_fcons_elems (A B : Type) `{Exact A B}
    (as_ : list A) (s_2 : Seq A) (outD : SeqA B) : list (T B) :=
  match as_ with
  | [] => []
  | x :: as' =>
      let s := List.fold_right fcons s_2 as' in
      let xD := fcons_elemD s outD in
      let innerD := Tick.val (fconsD' x s outD) in
      let innerD_forced := match innerD with
                           | Thunk q => q
                           | Undefined => bottom_of (exact s)
                           end in
      xD :: foldr_fcons_elems as' s_2 innerD_forced
  end.

Fixpoint foldl_fsnoc_elems (A B : Type) `{Exact A B}
    (as_ : list A) (s_1 : Seq A) (outD : SeqA B) {struct as_} : list (T B) :=
  match as_ with
  | [] => []
  | x :: as' =>
      let innerD := Tick.val (foldl_fsnocD' as' (fsnoc s_1 x) outD) in
      let innerD_forced := match innerD with
                           | Thunk q => q
                           | Undefined => bottom_of (exact (fsnoc s_1 x))
                           end in
      let xD := fsnoc_elemD s_1 innerD_forced in
      xD :: foldl_fsnoc_elems as' (fsnoc s_1 x) outD
  end.


(** *** [glueD']: the demand function for [glue].

    Six cases mirroring [glue]'s structure.  The deep case uses
    [unbundle] to split the recursive middle demand back into demands on
    [v1], [as_], [u2]; the fold arms recover their element demands via
    [foldr_fcons_elems] / [foldl_fsnoc_elems]. *)
Fixpoint glueD' (A B : Type) `{Exact A B}
    (s1 : Seq A) (as_ : list A) (s2 : Seq A) (outD : SeqA B)
    {struct s1} : Tick (T (SeqA B) * list (T B) * T (SeqA B)) :=
  Tick.tick >>
  match s1, s2 with
  | Nil, _ =>
      (* glue Nil as_ s_2 = foldr fcons s_2 as_ *)
      let+ s2D := foldr_fconsD' as_ s2 outD in
      Tick.ret (Thunk NilA, foldr_fcons_elems as_ s2 outD, s2D)

  | Unit x, Nil =>
      (* glue (Unit x) as_ Nil = foldl fsnoc (Unit x) as_ *)
      let+ s1D := foldl_fsnocD' as_ (Unit x) outD in
      Tick.ret (s1D, foldl_fsnoc_elems as_ (Unit x) outD, Thunk NilA)

  | More u1 m1 v1, Nil =>
      (* glue (More u_1 m_1 v_1) as_ Nil = foldl fsnoc (More u_1 m_1 v_1) as_ *)
      let+ s1D := foldl_fsnocD' as_ (More u1 m1 v1) outD in
      Tick.ret (s1D, foldl_fsnoc_elems as_ (More u1 m1 v1) outD, Thunk NilA)

  | Unit x, _ =>
      (* glue (Unit x) as_ s_2 = foldr fcons s_2 (x :: as_).
         The head element demand is [x]'s (it becomes the [UnitA] content);
         the tail is the demand on [as_]. *)
      let+ s2D := foldr_fconsD' (x :: as_) s2 outD in
      match foldr_fcons_elems (x :: as_) s2 outD with
      | xD :: asD => Tick.ret (Thunk (UnitA xD), asD, s2D)
      | []        => Tick.ret (Thunk (UnitA Undefined), [], s2D)
      end

  | More u1 m1 v1, Unit y =>
      (* glue (More u_1 m_1 v_1) as_ (Unit y) = foldl fsnoc (More u_1 m_1 v_1) (as_ ++ [y]).
         The first [|as_|] element demands are [as_]'s; the last is [y]'s (it
         becomes the [UnitA] content of [s2D]). *)
      let+ s1D := foldl_fsnocD' (as_ ++ [y]) (More u1 m1 v1) outD in
      let elemsD := foldl_fsnoc_elems (as_ ++ [y]) (More u1 m1 v1) outD in
      Tick.ret (s1D, List.firstn (List.length as_) elemsD,
                Thunk (UnitA (List.nth (List.length as_) elemsD Undefined)))

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

Lemma foldr_fconsD'_approx (A B : Type) `{LDB: LessDefined B, !Reflexive LDB, Exact A B}
    (as_ : list A) (s_2 : Seq A) (outD : SeqA B) :
  outD `is_approx` List.fold_right fcons s_2 as_ ->
  Tick.val (foldr_fconsD' as_ s_2 outD) `is_approx` s_2.
Proof.
  revert outD.
  induction as_ as [| x as' IH]; intros outD Happrox.

  - (* Base: foldr_fconsD' [] s_2 outD = Tick.ret (Thunk outD).
       Need Thunk outD ≤ exact s_2.  Happrox : outD ≤ exact (foldr fcons s_2 []) = exact s_2. *)
    simpl. constructor. exact Happrox.

  - (* Step: foldr_fconsD' (x :: as') s_2 outD =
       let+ innerD := fconsD' x (foldr fcons s_2 as') outD in
       foldr_fconsD' as' s_2 innerD_forced.
       Goal: Tick.val (that) ≤ exact s_2.
       Strategy: derive innerD_forced ≤ exact (foldr fcons s_2 as') from fconsD'_approx,
       then IH gives Tick.val (foldr_fconsD' as' s_2 innerD_forced) ≤ exact s_2. *)

    cbn [List.fold_right] in Happrox.
    (* Happrox : outD ≤ exact (fcons x (foldr fcons s_2 as')) *)

    Local Opaque fconsD'.
    cbn [foldr_fconsD'].

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

    specialize (IH innerD_forced Hinner_approx).
    (* IH : Tick.val (foldr_fconsD' as' s_2 innerD_forced) ≤ exact s_2 *)

    simpl Tick.val.
    change (match Tick.val (fconsD' x (List.fold_right fcons s_2 as') outD) with
            | Thunk q => q
            | Undefined => bottom_of (exact (List.fold_right fcons s_2 as'))
            end) with innerD_forced.

    exact IH.
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

(** *** The extracted element demands under-approximate their elements.

    These discharge the [asD] component of [glueD'_approx] now that the fold
    arms record real demands instead of [Undefined]. *)

Ltac invert_ld_struct :=
  repeat (match goal with
          | Hd : (UnitA _)      `less_defined` _ |- _ => invert_clear Hd
          | Hd : (MoreA _ _ _)  `less_defined` _ |- _ => invert_clear Hd
          | Hd : (OneA _)       `less_defined` _ |- _ => invert_clear Hd
          | Hd : (TwoA _ _)     `less_defined` _ |- _ => invert_clear Hd
          | Hd : (ThreeA _ _ _) `less_defined` _ |- _ => invert_clear Hd
          | Hd : (Thunk _)      `less_defined` _ |- _ => invert_clear Hd
          end).

Lemma fcons_elemD_approx (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (x : A) (s : Seq A) (outD : SeqA B) :
  outD `is_approx` fcons x s ->
  fcons_elemD s outD `less_defined` exact x.
Proof.
  intro Happrox. cbn [fcons] in Happrox.
  destruct s as [ | y | [a|a b|a b c] m r ];
    destruct outD as [ | xD | fD mD rD ];
    try (destruct fD as [ [ x1 | x1 x2 | x1 x2 x3 ] | ]);
    cbn [fcons_elemD];
    try solve [ constructor ];
    invert_ld_struct; try assumption; try solve [ constructor ].
Qed.

Lemma fsnoc_elemD_approx (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (x : A) (s : Seq A) (outD : SeqA B) :
  outD `is_approx` fsnoc s x ->
  fsnoc_elemD s outD `less_defined` exact x.
Proof.
  intro Happrox. cbn [fsnoc] in Happrox.
  destruct s as [ | y | f m [a|a b|a b c] ];
    destruct outD as [ | xD | fD mD rD ];
    try (destruct rD as [ [ x1 | x1 x2 | x1 x2 x3 ] | ]);
    cbn [fsnoc_elemD];
    try solve [ constructor ];
    invert_ld_struct; try assumption; try solve [ constructor ].
Qed.

Lemma foldr_fcons_elems_approx (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (as_ : list A) (s_2 : Seq A) (outD : SeqA B) :
  outD `is_approx` List.fold_right fcons s_2 as_ ->
  Forall2 less_defined (foldr_fcons_elems as_ s_2 outD) (List.map exact as_).
Proof.
  revert s_2 outD.
  induction as_ as [| x as' IH]; intros s_2 outD Happrox.
  - simpl. constructor.
  - cbn [List.fold_right] in Happrox.
    cbn [foldr_fcons_elems List.map].
    set (s := List.fold_right fcons s_2 as') in *.
    constructor.
    + eapply fcons_elemD_approx; eauto.
    + apply IH.
      pose proof (@fconsD'_approx A B _ _ _ x s outD Happrox) as Hin.
      destruct (Tick.val (fconsD' x s outD)) as [ q | ] eqn:Eq.
      * cbn. invert_clear Hin. assumption.
      * cbn. apply bottom_is_least. reflexivity.
Qed.

Lemma foldl_fsnoc_elems_approx (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (as_ : list A) (s_1 : Seq A) (outD : SeqA B) :
  outD `is_approx` List.fold_left fsnoc as_ s_1 ->
  Forall2 less_defined (foldl_fsnoc_elems as_ s_1 outD) (List.map exact as_).
Proof.
  revert s_1 outD.
  induction as_ as [| x as' IH]; intros s_1 outD Happrox.
  - simpl. constructor.
  - cbn [List.fold_left] in Happrox.
    cbn [foldl_fsnoc_elems List.map].
    pose proof (@foldl_fsnocD'_approx A B _ _ _ as' (fsnoc s_1 x) outD Happrox) as Hin.
    assert (Hpre : (match Tick.val (foldl_fsnocD' as' (fsnoc s_1 x) outD) with
                    | Thunk q => q
                    | Undefined => bottom_of (exact (fsnoc s_1 x))
                    end) `is_approx` fsnoc s_1 x).
    { destruct (Tick.val (foldl_fsnocD' as' (fsnoc s_1 x) outD)) as [ q | ] eqn:Eq.
      - cbn. invert_clear Hin. assumption.
      - cbn. apply bottom_is_least. reflexivity. }
    constructor.
    + eapply fsnoc_elemD_approx; eauto.
    + apply IH. exact Happrox.
Qed.

(** NOTE: the old [foldr_fconsA_undef_spec] (clairvoyant fold over an
    all-[Undefined] middle dominates [outD]) was removed: it is *false*.
    Concretely, [glue Nil [a] Nil = Unit a] with [outD = UnitA (Thunk a)]
    demands the element [a], but the all-[Undefined] reconstruction can only
    produce [UnitA Undefined].  The fix was to make [glueD'] record the real
    element demands ([foldr_fcons_elems]); [glueD'_spec] now reconstructs
    [outD] from those via [fconsA_elemD_step] (work of [concat-continue]). *)

Lemma foldr_fconsD'_val_thunk (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (as_ : list A) (s_2 : Seq A) (outD : SeqA B) :
  exists q, Tick.val (foldr_fconsD' as_ s_2 outD) = Thunk q.
Proof.
  revert s_2 outD.
  induction as_ as [| x as' IH]; intros s_2 outD.
  - cbn [foldr_fconsD']. eexists. reflexivity.
  - cbn [foldr_fconsD'].
    (* foldr_fconsD' (x::as') = let+ innerD := fconsD' x … in foldr_fconsD' as' … innerD_forced.
       Tick.val of that = Tick.val (foldr_fconsD' as' … innerD_forced), a Thunk by IH. *)
    destruct (IH s_2 (match Tick.val (fconsD' x (List.fold_right fcons s_2 as') outD) with
                      | Thunk q => q
                      | Undefined => bottom_of (exact (List.fold_right fcons s_2 as'))
                      end)) as [q Hq].
    eexists. (* the bind's val reduces to the recursive call's val *)
    cbn [Tick.bind Tick.val]. (* expose the structure *)
    exact Hq.
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
    By the size-depth relation [depth q ≤ log_2 |q|] (see
    [depth_log_size] in [FingerSize.v]),
      depth q_1 + depth q_2 ≤ log_2 |q_1| + log_2 |q_2|.
    For nonempty inputs, [log_2 a + log_2 b ≤ 2 * log_2 (a + b)],
    so cost = O(log(|q_1| + |q_2|)). *)


(* ================================================================= *)
(** ** Section 6: Future work — demand correctness & spec              *)
(* ================================================================= *)

(** These are placeholders for the full demand-side machinery, NOT
    needed for Claim 1.  Each requires a correct [unbundle], and the
    spec additionally requires extensive proofs analogous to
    [ftailD'_spec].  Left as future work; see [claim1_proof.md] and
    [PROGRESS.md] in the repository root for scope rationale. *)

(** Pointwise: a list of [Undefined] demands approximates any exact list. *)
Lemma Forall2_map_Undefined {A B : Type} `{LessDefined B, Exact A B} (as_ : list A) :
  Forall2 less_defined
          (List.map (fun _ : A => @Undefined B) as_)
          (List.map exact as_).
Proof.
  induction as_ as [| a as' IH]; simpl.
  - constructor.
  - constructor.
    + apply LessDefined_Undefined. (* Undefined ≤ exact a *)
    + exact IH.
Qed.


Definition tupleToList {A : Type} (t : Tuple A) : list A :=
  match t with
  | Pair a b     => [a; b]
  | Triple a b c => [a; b; c]
  end.

Lemma toTuples_concat_id {A : Type} (L : list A) :
  2 <= List.length L <= 9 ->
  List.concat (List.map tupleToList (toTuples L)) = L.
Proof.
  intro Hlen.
  destruct L as [|?]; simpl in Hlen; try lia; try reflexivity.
  destruct L as [|?]; simpl in Hlen; try lia; try reflexivity.
  destruct L as [|?]; simpl in Hlen; try lia; try reflexivity.
  destruct L as [|?]; simpl in Hlen; try lia; try reflexivity.
  destruct L as [|?]; simpl in Hlen; try lia; try reflexivity.
  destruct L as [|?]; simpl in Hlen; try lia; try reflexivity.
  destruct L as [|?]; simpl in Hlen; try lia; try reflexivity.
  destruct L as [|?]; simpl in Hlen; try lia; try reflexivity.
  destruct L as [|?]; simpl in Hlen; try lia; try reflexivity.
  assert (Hl : length L = 0) by lia.
  assert (Hempty: L = []).
  {
    destruct L.
    - reflexivity.
    - simpl in Hl. discriminate.
  }
  simpl. repeat apply f_equal. rewrite Hempty. simpl. reflexivity.
Qed.

Lemma unbundleTuple_approx {A B : Type} `{LessDefined B, Exact A B}
    (t : T (TupleA B)) (tup : Tuple A) :
  t `less_defined` exact tup ->
  Forall2 less_defined (unbundleTuple (tupleArity tup) t)
                       (List.map exact (tupleToList tup)).
Proof.
  intro Ht.
  destruct tup as [ a b | a b c ]; simpl tupleArity; simpl tupleToList; simpl exact in Ht.
  - (* Pair a b: exact (Pair a b) = PairA (exact a) (exact b), arity 2 *)
    destruct t as [ q | ].
    + invert_clear Ht.   (* q = PairA …, fields ≤ exact a, exact b *)
      simpl. invert_clear H1. repeat (constructor; [ assumption | ]). constructor.
    + (* Undefined: unbundleTuple 2 Undefined = repeat Undefined 2 *)
      simpl. invert_clear Ht. 
      repeat (constructor; [ apply LessDefined_Undefined | ]). constructor.
  - (* Triple a b c: arity 3 *)
    destruct t as [ q | ].
    + invert_clear Ht.
      simpl. invert_clear H1. repeat (constructor; [ assumption | ]). constructor.
    + simpl. invert_clear Ht. repeat (constructor; [ apply LessDefined_Undefined | ]). constructor.
Qed.

Lemma listToDigitA_approx {A B : Type} `{LessDefined B, Exact A B}
    (l : list (T B)) (d : Digit A) :
  Forall2 less_defined l (List.map exact (digitToList d)) ->
  listToDigitA l `less_defined` exact d.
Proof.
  intro Hl.
  destruct d as [ a | a b | a b c ]; simpl digitToList in Hl; simpl exact.
  - (* One a: map exact [a] = [exact a]; l must be [d0] with d0 ≤ exact a *)
    inversion Hl as [| d0 e0 tl0 tle0 Hd0 Htl0 ]; subst.
    inversion Htl0; subst. simpl listToDigitA.
    constructor. constructor. exact Hd0.
  - inversion Hl as [| d0 e0 tl0 tle0 Hd0 Htl0 ]; subst.
    inversion Htl0 as [| d1 e1 tl1 tle1 Hd1 Htl1 ]; subst.
    inversion Htl1; subst. simpl listToDigitA.
    constructor. constructor; [ exact Hd0 | exact Hd1 ].
  - inversion Hl as [| d0 e0 tl0 tle0 Hd0 Htl0 ]; subst.
    inversion Htl0 as [| d1 e1 tl1 tle1 Hd1 Htl1 ]; subst.
    inversion Htl1 as [| d2 e2 tl2 tle2 Hd2 Htl2 ]; subst.
    inversion Htl2; subst. simpl listToDigitA.
    constructor. constructor; [ exact Hd0 | exact Hd1 | exact Hd2 ].
Qed.

Lemma unbundle_flat_approx {A B : Type} `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (L : list A) (middleD : list (T (TupleA B))) :
  2 <= List.length L <= 9 ->
  Forall2 less_defined middleD (List.map exact (toTuples L)) ->
  Forall2 less_defined
    (List.concat (List.map (fun '(k, t) => unbundleTuple k t)
                           (List.combine (tupleArities (List.length L)) middleD)))
    (List.map exact L).
Proof.
  intros Hlen HmD.
  assert (Harity : tupleArities (List.length L) = List.map tupleArity (toTuples L)).
  { 
    apply tupleArities_spec. 
    lia. 
  }
  rewrite Harity.
  (* Fold the RHS L into its tuple-reassembly.  L is a bare variable here, so the
     match is syntactic and instance-independent.  `at 2` targets the L under
     `map exact` (occurrence 1 is the L inside `toTuples L` on the left). *)
  replace L with (List.concat (List.map tupleToList (toTuples L))) at 2
    by (apply toTuples_concat_id; exact Hlen).
  rewrite concat_map, map_map.
  revert middleD HmD.
  generalize (toTuples L); intro TS.
  clear Hlen L Harity.
  induction TS as [| tup ts IHts]; intros middleD HmD.
  - inversion HmD; subst. simpl. constructor.
  - inversion HmD as [| d md tl_d tl_md Hd Htl ]; subst.
    simpl. apply Forall2_app.
    + apply unbundleTuple_approx. exact Hd.
    + apply IHts. exact Htl.
Qed.

Lemma Forall2_firstn {A B : Type} (R : A -> B -> Prop) (n : nat) :
  forall (l : list A) (l' : list B),
    Forall2 R l l' -> Forall2 R (List.firstn n l) (List.firstn n l').
Proof.
  induction n as [| n IHn]; intros l l' HF.
  - simpl. constructor.
  - destruct HF as [| x y l l' Hxy HF ].
    + simpl. constructor.
    + simpl. constructor; [ exact Hxy | apply IHn; exact HF ].
Qed.

Lemma Forall2_skipn {A B : Type} (R : A -> B -> Prop) (n : nat) :
  forall (l : list A) (l' : list B),
    Forall2 R l l' -> Forall2 R (List.skipn n l) (List.skipn n l').
Proof.
  induction n as [| n IHn]; intros l l' HF.
  - simpl. exact HF.
  - destruct HF as [| x y l l' Hxy HF ].
    + simpl. constructor.
    + simpl. apply IHn; exact HF.
Qed.

Lemma Forall2_nth {X Y : Type} (R : X -> Y -> Prop) :
  forall (l : list X) (l' : list Y) (n : nat) (dx : X) (dy : Y),
    Forall2 R l l' -> n < List.length l -> R (List.nth n l dx) (List.nth n l' dy).
Proof.
  intros l l' n dx dy HF. revert n.
  induction HF as [| x y l l' Hxy HF IH]; intros n Hn.
  - simpl in Hn. lia.
  - destruct n as [| n].
    + exact Hxy.
    + simpl. apply IH. simpl in Hn. lia.
Qed.

Lemma foldl_fsnoc_elems_length (A B : Type) `{Exact A B}
    (as_ : list A) (s_1 : Seq A) (outD : SeqA B) :
  List.length (foldl_fsnoc_elems as_ s_1 outD) = List.length as_.
Proof.
  revert s_1 outD. induction as_ as [| x as' IH]; intros s_1 outD.
  - reflexivity.
  - cbn [foldl_fsnoc_elems List.length]. f_equal. apply IH.
Qed.

Lemma firstn_nth_last {X : Type} :
  forall (l : list X) (n : nat) (d : X),
    List.length l = S n -> List.firstn n l ++ [List.nth n l d] = l.
Proof.
  induction l as [| a l IHl]; intros n d Hlen.
  - simpl in Hlen. discriminate.
  - destruct n as [| n].
    + simpl in Hlen. destruct l; [ reflexivity | simpl in Hlen; discriminate ].
    + simpl. f_equal. apply IHl. simpl in Hlen. lia.
Qed.

Lemma glueD'_approx :
  forall (A : Type) (s1 : Seq A)
         (B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
         (as_ : list A) (s2 : Seq A) (outD : SeqA B),
    List.length as_ <= 3 ->
    outD `is_approx` glue s1 as_ s2 ->
    let '(s1D, asD, s2D) := Tick.val (glueD' s1 as_ s2 outD) in
    s1D `less_defined` exact s1 /\
    Forall2 less_defined asD (List.map exact as_) /\
    s2D `less_defined` exact s2.
Proof.
  apply (Seq_ind_poly
    (fun (A : Type) (s1 : Seq A) =>
       forall (B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
              (as_ : list A) (s2 : Seq A) (outD : SeqA B),
         List.length as_ <= 3 ->
         outD `is_approx` glue s1 as_ s2 ->
         let '(s1D, asD, s2D) := Tick.val (glueD' s1 as_ s2 outD) in
         s1D `less_defined` exact s1 /\
         Forall2 less_defined asD (List.map exact as_) /\
         s2D `less_defined` exact s2)).

  (* =============================================================== *)
  (* === Case 1: s1 = Nil ===                                        *)
  (* =============================================================== *)
  - intros A0 B0 LDB0 Refl0 EAB0 as_ s2 outD Hlen_as Happrox.
    Local Opaque foldr_fconsD' foldl_fsnocD' foldr_fcons_elems foldl_fsnoc_elems.
    cbn [glueD']. cbv zeta.
    (* val = (Thunk NilA, map (fun _=>Undefined) as_, Tick.val (foldr_fconsD' as_ s2 outD)) *)
    cbn [glue] in Happrox.
    pose proof (@foldr_fconsD'_approx A0 B0 _ _ _ as_ s2 outD Happrox) as Hs2.
    simpl Tick.val.
    split; [ | split ].
    + (* Thunk NilA ≤ exact Nil *)
      apply LessDefined_Thunk. reflexivity.
    + apply (@foldr_fcons_elems_approx A0 B0 _ _ _ as_ s2 outD Happrox).
    + (* Tick.val (foldr_fconsD' as_ s2 outD) ≤ exact s2 *)
      exact Hs2.

  (* =============================================================== *)
  (* === Case 2: s1 = Unit x ===                                     *)
  (* =============================================================== *)
  - intros A0 x B0 LDB0 Refl0 EAB0 as_ s2 outD Hlen_as Happrox.
    Local Opaque foldr_fconsD' foldl_fsnocD' foldr_fcons_elems foldl_fsnoc_elems.
    destruct s2 as [ | y | u2 m2 v2 ].

    + (* s2 = Nil : arm 2, foldl_fsnocD' as_ (Unit x) *)
      cbn [glueD']. cbv zeta.
      cbn [glue] in Happrox.
      pose proof (@foldl_fsnocD'_approx A0 B0 _ _ _ as_ (Unit x) outD Happrox) as Hs1.
      simpl Tick.val.
      split; [ | split ].
      * exact Hs1.
      * apply (@foldl_fsnoc_elems_approx A0 B0 _ _ _ as_ (Unit x) outD Happrox).
      * apply LessDefined_Thunk. reflexivity.                              (* Thunk NilA ≤ exact Nil *)

    + (* s2 = Unit y : arm 4, foldr_fconsD' (x :: as_) (Unit y) *)
      cbn [glue] in Happrox.
      pose proof (@foldr_fconsD'_approx A0 B0 _ _ _ (x :: as_) (Unit y) outD Happrox) as Hs2.
      pose proof (@foldr_fcons_elems_approx A0 B0 _ _ _ (x :: as_) (Unit y) outD Happrox) as Helems.
      cbn [List.map] in Helems.
      cbn [glueD']. cbv zeta.
      destruct (foldr_fcons_elems (x :: as_) (Unit y) outD) as [ | xD asD' ] eqn:He.
      * inversion Helems.
      * invert_clear Helems.
        simpl Tick.val.
        split; [ | split ].
        -- (* Thunk (UnitA xD) ≤ exact (Unit x) *)
           constructor. constructor. assumption.
        -- assumption.
        -- exact Hs2.

    + (* s2 = More u2 m2 v2 : arm 4 again (same Unit-front branch) *)
      cbn [glue] in Happrox.
      pose proof (@foldr_fconsD'_approx A0 B0 _ _ _ (x :: as_) (More u2 m2 v2) outD Happrox) as Hs2.
      pose proof (@foldr_fcons_elems_approx A0 B0 _ _ _ (x :: as_) (More u2 m2 v2) outD Happrox) as Helems.
      cbn [List.map] in Helems.
      cbn [glueD']. cbv zeta.
      destruct (foldr_fcons_elems (x :: as_) (More u2 m2 v2) outD) as [ | xD asD' ] eqn:He.
      * inversion Helems.
      * invert_clear Helems.
        simpl Tick.val.
        split; [ | split ].
        -- (* Thunk (UnitA xD) ≤ exact (Unit x) *)
           constructor. constructor. assumption.
        -- assumption.
        -- exact Hs2.

  (* =============================================================== *)
  (* === Case 3: s1 = More f m r ===                                 *)
  (* =============================================================== *)
  - intros A0 f m r IHm B0 LDB0 Refl0 EAB0 as_ s2 outD Hlen_as Happrox.
    Local Opaque foldr_fconsD' foldl_fsnocD' foldr_fcons_elems foldl_fsnoc_elems.
    destruct s2 as [ | y | u2 m2 v2 ].

    + (* s2 = Nil : arm 3, foldl_fsnocD' as_ (More f m r) *)
      cbn [glueD']. cbv zeta.
      cbn [glue] in Happrox.
      pose proof (@foldl_fsnocD'_approx A0 B0 _ _ _ as_ (More f m r) outD Happrox) as Hs1.
      simpl Tick.val.
      split; [ | split ].
      * exact Hs1.
      * apply (@foldl_fsnoc_elems_approx A0 B0 _ _ _ as_ (More f m r) outD Happrox).
      * apply LessDefined_Thunk. reflexivity.                              (* Thunk NilA ≤ exact Nil *)

    + (* s2 = Unit y : arm 5, foldl_fsnocD' (as_ ++ [y]) (More f m r) *)
      cbn [glue] in Happrox.
      pose proof (@foldl_fsnocD'_approx A0 B0 _ _ _ (as_ ++ [y]) (More f m r) outD Happrox) as Hs1.
      pose proof (@foldl_fsnoc_elems_approx A0 B0 _ _ _ (as_ ++ [y]) (More f m r) outD Happrox) as Helems.
      rewrite List.map_app in Helems. cbn [List.map] in Helems.
      cbn [glueD']. cbv zeta.
      simpl Tick.val.
      split; [ | split ].
      * exact Hs1.
      * (* Forall2 (firstn |as_| elemsD) (map exact as_) *)
        pose proof (@Forall2_firstn (T B0) (T B0) less_defined (List.length as_) _ _ Helems) as Hfn.
        rewrite List.firstn_app in Hfn.
        rewrite List.map_length in Hfn.
        rewrite Nat.sub_diag in Hfn.
        cbn [List.firstn] in Hfn. rewrite List.app_nil_r in Hfn.
        set (lhsF := List.firstn (List.length as_)
                       (foldl_fsnoc_elems (as_ ++ [y]) (More f m r) outD)) in Hfn.
        rewrite List.firstn_all2 in Hfn by (rewrite List.map_length; lia).
        exact Hfn.
      * (* Thunk (UnitA (nth |as_| elemsD Undefined)) ≤ exact (Unit y) *)
        constructor. constructor.
        assert (Hbound : List.length as_ <
                         List.length (foldl_fsnoc_elems (as_ ++ [y]) (More f m r) outD)).
        { rewrite foldl_fsnoc_elems_length, List.app_length. cbn [List.length]. lia. }
        pose proof (@Forall2_nth (T B0) (T B0) less_defined _ _
                      (List.length as_) Undefined (exact y) Helems Hbound) as Hnth.
        rewrite app_nth2 in Hnth by (rewrite List.map_length; lia).
        rewrite List.map_length, Nat.sub_diag in Hnth. cbn [List.nth] in Hnth.
        exact Hnth.

    + (* s2 = More u2 m2 v2 : ARM 6 — deep recursive case *)
          destruct outD as [ | | u1D m'D v2D ].
          * cbn [glue] in Happrox. invert_clear Happrox.   (* outD = NilA: contradiction *)
          * cbn [glue] in Happrox. invert_clear Happrox.   (* outD = UnitA: contradiction *)
          * (* outD = MoreA u1D m'D v2D *)
            cbn [glue] in Happrox.
            invert_clear Happrox as [ | | ? ? ? ? ? ? Hu1 Hm Hv2 ].
            (* Hu1 : u1D ≤ exact f      (here u1 := f, the front digit of s1)
              Hm  : m'D ≤ exact (glue m (toTuples (digitToList r ++ as_ ++ digitToList u2)) m2)
              Hv2 : v2D ≤ exact v2 *)
            cbn [glueD']. cbv zeta.
            set (middle := toTuples (digitToList r ++ as_ ++ digitToList u2)) in *.
            set (m'D_forced := match m'D with
                              | Thunk q => q
                              | Undefined => bottom_of (exact (glue m middle m2))
                              end) in *.
            assert (Hm_forced : m'D_forced `is_approx` glue m middle m2).
            {
              unfold m'D_forced. destruct m'D as [ q | ] eqn:Eq.
              - invert_clear Hm. assumption.
              - apply bottom_is_least. reflexivity.
            }
            assert (Hmiddle_len : List.length middle <= 3).
            { 
              unfold middle. 
              apply toTuples_length_bound.
              rewrite !app_length. 
              destruct r, u2; simpl; lia. 
            }
            (* Fire the IH on the recursive call, capturing all three approx facts. *)
            specialize (IHm _ _ _ _ middle m2 m'D_forced Hmiddle_len Hm_forced).
            destruct (Tick.val (glueD' m middle m2 m'D_forced)) as [ [m1D middleD] m2D ] eqn:Eval.
            destruct IHm as [ Hm1D [ HmiddleD Hm2D ] ].
            (* Hm1D     : m1D     ≤ exact m
              HmiddleD : Forall2 less_defined middleD (map exact middle)
              Hm2D     : m2D     ≤ exact m2 *)
            simpl Tick.val.
            (* Goal now (after unbundle exposed):
              let '(v1D, asD, u2D) := unbundle middleD n_v1 n_as n_u2 in
              Thunk (MoreA u1D m1D v1D) ≤ exact (More f m r) /\
              Forall2 less_defined asD (map exact as_) /\
              Thunk (MoreA u2D m2D v2D) ≤ exact (More u2 m2 v2)
              where n_v1 = |digitToList r|, n_as = |as_|, n_u2 = |digitToList u2|. *)
            rewrite Eval.
            simpl Tick.val.
            (* If simpl over-reduces, use: cbn [Tick.val Tick.bind Tick.ret]. *)

            (* Name the slicing pieces. *)
            set (n_v1 := length (digitToList r)) in *.
            set (n_as := length as_) in *.
            set (n_u2 := length (digitToList u2)) in *.
            set (FLAT := List.concat
                          (map (fun '(k, t) => unbundleTuple k t)
                                (combine (tupleArities (n_v1 + n_as + n_u2)) middleD))) in *.

            (* The source list and its length bound. *)
            set (L := digitToList r ++ as_ ++ digitToList u2) in *.
            assert (HL_len : 2 <= length L <= 9).
            { 
              unfold L. rewrite !app_length. destruct r, u2; simpl; lia.
            }

            (* FLAT approximates `map exact L`, via lemma B.
              Note: middle = toTuples L, and n_v1 + n_as + n_u2 = length L. *)
            assert (Hn : n_v1 + n_as + n_u2 = length L).
            { 
              unfold n_v1, n_as, n_u2, L. rewrite !app_length.
              lia. 
            }
            assert (HFLAT : Forall2 less_defined FLAT (map exact L)).
            {
              unfold FLAT. rewrite Hn.
              apply unbundle_flat_approx; [ exact HL_len | ].
              (* HmiddleD : Forall2 ≤ middleD (map exact middle), middle = toTuples L *)
              unfold L. exact HmiddleD.
            }

            (* Split FLAT ≤ map exact L along the three segments of L.
              map exact L = map exact (digitToList r) ++ map exact as_ ++ map exact (digitToList u2). *)
            unfold L in HFLAT. rewrite !map_app in HFLAT.

            split; [ | split ].

            -- (* LEFT: Thunk (MoreA u1D m1D (listToDigitA (firstn n_v1 FLAT))) ≤ exact (More f m r) *)
              simpl exact.
              constructor.                 (* LessDefined_Thunk *)
              constructor.                 (* LessDefined_MoreA: 3 goals *)
              ++ exact Hu1.                 (* u1D ≤ exact f *)
              ++ exact Hm1D.                (* m1D ≤ exact m  (slot is Thunk (Exact_Seq … m)) *)
              ++ (* listToDigitA (firstn n_v1 FLAT) ≤ exact r *)
                apply listToDigitA_approx.
                pose proof (@Forall2_firstn _ _ less_defined n_v1 _ _ HFLAT) as Hsl.
                unfold n_v1 in *.
                destruct r as [a1 | a1 a2 | a1 a2 a3]; cbn [digitToList List.length List.map List.firstn List.app] in Hsl |- *; exact Hsl.

            -- (* MIDDLE: firstn n_as (skipn n_v1 FLAT) ≤ map exact as_ *)
                pose proof (@Forall2_firstn _ _ less_defined n_as _ _
                            (@Forall2_skipn _ _ less_defined n_v1 _ _ HFLAT)) as Hsl.
                unfold n_v1 in Hsl.
                destruct r as [a1 | a1 a2 | a1 a2 a3];
                  cbn [digitToList List.length List.map List.skipn List.app] in Hsl;
                  rewrite List.firstn_app in Hsl;
                  remember (map exact as_) as EA eqn:HEA in Hsl;
                  assert (Hla : length EA = n_as)
                    by (rewrite HEA; unfold n_as; rewrite List.map_length; reflexivity);
                  rewrite Hla in Hsl;
                  rewrite Nat.sub_diag in Hsl;
                  cbn [List.firstn] in Hsl;
                  rewrite List.app_nil_r in Hsl;
                  assert (HfA : List.firstn n_as EA = EA)
                    by (rewrite <- Hla; apply List.firstn_all);
                  rewrite HfA in Hsl;
                  rewrite HEA in Hsl;
                  exact Hsl.


            -- (* RIGHT: Thunk (MoreA (listToDigitA (skipn (n_v1+n_as) FLAT)) m2D v2D)
                          ≤ exact (More u2 m2 v2) *)
                simpl exact.
                constructor.
                constructor.
                ++ (* listToDigitA (skipn (n_v1+n_as) FLAT) ≤ exact u2 *)
                  apply listToDigitA_approx.
                  (* goal: skipn (n_v1 + n_as) FLAT `Forall2≤` map exact (digitToList u2) *)
                  pose proof (@Forall2_skipn _ _ less_defined (n_v1 + n_as) _ _ HFLAT) as Hsl.
                unfold n_v1 in Hsl.

                destruct r as [a1 | a1 a2 | a1 a2 a3].
                ** (* r = One a1, k = 1 *)
                  cbn [digitToList List.map] in Hsl.
                  rewrite !List.skipn_app in Hsl.
                  cbn [List.length] in Hsl.
                  rewrite List.map_length in Hsl.
                  replace (1 + n_as - 1 - n_as) with 0 in Hsl by lia.
                  replace (1 + n_as - 1) with n_as in Hsl by lia.
                  rewrite (List.skipn_all2 [exact a1] (n := 1 + n_as)) in Hsl
                    by (cbn [List.length]; lia).
                  rewrite (List.skipn_all2 (map exact as_) (n := n_as)) in Hsl
                    by (rewrite List.map_length; unfold n_as; lia).
                  cbn [List.app] in Hsl.
                  replace (n_as - length as_) with 0 in Hsl by (unfold n_as; lia).
                  cbn [List.skipn] in Hsl.
                  unfold n_v1.
                  cbn [digitToList List.length].
                  exact Hsl.
                ** (* r = Two a1 a2, k = 2 *)
                  cbn [digitToList List.map] in Hsl.
                  rewrite !List.skipn_app in Hsl.
                  cbn [List.length] in Hsl.
                  rewrite List.map_length in Hsl.
                  replace (2 + n_as - 2 - n_as) with 0 in Hsl by lia.
                  replace (2 + n_as - 2) with n_as in Hsl by lia.
                  rewrite (List.skipn_all2 [exact a1; exact a2] (n := 2 + n_as)) in Hsl
                    by (cbn [List.length]; lia).
                  rewrite (List.skipn_all2 (map exact as_) (n := n_as)) in Hsl
                    by (rewrite List.map_length; unfold n_as; lia).
                  cbn [List.app] in Hsl.
                  replace (n_as - length as_) with 0 in Hsl by (unfold n_as; lia).
                  cbn [List.skipn] in Hsl.
                  unfold n_v1.
                  cbn [digitToList List.length].
                  exact Hsl.
                ** (* r = Three a1 a2 a3, k = 3 *)
                  cbn [digitToList List.map] in Hsl.
                  rewrite !List.skipn_app in Hsl.
                  cbn [List.length] in Hsl.
                  rewrite List.map_length in Hsl.
                  replace (3 + n_as - 3 - n_as) with 0 in Hsl by lia.
                  replace (3 + n_as - 3) with n_as in Hsl by lia.
                  rewrite (List.skipn_all2 [exact a1; exact a2; exact a3] (n := 3 + n_as)) in Hsl
                    by (cbn [List.length]; lia).
                  rewrite (List.skipn_all2 (map exact as_) (n := n_as)) in Hsl
                    by (rewrite List.map_length; unfold n_as; lia).
                  cbn [List.app] in Hsl.
                  replace (n_as - length as_) with 0 in Hsl by (unfold n_as; lia).
                  cbn [List.skipn] in Hsl.
                  unfold n_v1.
                  cbn [digitToList List.length].
                  exact Hsl.

              ++ exact Hm2D.
              ++ exact Hv2.

Qed.

Corollary concatD_approx (A : Type) `{LDA : LessDefined A, !Reflexive LDA}
    (q1 q2 : Seq A) (outD : SeqA A) :
  outD `is_approx` concat q1 q2 ->
  let '(s1D, asD, s2D) := Tick.val (concatD q1 q2 outD) in
  s1D `less_defined` exact q1 /\
  Forall2 less_defined asD (List.map exact (@nil A)) /\
  s2D `less_defined` exact q2.
Proof.
  intro Happrox. unfold concatD.
  apply (@glueD'_approx A q1 A _ _ _ [] q2 outD); [ apply Nat.le_0_l | exact Happrox ].
Qed.


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

Lemma glue_middle_len_bound {A : Type} (r u2 : Digit A) (as_ : list A) :
  length as_ <= 3 ->
  length (toTuples (digitToList r ++ as_ ++ digitToList u2)) <= 3.
Proof.
  intro H. apply toTuples_length_bound.
  rewrite !List.app_length. destruct r, u2; cbn [digitToList List.length]; lia.
Qed.


#[local] Existing Instance Reflexive_LessDefined_T.
#[local] Existing Instance Reflexive_LessDefined_prodA.


(** [fconsD'] returns a Thunk for a valid demand — needed to force the middle
    spine in the recursive case of [fconsA_elemD_step] ([fconsD'] is not
    unconditionally Thunk, hence the [is_approx] hypothesis). *)
Lemma fconsD'_val_thunk (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (x : A) (s : Seq A) (outD : SeqA B) :
  outD `is_approx` fcons x s -> exists q, Tick.val (fconsD' x s outD) = Thunk q.
Proof.
  intro Hap. cbn [fcons] in Hap.
  destruct s as [ | y | [a | a b | a b c] m r ];
    destruct outD as [ | xD | fD mD rD ]; try (invert_clear Hap; fail);
    try (destruct fD as [ [ ? | ? ? | ? ? ? ] | ]);
    cbn [fconsD' Tick.bind Tick.ret Tick.val]; eexists; reflexivity.
Qed.

(** *** Single-[fcons] step for the spec direction.

    Kernel of the fold arms of [glueD'_spec].  Given the extracted element
    demand [fcons_elemD s outD] (or anything [e] above it) and any spine [q]
    at least the spine demand, the clairvoyant [fconsA'] reconstructs [outD]
    within the [fconsD'] cost.  The element [e] is upper-unconstrained: a
    bigger element only makes the output more defined, which still dominates
    [outD], and lets the recursive [More (Three ...)] case feed the
    spine-derived [PairA] demand.  Mirrors [fconsD'_spec] (FingerCons.v) but
    with the extracted/over-approximated element and an over-approximated
    spine. *)

Ltac kill_digit H :=
  try (invert_clear H;
       match goal with
       | Hd : (OneA _)       `less_defined` _ |- _ => invert_clear Hd
       | Hd : (TwoA _ _)     `less_defined` _ |- _ => invert_clear Hd
       | Hd : (ThreeA _ _ _) `less_defined` _ |- _ => invert_clear Hd
       end; fail).
Ltac force_all := mgo_; repeat (apply optimistic_thunk_go; mgo_).

Lemma fconsA_elemD_step (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, !Transitive LDB, Exact A B}
    (x : A) (s : Seq A) (outD : SeqA B) (e : T B) (q : SeqA B) :
  outD `is_approx` fcons x s ->
  fcons_elemD s outD `less_defined` e ->
  (match Tick.val (fconsD' x s outD) with
   | Thunk d => d | Undefined => bottom_of (exact s) end) `less_defined` q ->
  fconsA' q e
  [[ fun out cost => outD `less_defined` out /\ cost <= Tick.cost (fconsD' x s outD) ]].
Proof.
  revert e q. revert A x s B LDB Reflexive0 Transitive0 H outD.
  apply (fcons_ind (fun A x s s' =>
    forall B `{LDB : LessDefined B, !Reflexive LDB, !Transitive LDB, Exact A B}
           (outD : SeqA B) (e : T B) (q : SeqA B),
      outD `less_defined` exact s' ->
      fcons_elemD s outD `less_defined` e ->
      (match Tick.val (fconsD' x s outD) with
       | Thunk d => d | Undefined => bottom_of (exact s) end) `less_defined` q ->
      fconsA' q e
      [[ fun out cost => outD `less_defined` out /\ cost <= Tick.cost (fconsD' x s outD) ]])).
  - (* Case 1: s = Nil *)
    intros A0 x0 B0 LDB0 HRefl0 HTrans0 EAB0 outD e q Happrox Helem Hq.
    destruct outD as [ | xD | fD mD rD ]; try (invert_clear Happrox; fail).
    cbn [fcons_elemD] in Helem. simpl in Hq. invert_clear Hq.
    cbn [fconsA']. force_all.
  - (* Case 2: s = Unit y *)
    intros A0 x0 y0 B0 LDB0 HRefl0 HTrans0 EAB0 outD e q Happrox Helem Hq.
    destruct outD as [ | xD | fD mD rD ]; try (invert_clear Happrox; fail).
    invert_clear Happrox as [ | | ? ? ? ? ? ? Hf Hm Hr ].
    destruct fD as [ [ f1 | f1 f2 | f1 f2 f3 ] | ]; kill_digit Hf;
    destruct rD as [ [ ra | ra rb | ra rb rc ] | ]; kill_digit Hr;
      cbn [fcons_elemD] in Helem; simpl in Hq; invert_clear Hq;
      cbn [fconsA']; force_all.
  - (* Case 3: s = More (One a) m r *)
    intros A0 x0 a0 m0 r0 B0 LDB0 HRefl0 HTrans0 EAB0 outD e q Happrox Helem Hq.
    destruct outD as [ | xD | fD mD rD ]; try (invert_clear Happrox; fail).
    invert_clear Happrox as [ | | ? ? ? ? ? ? Hf Hm Hr ].
    destruct fD as [ [ f1 | f1 f2 | f1 f2 f3 ] | ]; kill_digit Hf;
      cbn [fcons_elemD] in Helem; simpl in Hq;
      invert_clear Hq as [ | | ? ? ? ? ? ? Hqf Hqm Hqr ];
      invert_clear Hqf as [ | ? ? Hz ]; invert_clear Hz as [ ? ? Hf2q | | ];
      cbn [fconsA']; force_all.
  - (* Case 4: s = More (Two a b) m r *)
    intros A0 x0 a0 b0 m0 r0 B0 LDB0 HRefl0 HTrans0 EAB0 outD e q Happrox Helem Hq.
    destruct outD as [ | xD | fD mD rD ]; try (invert_clear Happrox; fail).
    invert_clear Happrox as [ | | ? ? ? ? ? ? Hf Hm Hr ].
    destruct fD as [ [ f1 | f1 f2 | f1 f2 f3 ] | ]; kill_digit Hf;
      cbn [fcons_elemD] in Helem; simpl in Hq;
      invert_clear Hq as [ | | ? ? ? ? ? ? Hqf Hqm Hqr ];
      invert_clear Hqf as [ | ? ? Hz ]; invert_clear Hz as [ | ? ? ? ? Haq Hbq | ];
      cbn [fconsA']; force_all.
  - (* Case 5: s = More (Three a b c) m r -- recursive.  Forces the three
       let~ (f', pbc, m'); the middle m' recurses via IH at Tuple level
       (element the spine-derived PairA qb qc, hence the over-approximated
       element and the [transitivity] step for IH side-condition 2).  The
       mD = Undefined sub-cases skip the middle (optimistic_skip). *)
    intros A0 x0 a0 b0 c0 m0 r0 IH B0 LDB0 HRefl0 HTrans0 EAB0 outD e q Happrox Helem Hq.
    destruct outD as [ | xD | fD mD rD ]; try (invert_clear Happrox; fail).
    invert_clear Happrox as [ | | ? ? ? ? ? ? Hf Hm Hr ].
    destruct fD as [ [ f1 | f1 f2 | f1 f2 f3 ] | ]; kill_digit Hf;
      cbn [fcons_elemD] in Helem; cbn [fconsD' Tick.bind Tick.ret Tick.val] in Hq;
      invert_clear Hq as [ | | ? ? ? ? ? ? Hqf Hqm Hqr ];
      invert_clear Hqf as [ | ? ? Hz ];
      invert_clear Hz as [ | | ? ? ? ? ? ? Haq Hbq Hcq ];
      destruct mD as [ dc | ]; cbn [thunkD] in Hqm.
    + (* TwoA front, mD = Thunk dc *)
      assert (Hmc : dc `is_approx` fcons (Pair b0 c0) m0) by (invert_clear Hm; assumption).
      destruct (@fconsD'_val_thunk (Tuple A0) (TupleA B0) _ _ _ (Pair b0 c0) m0 dc Hmc) as [ qd Hqd ].
      rewrite Hqd in Hqm.
      assert (Hq2 : exists q2', m2 = Thunk q2' /\ qd `less_defined` q2')
        by (destruct m2 as [ q2' | ]; [ exists q2'; split; [ reflexivity | invert_clear Hqm; assumption ] | invert_clear Hqm ]).
      destruct Hq2 as [ q2' [ Hm2 Hqd' ] ]. subst m2.
      cbn [fconsA']; mgo_;
      apply optimistic_thunk_go; mgo_;
      apply optimistic_thunk_go; mgo_;
      apply optimistic_thunk_go; mgo_.
      eapply optimistic_mon.
      { eapply IH.
        - typeclasses eauto.
        - typeclasses eauto.
        - exact Hmc.
        - eapply (@transitivity (T (TupleA B0)) less_defined
                    (@Transitive_LessDefined_T (TupleA B0) _ (@Transitive_LessDefined_TupleA B0 _ HTrans0))
                    _ (exact (Pair b0 c0)) _);
            [ eapply fcons_elemD_approx; exact Hmc
            | cbn [exact Exact_Tuple Exact_T]; constructor; constructor; [ exact Hbq | exact Hcq ] ].
        - rewrite Hqd. cbn. exact Hqd'. }
      intros mv n2 [Hmv Hcost2].
      apply optimistic_ret. split.
      * constructor;
        [ constructor; constructor; [ exact Helem | exact Haq ]
        | constructor; exact Hmv
        | exact Hqr ].
      * cbn [fconsD' thunkD Tick.bind Tick.ret Tick.tick Tick.cost Tick.val] in *; lia.
    + (* TwoA front, mD = Undefined: skip the middle recursion *)
      cbn [fconsA']; mgo_;
      apply optimistic_thunk_go; mgo_;
      apply optimistic_thunk_go; mgo_;
      apply optimistic_skip; mgo_.
    + (* Undefined front, mD = Thunk dc: recurse (mirror of TwoA-Thunk, Undefined front) *)
      assert (Hmc : dc `is_approx` fcons (Pair b0 c0) m0) by (invert_clear Hm; assumption).
      destruct (@fconsD'_val_thunk (Tuple A0) (TupleA B0) _ _ _ (Pair b0 c0) m0 dc Hmc) as [ qd Hqd ].
      rewrite Hqd in Hqm.
      assert (Hq2 : exists q2', m2 = Thunk q2' /\ qd `less_defined` q2')
        by (destruct m2 as [ q2' | ]; [ exists q2'; split; [ reflexivity | invert_clear Hqm; assumption ] | invert_clear Hqm ]).
      destruct Hq2 as [ q2' [ Hm2 Hqd' ] ]. subst m2.
      cbn [fconsA']; mgo_;
      apply optimistic_thunk_go; mgo_;
      apply optimistic_thunk_go; mgo_;
      apply optimistic_thunk_go; mgo_.
      eapply optimistic_mon.
      { eapply IH.
        - typeclasses eauto.
        - typeclasses eauto.
        - exact Hmc.
        - eapply (@transitivity (T (TupleA B0)) less_defined
                    (@Transitive_LessDefined_T (TupleA B0) _ (@Transitive_LessDefined_TupleA B0 _ HTrans0))
                    _ (exact (Pair b0 c0)) _);
            [ eapply fcons_elemD_approx; exact Hmc
            | cbn [exact Exact_Tuple Exact_T]; constructor; constructor; [ exact Hbq | exact Hcq ] ].
        - rewrite Hqd. cbn. exact Hqd'. }
      intros mv n2 [Hmv Hcost2].
      apply optimistic_ret. split.
      * constructor; [ constructor | constructor; exact Hmv | exact Hqr ].
      * cbn [fconsD' thunkD Tick.bind Tick.ret Tick.tick Tick.cost Tick.val] in *; lia.
    + (* Undefined front, mD = Undefined: skip *)
      cbn [fconsA']; mgo_;
      apply optimistic_thunk_go; mgo_;
      apply optimistic_thunk_go; mgo_;
      apply optimistic_skip; mgo_.
Qed.


(** *** Clairvoyant fold-right reconstructs [outD] from the recorded element
    demands ([foldr_fcons_elems]).  This is the fold arm of [glueD'_spec]'s
    [Nil]/[Unit] cases: the clairvoyant fold over the element demands, started
    from the threaded spine demand [q2], dominates [outD] within the
    [foldr_fconsD'] cost.  Replaces the (false) [foldr_fconsA_undef_spec].
    Runs by induction on [as_] using [fconsA_elemD_step] per element. *)
Lemma foldr_fcons_clairvoyant_spec (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, !Transitive LDB, Exact A B}
    (as_ : list A) (s_2 : Seq A) (outD : SeqA B) (q2 : SeqA B) :
  outD `is_approx` List.fold_right fcons s_2 as_ ->
  Tick.val (foldr_fconsD' as_ s_2 outD) = Thunk q2 ->
  List.fold_right (fun (x : T B) (acc : M (SeqA B)) => let! q := acc in fconsA' q x)
                  (ret q2) (foldr_fcons_elems as_ s_2 outD)
  [[ fun y m => outD `less_defined` y /\ S m <= S (Tick.cost (foldr_fconsD' as_ s_2 outD) + 0) ]].
Proof.
  revert s_2 outD q2.
  induction as_ as [| x as' IH]; intros s_2 outD q2 Happrox Hval.
  - cbn [foldr_fcons_elems List.fold_right] in *.
    cbn [foldr_fconsD' Tick.bind Tick.ret Tick.val] in Hval |- *.
    apply optimistic_ret. injection Hval as Hq2. subst q2. split; [ reflexivity | lia ].
  - cbn [List.fold_right] in Happrox.
    set (s := List.fold_right fcons s_2 as') in *.
    set (iD := match Tick.val (fconsD' x s outD) with
               | Thunk q => q | Undefined => bottom_of (exact s) end) in *.
    cbn [foldr_fcons_elems]. fold s. fold iD.
    cbn [List.fold_right].
    apply optimistic_bind.
    assert (Hap_iD : iD `is_approx` List.fold_right fcons s_2 as').
    { unfold iD. pose proof (@fconsD'_approx A B _ _ _ x s outD Happrox) as Hin.
      destruct (Tick.val (fconsD' x s outD)) as [ d | ] eqn:Eq.
      - cbn. invert_clear Hin. assumption.
      - cbn. apply bottom_is_least. reflexivity. }
    eapply optimistic_mon.
    { apply (IH s_2 iD q2 Hap_iD Hval). }
    intros q n [Hq_ge Hn].
    eapply optimistic_mon.
    { eapply fconsA_elemD_step; [ exact Happrox | reflexivity | exact Hq_ge ]. }
    intros y m [Hout Hcost].
    split; [ exact Hout | ].
    unfold iD in *.
    cbn [foldr_fconsD'] in Hn |- *.
    unfold Tick.bind; cbn [Tick.cost Tick.val].
    unfold s in *. lia.
Qed.


(** *** Snoc-side duals of the cons step / fold helper, for the [_,Nil] and
    [_,Unit] arms of [glueD'_spec] (which run [glueA']'s [fold_left fsnoc]).
    [fsnocA_elemD_step] mirrors [fconsA_elemD_step] (front<->rear); the fold
    helper is generalised on the seed computation [acc] (and its cost budget
    [Cacc]) because [fold_left] threads the accumulator. *)

Lemma fsnocA_elemD_step (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, !Transitive LDB, Exact A B}
    (x : A) (s : Seq A) (outD : SeqA B) (e : T B) (q : SeqA B) :
  outD `is_approx` fsnoc s x ->
  fsnoc_elemD s outD `less_defined` e ->
  (match Tick.val (fsnocD' s x outD) with
   | Thunk d => d | Undefined => bottom_of (exact s) end) `less_defined` q ->
  fsnocA' q e
  [[ fun out cost => outD `less_defined` out /\ cost <= Tick.cost (fsnocD' s x outD) ]].
Proof.
  revert e q. revert A x s B LDB Reflexive0 Transitive0 H outD.
  apply (fsnoc_ind (fun A x s s' =>
    forall B `{LDB : LessDefined B, !Reflexive LDB, !Transitive LDB, Exact A B}
           (outD : SeqA B) (e : T B) (q : SeqA B),
      outD `less_defined` exact s' ->
      fsnoc_elemD s outD `less_defined` e ->
      (match Tick.val (fsnocD' s x outD) with
       | Thunk d => d | Undefined => bottom_of (exact s) end) `less_defined` q ->
      fsnocA' q e
      [[ fun out cost => outD `less_defined` out /\ cost <= Tick.cost (fsnocD' s x outD) ]])).
  - (* Case 1: s = Nil *)
    intros A0 x0 B0 LDB0 HRefl0 HTrans0 EAB0 outD e q Happrox Helem Hq.
    destruct outD as [ | xD | fD mD rD ]; try (invert_clear Happrox; fail).
    cbn [fsnoc_elemD] in Helem. simpl in Hq. invert_clear Hq.
    cbn [fsnocA']. force_all.
  - (* Case 2: s = Unit y *)
    intros A0 x0 y0 B0 LDB0 HRefl0 HTrans0 EAB0 outD e q Happrox Helem Hq.
    destruct outD as [ | xD | fD mD rD ]; try (invert_clear Happrox; fail).
    invert_clear Happrox as [ | | ? ? ? ? ? ? Hf Hm Hr ].
    destruct fD as [ [ f1 | f1 f2 | f1 f2 f3 ] | ]; kill_digit Hf;
    destruct rD as [ [ ra | ra rb | ra rb rc ] | ]; kill_digit Hr;
      cbn [fsnoc_elemD] in Helem; simpl in Hq; invert_clear Hq;
      cbn [fsnocA']; force_all.
  - (* Case 3: s = More f m (One a) *)
    intros A0 x0 a0 f0 m0 B0 LDB0 HRefl0 HTrans0 EAB0 outD e q Happrox Helem Hq.
    destruct outD as [ | xD | fD mD rD ]; try (invert_clear Happrox; fail).
    invert_clear Happrox as [ | | ? ? ? ? ? ? Hf Hm Hr ].
    destruct rD as [ [ r1 | r1 r2 | r1 r2 r3 ] | ]; kill_digit Hr;
      cbn [fsnoc_elemD] in Helem; simpl in Hq;
      invert_clear Hq as [ | | ? ? ? ? ? ? Hqf Hqm Hqr ];
      invert_clear Hqr as [ | ? ? Hz ]; invert_clear Hz as [ ? ? Hr1q | | ];
      cbn [fsnocA']; force_all.
  - (* Case 4: s = More f m (Two a b) *)
    intros A0 x0 a0 b0 f0 m0 B0 LDB0 HRefl0 HTrans0 EAB0 outD e q Happrox Helem Hq.
    destruct outD as [ | xD | fD mD rD ]; try (invert_clear Happrox; fail).
    invert_clear Happrox as [ | | ? ? ? ? ? ? Hf Hm Hr ].
    destruct rD as [ [ r1 | r1 r2 | r1 r2 r3 ] | ]; kill_digit Hr;
      cbn [fsnoc_elemD] in Helem; simpl in Hq;
      invert_clear Hq as [ | | ? ? ? ? ? ? Hqf Hqm Hqr ];
      invert_clear Hqr as [ | ? ? Hz ]; invert_clear Hz as [ | ? ? ? ? Haq Hbq | ];
      cbn [fsnocA']; force_all.
  - (* Case 5: recursive -- admit (mirror of fconsA_elemD_step case 5) *)
    admit.
Admitted.

Lemma foldl_fsnoc_clairvoyant_spec (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, !Transitive LDB, Exact A B} :
  forall (as_ : list A) (s_1 : Seq A) (outD : SeqA B) (acc : M (SeqA B)) (Cacc : nat),
    outD `is_approx` List.fold_left fsnoc as_ s_1 ->
    acc [[ fun a c => (match Tick.val (foldl_fsnocD' as_ s_1 outD) with
                       | Thunk d => d | Undefined => bottom_of (exact s_1) end) `less_defined` a
                      /\ c <= Cacc ]] ->
    List.fold_left (fun ac x => let! q := ac in fsnocA' q x) (foldl_fsnoc_elems as_ s_1 outD) acc
    [[ fun y m => outD `less_defined` y /\ m <= Cacc + Tick.cost (foldl_fsnocD' as_ s_1 outD) ]].
Proof.
  induction as_ as [| x as' IH]; intros s_1 outD acc Cacc Happrox Hacc.
  - cbn [foldl_fsnoc_elems List.fold_left] in *.
    cbn [foldl_fsnocD' Tick.bind Tick.ret Tick.val] in Hacc |- *.
    eapply optimistic_mon; [ exact Hacc | ]. intros y m [Ho Hc]. split; [ exact Ho | lia ].
  - cbn [List.fold_left] in Happrox.
    set (iD := match Tick.val (foldl_fsnocD' as' (fsnoc s_1 x) outD) with
               | Thunk d => d | Undefined => bottom_of (exact (fsnoc s_1 x)) end) in *.
    cbn [foldl_fsnoc_elems]. fold iD.
    cbn [List.fold_left].
    assert (Hap_iD : iD `is_approx` fsnoc s_1 x).
    { unfold iD. pose proof (@foldl_fsnocD'_approx A B _ _ _ as' (fsnoc s_1 x) outD Happrox) as Hin.
      destruct (Tick.val (foldl_fsnocD' as' (fsnoc s_1 x) outD)) as [ d | ] eqn:Eq.
      - cbn. invert_clear Hin. assumption.
      - cbn. apply bottom_is_least. reflexivity. }
    eapply optimistic_mon.
    { apply (IH (fsnoc s_1 x) outD
                (let! q := acc in fsnocA' q (fsnoc_elemD s_1 iD))
                (Cacc + Tick.cost (fsnocD' s_1 x iD)) Happrox).
      apply optimistic_bind.
      eapply optimistic_mon; [ exact Hacc | ].
      intros qa na [Hqa Hna].
      eapply optimistic_mon.
      { eapply fsnocA_elemD_step; [ exact Hap_iD | reflexivity | ].
        cbn [foldl_fsnocD' Tick.bind Tick.val] in Hqa. exact Hqa. }
      intros y m [Ho Hc]. split; [ exact Ho | lia ]. }
    intros y m [Ho Hc]. split; [ exact Ho | ].
    cbn [foldl_fsnocD'] in *.
    unfold Tick.bind, Tick.ret; cbn [Tick.cost Tick.val] in *. unfold iD in *. lia.
Qed.


(** *** [foldl_fsnocD'] returns a Thunk for a valid demand -- needed to
    discharge the Undefined-spine branch of the snoc arms of glueD'_spec.
    (Unlike the cons fold, fsnocD' is not unconditionally Thunk, hence the
    is_approx hypothesis.) *)
Lemma fsnocD'_val_thunk (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (s : Seq A) (x : A) (outD : SeqA B) :
  outD `is_approx` fsnoc s x ->
  exists q, Tick.val (fsnocD' s x outD) = Thunk q.
Proof.
  intro Hap. cbn [fsnoc] in Hap.
  destruct s as [ | y | f m [a | a b | a b c] ];
    destruct outD as [ | xD | fD mD rD ]; try (invert_clear Hap; fail);
    try (destruct fD as [ [ ? | ? ? | ? ? ? ] | ]);
    try (destruct rD as [ [ ? | ? ? | ? ? ? ] | ]);
    cbn [fsnocD' Tick.bind Tick.ret Tick.val]; eexists; reflexivity.
Qed.

Lemma foldl_fsnocD'_val_thunk (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (as_ : list A) (s_1 : Seq A) (outD : SeqA B) :
  outD `is_approx` List.fold_left fsnoc as_ s_1 ->
  exists q, Tick.val (foldl_fsnocD' as_ s_1 outD) = Thunk q.
Proof.
  revert s_1 outD. induction as_ as [| x as' IH]; intros s_1 outD Hap.
  - cbn [foldl_fsnocD' Tick.ret Tick.val]. eexists. reflexivity.
  - cbn [List.fold_left] in Hap.
    cbn [foldl_fsnocD'].
    set (iD := match Tick.val (foldl_fsnocD' as' (fsnoc s_1 x) outD) with
               | Thunk d => d | Undefined => bottom_of (exact (fsnoc s_1 x)) end) in *.
    assert (Hap_iD : iD `is_approx` fsnoc s_1 x).
    { unfold iD. pose proof (@foldl_fsnocD'_approx A B _ _ _ as' (fsnoc s_1 x) outD Hap) as Hin.
      destruct (Tick.val (foldl_fsnocD' as' (fsnoc s_1 x) outD)) as [ d | ] eqn:Eq.
      - cbn. invert_clear Hin. assumption.
      - cbn. apply bottom_is_least. reflexivity. }
    destruct (@fsnocD'_val_thunk A B _ _ _ s_1 x iD Hap_iD) as [ q Hq ].
    cbn [Tick.bind Tick.val]. fold iD. rewrite Hq. cbn. eexists. reflexivity.
Qed.


(** *** [glueD'_spec]: clairvoyant dominates demand. *)
Lemma glueD'_spec :
  forall (A : Type) (s1 : Seq A)
         (B : Type) `{LDB : LessDefined B, !Reflexive LDB, !Transitive LDB, Exact A B}
         (as_ : list A) (s2 : Seq A) (outD : SeqA B),
    List.length as_ <= 3 ->
    outD `is_approx` glue s1 as_ s2 ->
    forall s1D asD s2D,
      (s1D, asD, s2D) = Tick.val (glueD' s1 as_ s2 outD) ->
      let dcost := Tick.cost (glueD' s1 as_ s2 outD) in
      glueA s1D asD s2D
      [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  apply (Seq_ind_poly
    (fun (A : Type) (s1 : Seq A) =>
       forall (B : Type) `{LDB : LessDefined B, !Reflexive LDB, !Transitive LDB, Exact A B}
              (as_ : list A) (s2 : Seq A) (outD : SeqA B),
         List.length as_ <= 3 ->
         outD `is_approx` glue s1 as_ s2 ->
         forall s1D asD s2D,
           (s1D, asD, s2D) = Tick.val (glueD' s1 as_ s2 outD) ->
           let dcost := Tick.cost (glueD' s1 as_ s2 outD) in
           glueA s1D asD s2D
           [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]])).

  (* ------------------------------------------------------------------ *)
  (* Six admits below.  Plan + per-session orchestration:               *)
  (*   docs/CONCAT_SPEC_PLAN.md.    Kernel lemma + harness: wip/.        *)
  (* Inspect any arm's exact goal with wip/inspect.v (copy the block,    *)
  (* set s1/s2, idtac the goal).  Order: Nil -> Unit/_ -> snoc arms ->   *)
  (* deep More/More (hardest).                                           *)
  (* ------------------------------------------------------------------ *)

  - (* === s1 = Nil ===  glue Nil as_ s2 = foldr fcons s2 as_;
       reconstruct outD from the recorded element demands via the fold helper. *)
    intros A0 B0 LDB0 Refl0 Trans0 EAB0 as_ s2 outD Hlen Happrox s1D asD s2D Htriple dcost.
    cbn [glueD'] in Htriple, dcost.
    cbn [Tick.val Tick.bind Tick.ret] in Htriple.
    invert_clear Htriple.
    unfold glueA.
    destruct (Tick.val (foldr_fconsD' as_ s2 outD)) as [ q2 | ] eqn:Es2D.
    + simpl. mgo_. subst dcost. cbn [glue] in Happrox.
      eapply foldr_fcons_clairvoyant_spec; [ exact Happrox | exact Es2D ].
    + (* [s2D] = Undefined is vacuous: foldr_fconsD' always returns a Thunk. *)
      exfalso. destruct (foldr_fconsD'_val_thunk as_ s2 outD) as [ qx Hqx ].
      rewrite Hqx in Es2D. discriminate Es2D.

  - (* === s1 = Unit x === *)
    intros A0 x B0 LDB0 Refl0 Trans0 EAB0 as_ s2 outD Hlen Happrox s1D asD s2D Htriple dcost.
    destruct s2 as [ | y | u2 m2 v2 ].
    + (* arm 2: glue (Unit x) as_ Nil = foldl fsnoc (Unit x) as_.
         glueA' q1 asD NilA hits the _,NilA branch (q1 = demand on Unit x, <> NilA)
         = fold_left fsnoc over (foldl_fsnoc_elems as_ (Unit x) outD) from ret q1,
         which is the foldl helper with seed (ret q1). *)
      cbn [glueD'] in Htriple, dcost; cbv zeta in Htriple, dcost. subst dcost.
      cbn [Tick.val Tick.bind Tick.ret] in Htriple. invert_clear Htriple.
      unfold glueA. cbn [glue] in Happrox.
      destruct (Tick.val (foldl_fsnocD' as_ (Unit x) outD)) as [ q1 | ] eqn:Es1D.
      * pose proof (@foldl_fsnocD'_approx A0 B0 _ _ _ as_ (Unit x) outD Happrox) as Happ1.
        rewrite Es1D in Happ1.
        pose proof (@foldl_fsnoc_clairvoyant_spec A0 B0 _ _ _ _ as_ (Unit x) outD (ret q1) 0 Happrox) as Hh.
        destruct q1 as [ | qx | qf qm qr ];
          [ exfalso; invert_clear Happ1;
            match goal with H : _ `less_defined` _ |- _ => invert_clear H end
          | cbn [glueA']; apply optimistic_bind; apply optimistic_tick;
            eapply optimistic_mon;
            [ apply Hh; apply optimistic_ret; rewrite Es1D; cbn; split; [ reflexivity | lia ]
            | intros yo mo [Ho Hc]; split;
              [ exact Ho
              | unfold Tick.bind, Tick.ret, Tick.tick; cbn [Tick.cost Tick.val] in *; lia ] ]
          | exfalso; invert_clear Happ1;
            match goal with H : _ `less_defined` _ |- _ => invert_clear H end ].
      * exfalso. destruct (@foldl_fsnocD'_val_thunk A0 B0 _ _ _ as_ (Unit x) outD Happrox) as [ qx Hqx ].
        rewrite Hqx in Es1D. discriminate Es1D.
    + (* arm 4: glue (Unit x) as_ (Unit y) = foldr fcons (Unit y) (x :: as_).
         glueD' returns s1D = Thunk (UnitA (head elems)), asD = tail elems; the
         clairvoyant glueA' (UnitA head) (tail) folds over (head :: tail) =
         foldr_fcons_elems (x :: as_) (Unit y) outD, so this reduces to the
         fold helper on (x :: as_). *)
      cbn [glueD'] in Htriple, dcost; cbv zeta in Htriple, dcost.
      destruct (foldr_fcons_elems (x :: as_) (Unit y) outD) as [ | xD asD' ] eqn:He.
      * cbn [foldr_fcons_elems] in He. discriminate He.
      * cbn [Tick.val Tick.bind Tick.ret] in Htriple. invert_clear Htriple.
        unfold glueA. cbn [glue] in Happrox.
        destruct (Tick.val (foldr_fconsD' (x :: as_) (Unit y) outD)) as [ q2 | ] eqn:Es2D.
        -- subst dcost.
           pose proof (@foldr_fconsD'_approx A0 B0 _ _ _ (x :: as_) (Unit y) outD Happrox) as Happ2.
           rewrite Es2D in Happ2.
           pose proof (@foldr_fcons_clairvoyant_spec A0 B0 _ _ _ _ (x :: as_) (Unit y) outD q2 Happrox Es2D) as Hh.
           rewrite He in Hh.
           (* q2 = demand on (Unit y), so q2 <> NilA: the UnitA-front fold_right branch
              applies.  Consume only the glueA' tick (don't let mgo_ peel the concrete
              cons), then hand the whole fold to the helper. *)
           destruct q2 as [ | qy | qf qm qr ].
           { exfalso. invert_clear Happ2.
             match goal with H : _ `less_defined` _ |- _ => invert_clear H end. }
           all: cbn [glueA']; apply optimistic_bind; apply optimistic_tick;
                eapply optimistic_mon; [ exact Hh | ];
                intros yo mo [Ho Hc]; split;
                [ exact Ho
                | unfold Tick.bind, Tick.ret, Tick.tick;
                  cbn [foldr_fcons_elems Tick.cost Tick.val] in *; lia ].
        -- exfalso. destruct (foldr_fconsD'_val_thunk (x :: as_) (Unit y) outD) as [ qx Hqx ].
           rewrite Hqx in Es2D. discriminate Es2D.
    + (* arm 4 again, s2 = More u2 m2 v2 (same Unit-front branch). *)
      cbn [glueD'] in Htriple, dcost; cbv zeta in Htriple, dcost.
      destruct (foldr_fcons_elems (x :: as_) (More u2 m2 v2) outD) as [ | xD asD' ] eqn:He.
      * cbn [foldr_fcons_elems] in He. discriminate He.
      * cbn [Tick.val Tick.bind Tick.ret] in Htriple. invert_clear Htriple.
        unfold glueA. cbn [glue] in Happrox.
        destruct (Tick.val (foldr_fconsD' (x :: as_) (More u2 m2 v2) outD)) as [ q2 | ] eqn:Es2D.
        -- subst dcost.
           pose proof (@foldr_fconsD'_approx A0 B0 _ _ _ (x :: as_) (More u2 m2 v2) outD Happrox) as Happ2.
           rewrite Es2D in Happ2.
           pose proof (@foldr_fcons_clairvoyant_spec A0 B0 _ _ _ _ (x :: as_) (More u2 m2 v2) outD q2 Happrox Es2D) as Hh.
           rewrite He in Hh.
           (* q2 = demand on (More u2 m2 v2), so q2 <> NilA. *)
           destruct q2 as [ | qy | qf qm qr ].
           { exfalso. invert_clear Happ2.
             match goal with H : _ `less_defined` _ |- _ => invert_clear H end. }
           all: cbn [glueA']; apply optimistic_bind; apply optimistic_tick;
                eapply optimistic_mon; [ exact Hh | ];
                intros yo mo [Ho Hc]; split;
                [ exact Ho
                | unfold Tick.bind, Tick.ret, Tick.tick;
                  cbn [foldr_fcons_elems Tick.cost Tick.val] in *; lia ].
        -- exfalso. destruct (foldr_fconsD'_val_thunk (x :: as_) (More u2 m2 v2) outD) as [ qx Hqx ].
           rewrite Hqx in Es2D. discriminate Es2D.

  - (* === s1 = More f m r === *)
    intros A0 f m r IHm B0 LDB0 Refl0 Trans0 EAB0 as_ s2 outD Hlen Happrox s1D asD s2D Htriple dcost.
    destruct s2 as [ | y | u2 m2 v2 ].
    + (* arm 3: glue (More f m r) as_ Nil = foldl fsnoc (More f m r) as_.
         Like arm 2 with accumulator (More f m r); q1 = demand on More, so MoreA. *)
      cbn [glueD'] in Htriple, dcost; cbv zeta in Htriple, dcost. subst dcost.
      cbn [Tick.val Tick.bind Tick.ret] in Htriple. invert_clear Htriple.
      unfold glueA. cbn [glue] in Happrox.
      destruct (Tick.val (foldl_fsnocD' as_ (More f m r) outD)) as [ q1 | ] eqn:Es1D.
      * pose proof (@foldl_fsnocD'_approx A0 B0 _ _ _ as_ (More f m r) outD Happrox) as Happ1.
        rewrite Es1D in Happ1.
        pose proof (@foldl_fsnoc_clairvoyant_spec A0 B0 _ _ _ _ as_ (More f m r) outD (ret q1) 0 Happrox) as Hh.
        destruct q1 as [ | qx | qf qm qr ];
          [ exfalso; invert_clear Happ1;
            match goal with H : _ `less_defined` _ |- _ => invert_clear H end
          | exfalso; invert_clear Happ1;
            match goal with H : _ `less_defined` _ |- _ => invert_clear H end
          | cbn [glueA']; apply optimistic_bind; apply optimistic_tick;
            eapply optimistic_mon;
            [ apply Hh; apply optimistic_ret; rewrite Es1D; cbn; split; [ reflexivity | lia ]
            | intros yo mo [Ho Hc]; split;
              [ exact Ho
              | unfold Tick.bind, Tick.ret, Tick.tick; cbn [Tick.cost Tick.val] in *; lia ] ] ].
      * exfalso. destruct (@foldl_fsnocD'_val_thunk A0 B0 _ _ _ as_ (More f m r) outD Happrox) as [ qx Hqx ].
        rewrite Hqx in Es1D. discriminate Es1D.
    + (* arm 5: glue (More f m r) as_ (Unit y) = foldl fsnoc (as_ ++ [y]) (More f m r).
         glueA' q1 asD (UnitA yD) hits the _,UnitA branch = fold_left fsnoc over
         (asD ++ [yD]) from ret q1.  glueD' set asD = firstn |as_| elemsD and
         yD = nth |as_| elemsD; firstn_nth_last reassembles them into elemsD =
         foldl_fsnoc_elems (as_ ++ [y]) (More f m r) outD, the foldl helper's list. *)
      cbn [glueD'] in Htriple, dcost; cbv zeta in Htriple, dcost. subst dcost.
      set (elemsD := foldl_fsnoc_elems (as_ ++ [y]) (More f m r) outD) in *.
      assert (Hreass : List.firstn (List.length as_) elemsD
                       ++ [List.nth (List.length as_) elemsD Undefined] = elemsD).
      { apply firstn_nth_last. unfold elemsD.
        rewrite foldl_fsnoc_elems_length, List.app_length. cbn [List.length]. lia. }
      cbn [Tick.val Tick.bind Tick.ret] in Htriple. invert_clear Htriple.
      unfold glueA. cbn [glue] in Happrox.
      destruct (Tick.val (foldl_fsnocD' (as_ ++ [y]) (More f m r) outD)) as [ q1 | ] eqn:Es1D.
      * pose proof (@foldl_fsnocD'_approx A0 B0 _ _ _ (as_ ++ [y]) (More f m r) outD Happrox) as Happ1.
        rewrite Es1D in Happ1.
        pose proof (@foldl_fsnoc_clairvoyant_spec A0 B0 _ _ _ _ (as_ ++ [y]) (More f m r) outD (ret q1) 0 Happrox) as Hh.
        fold elemsD in Hh.
        destruct q1 as [ | qx | qf qm qr ];
          [ exfalso; invert_clear Happ1;
            match goal with H : _ `less_defined` _ |- _ => invert_clear H end
          | exfalso; invert_clear Happ1;
            match goal with H : _ `less_defined` _ |- _ => invert_clear H end
          | cbn [glueA']; apply optimistic_bind; apply optimistic_tick;
            eapply optimistic_mon;
            [ rewrite Hreass; apply Hh; apply optimistic_ret; rewrite Es1D; cbn;
              split; [ reflexivity | lia ]
            | intros yo mo [Ho Hc]; split;
              [ exact Ho
              | unfold Tick.bind, Tick.ret, Tick.tick; cbn [Tick.cost Tick.val] in *; lia ] ] ].
      * exfalso. destruct (@foldl_fsnocD'_val_thunk A0 B0 _ _ _ (as_ ++ [y]) (More f m r) outD Happrox) as [ qx Hqx ].
        rewrite Hqx in Es1D. discriminate Es1D.
    + (* arm 6: DEEP More/More — the hard lockstep.  outD = MoreA u1D m'D v2D.
         glueA' recurses on the middle; glueD' recursed via unbundle.  Need:
           IHm (the Seq_ind_poly hypothesis at Tuple level) for the middle,
           glueA'_mon for monotonicity of the recursive clairvoyant call,
           and the unbundle ROUND-TRIP on the spec side: that re-bundling the
           sliced (v1D | asD | u2D) reproduces the middle demand middleD.
           This last is the dual of unbundle_flat_approx and is the likely new
           lemma to write.  SPIKE THIS EARLY (see plan §3, Session A). *)
      admit.
Admitted.

(* ================================================================= *)
(** ** Section 5b: Asymptotic [O(log n)] corollary                     *)
(* ================================================================= *)

(** Convert the [depth]-based cost bound to a [log2 size]-based bound
    via the size-depth relationship established in [FingerSize.v]. *)


(** *** Cost of [concat] in terms of [log_2] of input sizes.

    For nonempty inputs, the cost is bounded by a constant multiple of
    [log_2 (size q_1) + log_2 (size q_2)] plus an additive constant. *)
Corollary concatD_cost_logsize (A : Type) `{LDA: LessDefined A, Hrefl: !Reflexive LDA}
    (q1 q2 : Seq A) (outD : SeqA A) :
  q1 <> Nil ->
  q2 <> Nil ->
  outD `is_approx` concat q1 q2 ->
  Tick.cost (concatD q1 q2 outD) <=
    glue_cost_const_1 * (Nat.log2 (size q1) + Nat.log2 (size q2))
    + glue_cost_const_2.
Proof.
  intros Hq1 Hq2 Happrox.

  pose proof (@concatD_cost A LDA Hrefl q1 q2 outD Happrox) as Hcost.
  pose proof (@depth_log_size A q1 Hq1) as Hlog1.
  pose proof (@depth_log_size A q2 Hq2) as Hlog2.
  unfold glue_cost_const_1, glue_cost_const_2 in *.
  unfold depth in Hcost.
  unfold depth in Hlog1, Hlog2.
  nia.
Qed.


(** *** Auxiliary: bound [log_2 (a + b)] when [a, b > 0].

    [log_2 a + log_2 b <= 2 * log_2 (a + b)] (when both are positive).
    This lets us state the final bound in terms of [a + b], matching
    the standard [O(log n)] formulation where [n = |q_1| + |q_2|]. *)
Lemma log2_sum_bound (a b : nat) :
  0 < a -> 0 < b ->
  Nat.log2 a + Nat.log2 b <= 2 * Nat.log2 (a + b).
Proof.
  intros Ha Hb.
  assert (Hle1 : a <= a + b) by lia.
  assert (Hle2 : b <= a + b) by lia.
  pose proof (Nat.log2_le_mono _ _ Hle1) as Hlog1.
  pose proof (Nat.log2_le_mono _ _ Hle2) as Hlog2.
  lia.
Qed.


(** *** Final asymptotic bound: [concat] is [O(log(|q_1| + |q_2|))].

    For nonempty inputs, the cost is bounded by a constant multiple of
    [log_2 (size q_1 + size q_2)] plus a constant.  This is the
    asymptotic statement [O(log n)] where [n] is the total input size. *)
Corollary concatD_cost_O_log_n (A : Type) `{LDA: LessDefined A, Hrefl: !Reflexive LDA}
    (q1 q2 : Seq A) (outD : SeqA A) :
  q1 <> Nil ->
  q2 <> Nil ->
  outD `is_approx` concat q1 q2 ->
  Tick.cost (concatD q1 q2 outD) <=
    2 * glue_cost_const_1 * Nat.log2 (size q1 + size q2)
    + glue_cost_const_2.
Proof.
  intros Hq1 Hq2 Happrox.
  pose proof (@concatD_cost_logsize A LDA Hrefl q1 q2 outD Hq1 Hq2 Happrox) as Hcost.
  pose proof (@size_pos A q1 Hq1) as Hpos1.
  pose proof (@size_pos A q2 Hq2) as Hpos2.
  pose proof (@log2_sum_bound (size q1) (size q2) Hpos1 Hpos2) as Hlog.
  unfold glue_cost_const_1, glue_cost_const_2 in *.
  nia.
Qed.


(** *** Theorem (informal restatement for thesis)

    For any two finite, nonempty finger trees [q_1, q_2 : Seq A]:
    
      cost(concat q_1 q_2) ≤ 16 * log_2 (|q_1| + |q_2|) + 60
    
    That is, [cost(concat q_1 q_2) = O(log(|q_1| + |q_2|))].
    
    This bound is worst-case (not amortized), and holds for every
    individual invocation of [concat].  The constant 16 = 2 * 8 reflects
    the looseness of the [log_2 a + log_2 b ≤ 2 * log_2 (a + b)]
    inequality; a sharper analysis would give 8. *)


(* ================================================================= *)
(** ** End of additions                                                 *)
(* ================================================================= *)