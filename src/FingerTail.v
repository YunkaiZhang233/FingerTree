(** * FingerTail — ftail operation, demand analysis, and spec *)

From Coq Require Import Arith Psatz Relations RelationClasses List.
From Clairvoyance Require Import Core Approx ApproxM Tick Prod Option.
From Hammer Require Import Tactics.
From Clairvoyance Require Import FingerCore FingerCons FingerHead.

Import ListNotations.

Import Tick.Notations.
Open Scope tick_scope.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

#[local] Existing Instance Exact_id | 1.
#[local] Existing Instance Reflexive_LessDefined_T.
#[local] Existing Instance Reflexive_LessDefined_prodA.

From Clairvoyance Require Import Core.

(** ===== ftail ===== *)

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
   docs/CLAESSEN_REFERENCE.md.  Re-enable to confirm.

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
      [ftailA'] as a higher-order parameter.  Inlining keeps proofs
      flatter despite the depth.
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

Lemma debt_inverse_chop_demand_Thunk_le 
    {A B : Type} `{LessDefined B, Exact A B}
    (m : Seq (Tuple A)) (sD : SeqA (TupleA B)) (xD : T B) :
  @Debitable_T _ (@Debitable_SeqA (TupleA B)) (inverse_chop_demand m (Thunk sD) xD)
    <= @Debitable_T _ (@Debitable_SeqA (TupleA B)) (Thunk sD).
Proof.
  destruct sD as [| t | fD_sD mD_inner rD_sD].
  - simpl. unfold_debt. lia.
  - simpl. unfold_debt. lia.
  - simpl.
    destruct fD_sD as [d | ].
    + destruct d as [t1 | t1 t2 | t1 t2 t3]; sauto unfold:debt.
    + destruct m as [| | m_d _ _]; [| | destruct m_d]; sauto unfold:debt.
Qed.

Lemma debt_add_pair_to_head_demand_Thunk_le 
    {A B : Type} `{LessDefined B, Exact A B}
    (m : Seq (Tuple A)) (sD : SeqA (TupleA B)) (xD yD : T B) :
  @Debitable_T _ (@Debitable_SeqA (TupleA B)) (add_pair_to_head_demand m (Thunk sD) xD yD)
    <= @Debitable_T _ (@Debitable_SeqA (TupleA B)) (Thunk sD).
Proof.
  destruct sD as [| t | fD_sD mD_inner rD_sD].
  - simpl. unfold_debt. lia.
  - simpl. unfold_debt. lia.
  - simpl.
    destruct fD_sD as [d | ].
    + destruct d as [t1 | t1 t2 | t1 t2 t3]; sauto unfold:debt.
    + destruct m as [| | m_d _ _]; [| | destruct m_d]; sauto unfold:debt.
Qed.  

(** The main demand function. *)

Fixpoint ftailD' (A B : Type) `{Exact A B} (s : Seq A) (outD : SeqA B)
    : Tick (T (SeqA B)) :=
  Tick.tick >>
  match s with
  | Nil =>
      (* ftail Nil = Nil *)
      match outD with
      | NilA => Tick.ret (Thunk NilA)
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

Lemma ftailD'_val_more (A B : Type) `{LDB : LessDefined B, Exact A B}
    (a : Digit A) (m : Seq (Tuple A)) (r : Digit A) (outD : SeqA B) :
  outD `is_approx` ftail (More a m r) ->
  exists v, Tick.val (ftailD' (More a m r) outD) = Thunk v.
Proof.
  intros Happrox.
  destruct a as [t1 | t1 t2 | t1 t2 t3].
  - (* One t1 *)
    destruct m as [| t_m | fd_m m_spine r_d_m].
    + (* m = Nil *) 
      destruct r as [w | w w' | w w' w''].
      * (* r = One w. ftail = Unit w. outD ≤ UnitA _. *)
        simpl in Happrox. invert_clear Happrox.
        eexists. simpl. reflexivity.
      * (* r = Two w w'. ftail = More _ _ _. outD ≤ MoreA _ _ _. *)
        simpl in Happrox.
        destruct outD as [| | fD mD rD]; try (invert_clear Happrox; fail).
        eexists. simpl. reflexivity.
      * (* r = Three. ftail = More _ _ _. *)
        simpl in Happrox.
        destruct outD as [| | fD mD rD]; try (invert_clear Happrox; fail).
        cbn.
        repeat (match goal with
                | [ |- context [match ?x with _ => _ end] ] => destruct x; cbn
                end);
        eexists; reflexivity.

    + (* m = Unit t_m. case on head. *)
      simpl in Happrox.
      destruct t_m as [u u' | u u' u''].
      * (* head = Some (Pair u u') *)
        destruct outD as [| | fD mD rD]; try (invert_clear Happrox; fail).
        simpl.
        destruct fD as [ [ | | ] | ]; destruct mD as [ | ]; eexists; simpl; reflexivity.
      * (* head = Some (Triple u u' u'') *)
        destruct outD as [| | fD mD rD]; try (invert_clear Happrox; fail).
        simpl.
        destruct fD as [ [ | | ] | ]; destruct mD as [ | ]; eexists; simpl; reflexivity.
    + (* m = More _ _ _ *)
      destruct fd_m as [t_fd | t_fd t_fd' | t_fd t_fd' t_fd''];
      (destruct t_fd as [u u' | u u' u'']);
      simpl in Happrox;
      destruct outD as [| | fD mD rD]; try (invert_clear Happrox; fail); simpl;
      destruct fD as [ [ | | ] | ]; destruct mD as [ | ]; eexists; simpl; reflexivity.
  - (* Two t1 t2 *) 
    simpl in Happrox.
    destruct outD as [| | fD mD rD]; try (invert_clear Happrox; fail).
    eexists. simpl. reflexivity.
  - (* Three t1 t2 t3 *)
    simpl in Happrox.
    destruct outD as [| | fD mD rD]; try (invert_clear Happrox; fail).
    destruct fD as [ [ | | ] | ]; destruct mD as [ | ]; eexists; simpl; reflexivity.
Qed.
Opaque ftailD'_val_more.
(* ================================================================= *)
(** *** Big proofs for [ftailD'].

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
(** **** Main theorem: [ftailD'_approx]

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


(* ----------------------------------------------------------------- *)
(** **** Main theorem: [ftailD'_cost] (amortized cost bound). *)
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
  intros A B LDB EAB s. revert A s B LDB EAB.
  apply (ftail_ind (fun (A : Type) (s : Seq A) (s' : Seq A) =>
    forall B LDB EAB outD,
      outD `is_approx` s' ->
      let inM := ftailD' s outD in
      let cost := Tick.cost inM in
      let inD := Tick.val inM in
      debt inD + cost <= 3 + debt outD)).

  (* === Case 1: Nil → Nil === *)
  {
    intros A B LDB EAB outD Happrox.
    refine (match outD with
            | NilA => _
            | _ => _
            end); intros;
      try solve [ invert_clear Happrox ];
    simpl; sauto unfold:debt.
  }

  (* === Case 2: Unit _ → Nil === *)
  {
    intros A x B LDB EAB outD Happrox.
    refine (match outD with
            | NilA => _
            | _ => _
            end); intros;
      try solve [ invert_clear Happrox ];
    simpl; sauto unfold:debt.
  }

  (* === Case 3: More (Three a x y) m r → More (Two x y) m r === *)
  {
    intros A a x y m r B LDB EAB outD Happrox.
    refine (match outD with
            | MoreA fD mD rD => _
            | _ => _
            end); intros;
      try solve [ invert_clear Happrox ].
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ];
    simpl.
    destruct inD as [ fA | ].
    - destruct fA;
        try (invert_clear HfD; invert_clear H1; fail).
      all: sauto unfold:debt.
      (* TwoA t1 t2 *)
    - sauto unfold:debt.
    - sauto unfold:debt.
    - invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
    subst inM cost inD.   (* or: unfold inM, cost, inD *)
    simpl.
    destruct fD as [ fA | ].
      + destruct fA as [ t1 | t1 t2 | t1 t2 t3 ];
          try (invert_clear HfD; invert_clear H1; fail); sauto unfold:debt.
      + sauto unfold:debt.
  }

  (* === Case 4: More (Two a x) m r → More (One x) m r === *)
  {
    intros A a x m r B LDB EAB outD Happrox.
    refine (match outD with
            | MoreA fD mD rD => _
            | _ => _
            end); intros;
      try solve [ invert_clear Happrox ].
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
    simpl.
    destruct inD as [ fA | ].
    - destruct fA;
        try (invert_clear HfD; invert_clear H1; fail);
      sauto unfold:debt.
    - sauto unfold:debt.
    - sauto unfold:debt.
    - invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
    subst inM cost inD.   (* or: unfold inM, cost, inD *)
    simpl.
    destruct fD as [ fA | ].
      + destruct fA;
          try (invert_clear HfD; invert_clear H1; fail); sauto unfold:debt.
      + sauto unfold:debt.
  }

  (* === Case 5: More (One a) Nil (One y) → Unit y === *)
  {
    intros A a y B LDB EAB outD Happrox.
    refine (match outD with
            | UnitA yD => _
            | _ => _
            end); intros;
      try solve [ invert_clear Happrox ];
    simpl; sauto unfold:debt.
  }

  (* === Case 6: More (One a) Nil (Two y z) → More (One y) Nil (One z) === *)
  {
    intros A a y z B LDB EAB outD Happrox.
    refine (match outD with
            | MoreA fD mD rD => _
            | _ => _
            end); intros;
      try solve [ invert_clear Happrox ].
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ];
    simpl.
    destruct inD as [ fA | ]; [ destruct fA | ];
    sauto unfold:debt.
    all: invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
    all: subst inM cost inD.   (* or: unfold inM, cost, inD *)
    all: simpl.
    - lia.
    - lia.
  }

  (* === Case 7: More (One a) Nil (Three y z w) → More (One y) Nil (Two z w) === *)
  {
    intros A a y z w B LDB EAB outD Happrox.
    refine (match outD with
            | MoreA fD mD rD => _
            | _ => _
            end); intros;
      try solve [ invert_clear Happrox ].
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ];
    simpl.
    sauto unfold:debt.
    all: invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ]; simpl.
    {
      subst cost inM.
      sauto unfold:debt.
    }
    {
      subst cost inM inD.
      sauto unfold:debt.
    }
  }

  (* === Case 8: More (One a) m r, head m = Some (Pair x y), recursive === *)
  {
    intros A a x y m r IH Hhead B LDB EAB outD Happrox.
    destruct outD; try (invert_clear Happrox; fail).
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD_out HrD ].
    cbv zeta in IH.
    destruct m as [| t_m | fd_m m_spine r_d_m]; [ discriminate Hhead | | ].
  
  - (* m = Unit (Pair x y) *)
    simpl in Hhead. inversion Hhead. subst t_m. clear Hhead.
    destruct t0 as [ s_inner | ].
    {
      (* Thunk case *)
      invert_clear HmD_out as [ | ? ? HsD ].
      cbv zeta.
      invert_clear HsD.
      sauto unfold:debt.
    }
    {
      (* Undefined case *)
      invert_clear HmD_out.
      simpl.
      destruct t as [ [ | t_x t_x' | ] | ];
        try (invert_clear HfD; invert_clear H; fail);
        simpl;
      sauto unfold:debt.
    }

  - (* m = More fd_m m_spine r_d_m *)
    destruct fd_m as [t_m | t_m t_m' | t_m t_m' t_m''];
    simpl in Hhead; inversion Hhead; subst t_m; clear Hhead;
    cbv zeta.

    (* fd_m = One *)
    {
      destruct t0 as [ s_inner | ].
      (* Thunk s_inner *)
      {
        invert_clear HmD_out as [ | ? ? HsD ].
        specialize (IH _ _ _ s_inner HsD).
        destruct (Tick.val (ftailD' (More (One (Pair x y)) m_spine r_d_m) s_inner)) as [ sD | ] eqn:Erec.
        (* Thunk sD: recursion returned a Thunk *)
        {
          destruct t as [ [ | t_x t_x' | ] | ];
          try (invert_clear HfD; invert_clear H; fail).
          (* Thunk Two *)
          {
            change (Tick.val (ftailD' (More (One a) (More (One (Pair x y)) m_spine r_d_m) r) (MoreA (Thunk (TwoA t_x t_x')) (Thunk s_inner) t1)))
            with (Thunk (MoreA (Thunk (OneA Undefined)) 
                          (add_pair_to_head_demand (More (One (Pair x y)) m_spine r_d_m) 
                  (Tick.val (ftailD' (More (One (Pair x y)) m_spine r_d_m) s_inner)) t_x t_x') t1)).

            rewrite Erec.

            pose proof (debt_add_pair_to_head_demand_Thunk_le 
              (More (One (Pair x y)) m_spine r_d_m) sD t_x t_x') as Hhelper.
            assert (Hcost_eq : 
            Tick.cost (ftailD' (More (One a) (More (One (Pair x y)) m_spine r_d_m) r) 
                (MoreA (Thunk (TwoA t_x t_x')) (Thunk s_inner) t1))
            = S (Tick.cost (ftailD' (More (One (Pair x y)) m_spine r_d_m) s_inner))).
            {
              simpl. auto.
            }

            rewrite Hcost_eq.

            cbn -[ftailD' add_pair_to_head_demand] in *.
            change (debt (Thunk sD)) with (debt sD) in IH.
            unfold debt in *.
            lia.
          }
          (* Undefined *)
          {
            change (Tick.val (ftailD' (More (One a) (More (One (Pair x y)) m_spine r_d_m) r) 
                  (MoreA Undefined (Thunk s_inner) t1)))
            with (Thunk (MoreA (Thunk (OneA Undefined)) 
                          (add_pair_to_head_demand (More (One (Pair x y)) m_spine r_d_m) 
            (Tick.val (ftailD' (More (One (Pair x y)) m_spine r_d_m) s_inner)) Undefined Undefined) t1)).

            rewrite Erec.

            pose proof (debt_add_pair_to_head_demand_Thunk_le 
                          (More (One (Pair x y)) m_spine r_d_m) sD Undefined Undefined) as Hhelper.

            assert (Hcost_eq : 
              Tick.cost (ftailD' (More (One a) (More (One (Pair x y)) m_spine r_d_m) r) 
                                  (MoreA Undefined (Thunk s_inner) t1))
              = S (Tick.cost (ftailD' (More (One (Pair x y)) m_spine r_d_m) s_inner))).
            {
              simpl. auto.
            }

            rewrite Hcost_eq.

            cbn -[ftailD' add_pair_to_head_demand] in *.
            change (debt (Thunk sD)) with (debt sD) in IH.
            unfold debt in *.
            lia.
          }
        }
        (* Undefined *)
        {
          assert (Hv_exists : exists v, Tick.val (ftailD' (More (One (Pair x y)) m_spine r_d_m) s_inner) = Thunk v).
          { 
            eapply ftailD'_val_more. eassumption. 
          }
          destruct Hv_exists as [v Hv].
          rewrite Hv in Erec. discriminate.
          }
      }

      (* Undefined *)
      {
        destruct t as [ [ | t_x t_x' | ] | ];
          try (invert_clear HfD; invert_clear H; fail).
        
        (* Thunk *)
        {
          cbn -[ftailD' add_pair_to_head_demand].
          unfold debt in *.
          cbn in *.
          lia.
        }

        (* Undefined *)
        {
          cbn -[ftailD' add_pair_to_head_demand].
          unfold debt in *.
          cbn in *.
          lia.
        }
      }
    }

    (* fd_m = Two *)
    {
      destruct t0 as [ s_inner | ].
      
      (* Thunk *)
      {
        invert_clear HmD_out as [ | ? ? HsD ].
        specialize (IH _ _ _ s_inner HsD).
        destruct (Tick.val (ftailD' (More (Two (Pair x y) t_m') m_spine r_d_m) s_inner)) as [ sD | ] eqn:Erec.
        
        (* Thunk sD *)
        {
          destruct t as [ [ | t_x t_x' | ] | ];
            try (invert_clear HfD; invert_clear H; fail).
          
          (* TwoA *)
          {
            change (Tick.val (ftailD' (More (One a) (More (Two (Pair x y) t_m') m_spine r_d_m) r) 
                                       (MoreA (Thunk (TwoA t_x t_x')) (Thunk s_inner) t1)))
              with (Thunk (MoreA (Thunk (OneA Undefined)) 
                            (add_pair_to_head_demand (More (Two (Pair x y) t_m') m_spine r_d_m) 
                                                      (Tick.val (ftailD' (More (Two (Pair x y) t_m') m_spine r_d_m) s_inner)) 
                                                      t_x t_x') 
                            t1)).
            rewrite Erec.
            pose proof (debt_add_pair_to_head_demand_Thunk_le 
                          (More (Two (Pair x y) t_m') m_spine r_d_m) sD t_x t_x') as Hhelper.
            assert (Hcost_eq : 
              Tick.cost (ftailD' (More (One a) (More (Two (Pair x y) t_m') m_spine r_d_m) r) 
                                  (MoreA (Thunk (TwoA t_x t_x')) (Thunk s_inner) t1))
              = S (Tick.cost (ftailD' (More (Two (Pair x y) t_m') m_spine r_d_m) s_inner))).
            {
              simpl. auto.
            }
            rewrite Hcost_eq.
            cbn -[ftailD' add_pair_to_head_demand] in *.
            change (debt (Thunk sD)) with (debt sD) in IH.
            unfold debt in *.
            lia.
          }
          
          (* Undefined *)
          {
            change (Tick.val (ftailD' (More (One a) (More (Two (Pair x y) t_m') m_spine r_d_m) r) 
                                       (MoreA Undefined (Thunk s_inner) t1)))
              with (Thunk (MoreA (Thunk (OneA Undefined)) 
                            (add_pair_to_head_demand (More (Two (Pair x y) t_m') m_spine r_d_m) 
                                                      (Tick.val (ftailD' (More (Two (Pair x y) t_m') m_spine r_d_m) s_inner)) 
                                                      Undefined Undefined) 
                            t1)).
            rewrite Erec.
            pose proof (debt_add_pair_to_head_demand_Thunk_le 
                          (More (Two (Pair x y) t_m') m_spine r_d_m) sD Undefined Undefined) as Hhelper.
            assert (Hcost_eq : 
              Tick.cost (ftailD' (More (One a) (More (Two (Pair x y) t_m') m_spine r_d_m) r) 
                                  (MoreA Undefined (Thunk s_inner) t1))
              = S (Tick.cost (ftailD' (More (Two (Pair x y) t_m') m_spine r_d_m) s_inner))).
            {
              simpl. auto.
            }
            rewrite Hcost_eq.
            cbn -[ftailD' add_pair_to_head_demand] in *.
            change (debt (Thunk sD)) with (debt sD) in IH.
            unfold debt in *.
            lia.
          }
        }
        
        (* Undefined sD *)
        {
          assert (Hv_exists : exists v, Tick.val (ftailD' (More (Two (Pair x y) t_m') m_spine r_d_m) s_inner) = Thunk v).
          { 
            eapply ftailD'_val_more. eassumption. 
          }
          destruct Hv_exists as [v Hv].
          rewrite Hv in Erec. discriminate.
        }
      }
      
      (* Undefined *)
      {
        destruct t as [ [ | t_x t_x' | ] | ];
          try (invert_clear HfD; invert_clear H; fail).
        
        (* Thunk *)
        {
          cbn -[ftailD' add_pair_to_head_demand].
          unfold debt in *.
          cbn in *.
          lia.
        }
        
        (* Undefined *)
        {
          cbn -[ftailD' add_pair_to_head_demand].
          unfold debt in *.
          cbn in *.
          lia.
        }
      }
    }

    (* fd_m = Three *)
    {
      destruct t0 as [ s_inner | ].
      
      (* Thunk *)
      {
        invert_clear HmD_out as [ | ? ? HsD ].
        specialize (IH _ _ _ s_inner HsD).
        destruct (Tick.val (ftailD' (More (Three (Pair x y) t_m' t_m'') m_spine r_d_m) s_inner)) as [ sD | ] eqn:Erec.
        
        (* Thunk sD *)
        {
          destruct t as [ [ | t_x t_x' | ] | ];
            try (invert_clear HfD; invert_clear H; fail).
          
          (* TwoA *)
          {
            change (Tick.val (ftailD' (More (One a) (More (Three (Pair x y) t_m' t_m'') m_spine r_d_m) r) 
                                       (MoreA (Thunk (TwoA t_x t_x')) (Thunk s_inner) t1)))
              with (Thunk (MoreA (Thunk (OneA Undefined)) 
                            (add_pair_to_head_demand (More (Three (Pair x y) t_m' t_m'') m_spine r_d_m) 
                                                      (Tick.val (ftailD' (More (Three (Pair x y) t_m' t_m'') m_spine r_d_m) s_inner)) 
                                                      t_x t_x') 
                            t1)).
            rewrite Erec.
            pose proof (debt_add_pair_to_head_demand_Thunk_le 
                          (More (Three (Pair x y) t_m' t_m'') m_spine r_d_m) sD t_x t_x') as Hhelper.
            assert (Hcost_eq : 
              Tick.cost (ftailD' (More (One a) (More (Three (Pair x y) t_m' t_m'') m_spine r_d_m) r) 
                                  (MoreA (Thunk (TwoA t_x t_x')) (Thunk s_inner) t1))
              = S (Tick.cost (ftailD' (More (Three (Pair x y) t_m' t_m'') m_spine r_d_m) s_inner))).
            {
              simpl. auto.
            }
            rewrite Hcost_eq.
            cbn -[ftailD' add_pair_to_head_demand] in *.
            change (debt (Thunk sD)) with (debt sD) in IH.
            unfold debt in *.
            lia.
          }
          
          (* Undefined *)
          {
            change (Tick.val (ftailD' (More (One a) (More (Three (Pair x y) t_m' t_m'') m_spine r_d_m) r) 
                                       (MoreA Undefined (Thunk s_inner) t1)))
              with (Thunk (MoreA (Thunk (OneA Undefined)) 
                            (add_pair_to_head_demand (More (Three (Pair x y) t_m' t_m'') m_spine r_d_m) 
                                                      (Tick.val (ftailD' (More (Three (Pair x y) t_m' t_m'') m_spine r_d_m) s_inner)) 
                                                      Undefined Undefined) 
                            t1)).
            rewrite Erec.
            pose proof (debt_add_pair_to_head_demand_Thunk_le 
                          (More (Three (Pair x y) t_m' t_m'') m_spine r_d_m) sD Undefined Undefined) as Hhelper.
            assert (Hcost_eq : 
              Tick.cost (ftailD' (More (One a) (More (Three (Pair x y) t_m' t_m'') m_spine r_d_m) r) 
                                  (MoreA Undefined (Thunk s_inner) t1))
              = S (Tick.cost (ftailD' (More (Three (Pair x y) t_m' t_m'') m_spine r_d_m) s_inner))).
            {
              simpl. auto.
            }
            rewrite Hcost_eq.
            cbn -[ftailD' add_pair_to_head_demand] in *.
            change (debt (Thunk sD)) with (debt sD) in IH.
            unfold debt in *.
            lia.
          }
        }
        
        (* Undefined sD *)
        {
          assert (Hv_exists : exists v, Tick.val (ftailD' (More (Three (Pair x y) t_m' t_m'') m_spine r_d_m) s_inner) = Thunk v).
          { 
            eapply ftailD'_val_more. eassumption. 
          }
          destruct Hv_exists as [v Hv].
          rewrite Hv in Erec. discriminate.
        }
      }
      
      (* Undefined *)
      {
        destruct t as [ [ | t_x t_x' | ] | ];
          try (invert_clear HfD; invert_clear H; fail).
        
        (* Thunk *)
        {
          cbn -[ftailD' add_pair_to_head_demand].
          unfold debt in *.
          cbn in *.
          lia.
        }
        
        (* Undefined *)
        {
          cbn -[ftailD' add_pair_to_head_demand].
          unfold debt in *.
          cbn in *.
          lia.
        }
      }
    }

  }

  (* === Case 9: More (One a) m r, head m = Some (Triple x y z), non-recursive === *)
  {
    intros A a x y z m r Hhead B LDB EAB outD Happrox.
    destruct outD; try (invert_clear Happrox; fail).
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD_out HrD ].
    destruct m as [| t_m | fd_m m_spine r_d_m]; [ discriminate Hhead | | ].

    - (* m = Unit t_m, t_m = Triple x y z *)
      simpl in Hhead. inversion Hhead. subst t_m. clear Hhead.
      destruct t0 as [ s_inner | ].

      (* Thunk s_inner *)
      {
        invert_clear HmD_out as [ | ? ? HsD ].
        destruct t as [ [ t_x | | ] | ];
          try (invert_clear HfD; invert_clear H; fail).

        (* OneA t_x *)
        {
          change (Tick.val (ftailD' (More (One a) (Unit (Triple x y z)) r) 
                                      (MoreA (Thunk (OneA t_x)) (Thunk s_inner) t1)))
            with (Thunk (MoreA (Thunk (OneA Undefined)) 
                          (inverse_chop_demand (Unit (Triple x y z)) (Thunk s_inner) t_x) 
                          t1)).
          pose proof (debt_inverse_chop_demand_Thunk_le 
                        (Unit (Triple x y z)) s_inner t_x) as Hhelper.
          assert (Hcost_eq : 
            Tick.cost (ftailD' (More (One a) (Unit (Triple x y z)) r) 
                                (MoreA (Thunk (OneA t_x)) (Thunk s_inner) t1)) = 1).
          { 
            simpl. auto. 
          }
          cbv zeta.
          rewrite Hcost_eq.
          cbn -[inverse_chop_demand] in *.
          unfold debt in *.
          lia.
        }

        (* Undefined fD *)
        {
          change (Tick.val (ftailD' (More (One a) (Unit (Triple x y z)) r) 
                                      (MoreA Undefined (Thunk s_inner) t1)))
            with (Thunk (MoreA (Thunk (OneA Undefined)) 
                          (inverse_chop_demand (Unit (Triple x y z)) (Thunk s_inner) Undefined) 
                          t1)).
          pose proof (debt_inverse_chop_demand_Thunk_le 
                        (Unit (Triple x y z)) s_inner Undefined) as Hhelper.
          assert (Hcost_eq : 
            Tick.cost (ftailD' (More (One a) (Unit (Triple x y z)) r) 
                                (MoreA Undefined (Thunk s_inner) t1)) = 1).
          { 
            simpl. auto. 
          }
          cbv zeta.
          rewrite Hcost_eq.
          cbn -[inverse_chop_demand] in *.
          unfold debt in *.
          lia.
        }
      }

      (* Undefined mD_out *)
      {
        destruct t as [ [ t_x | | ] | ];
          try (invert_clear HfD; invert_clear H; fail).
        (* OneA t_x *)
        { 
          cbn -[ftailD' inverse_chop_demand]. unfold debt in *. cbn in *. lia. 
        }
        (* Undefined fD *)
        { 
          cbn -[ftailD' inverse_chop_demand]. unfold debt in *. cbn in *. lia. 
        }
      }

    - (* m = More fd_m m_spine r_d_m, fd_m has Triple x y z in first slot *)
      destruct fd_m as [ t_m | t_m t_m' | t_m t_m' t_m'' ];
        simpl in Hhead; inversion Hhead; subst t_m; clear Hhead.

      (* fd_m = One (Triple x y z) *)
      {
        destruct t0 as [ s_inner | ].

        (* Thunk s_inner *)
        {
          invert_clear HmD_out as [ | ? ? HsD ].
          destruct t as [ [ t_x | | ] | ];
            try (invert_clear HfD; invert_clear H; fail).

          (* OneA t_x *)
          {
            change (Tick.val (ftailD' (More (One a) (More (One (Triple x y z)) m_spine r_d_m) r) 
                                        (MoreA (Thunk (OneA t_x)) (Thunk s_inner) t1)))
              with (Thunk (MoreA (Thunk (OneA Undefined)) 
                            (inverse_chop_demand (More (One (Triple x y z)) m_spine r_d_m) (Thunk s_inner) t_x) 
                            t1)).
            pose proof (debt_inverse_chop_demand_Thunk_le 
                          (More (One (Triple x y z)) m_spine r_d_m) s_inner t_x) as Hhelper.
            assert (Hcost_eq : 
              Tick.cost (ftailD' (More (One a) (More (One (Triple x y z)) m_spine r_d_m) r) 
                                  (MoreA (Thunk (OneA t_x)) (Thunk s_inner) t1)) = 1).
            { 
              simpl. auto. 
            }
            cbv zeta.
            rewrite Hcost_eq.
            cbn -[inverse_chop_demand] in *.
            unfold debt in *.
            lia.
          }

          (* Undefined fD *)
          {
            change (Tick.val (ftailD' (More (One a) (More (One (Triple x y z)) m_spine r_d_m) r) 
                                        (MoreA Undefined (Thunk s_inner) t1)))
              with (Thunk (MoreA (Thunk (OneA Undefined)) 
                            (inverse_chop_demand (More (One (Triple x y z)) m_spine r_d_m) (Thunk s_inner) Undefined) 
                            t1)).
            pose proof (debt_inverse_chop_demand_Thunk_le 
                          (More (One (Triple x y z)) m_spine r_d_m) s_inner Undefined) as Hhelper.
            assert (Hcost_eq : 
              Tick.cost (ftailD' (More (One a) (More (One (Triple x y z)) m_spine r_d_m) r) 
                                  (MoreA Undefined (Thunk s_inner) t1)) = 1).
            { 
              simpl. auto. 
            }
            cbv zeta.
            rewrite Hcost_eq.
            cbn -[inverse_chop_demand] in *.
            unfold debt in *.
            lia.
          }
        }

        (* Undefined mD_out *)
        {
          destruct t as [ [ t_x | | ] | ];
            try (invert_clear HfD; invert_clear H; fail).
          { 
            cbn -[ftailD' inverse_chop_demand]. 
            unfold debt in *. cbn in *. 
            lia. 
          }
          { 
            cbn -[ftailD' inverse_chop_demand]. 
            unfold debt in *. cbn in *. 
            lia. 
          }
        }
      }

      (* fd_m = Two (Triple x y z) t_m' *)
      {
        destruct t0 as [ s_inner | ].

        (* Thunk s_inner *)
        {
          invert_clear HmD_out as [ | ? ? HsD ].
          destruct t as [ [ t_x | | ] | ];
            try (invert_clear HfD; invert_clear H; fail).

          (* OneA t_x *)
          {
            change (Tick.val (ftailD' (More (One a) (More (Two (Triple x y z) t_m') m_spine r_d_m) r) 
                                        (MoreA (Thunk (OneA t_x)) (Thunk s_inner) t1)))
              with (Thunk (MoreA (Thunk (OneA Undefined)) 
                            (inverse_chop_demand (More (Two (Triple x y z) t_m') m_spine r_d_m) (Thunk s_inner) t_x) 
                            t1)).
            pose proof (debt_inverse_chop_demand_Thunk_le 
                          (More (Two (Triple x y z) t_m') m_spine r_d_m) s_inner t_x) as Hhelper.
            assert (Hcost_eq : 
              Tick.cost (ftailD' (More (One a) (More (Two (Triple x y z) t_m') m_spine r_d_m) r) 
                                  (MoreA (Thunk (OneA t_x)) (Thunk s_inner) t1)) = 1).
            { 
              simpl. auto. 
            }
            cbv zeta.
            rewrite Hcost_eq.
            cbn -[inverse_chop_demand] in *.
            unfold debt in *.
            lia.
          }

          (* Undefined fD *)
          {
            change (Tick.val (ftailD' (More (One a) (More (Two (Triple x y z) t_m') m_spine r_d_m) r) 
                                        (MoreA Undefined (Thunk s_inner) t1)))
              with (Thunk (MoreA (Thunk (OneA Undefined)) 
                            (inverse_chop_demand (More (Two (Triple x y z) t_m') m_spine r_d_m) (Thunk s_inner) Undefined) 
                            t1)).
            pose proof (debt_inverse_chop_demand_Thunk_le 
                          (More (Two (Triple x y z) t_m') m_spine r_d_m) s_inner Undefined) as Hhelper.
            assert (Hcost_eq : 
              Tick.cost (ftailD' (More (One a) (More (Two (Triple x y z) t_m') m_spine r_d_m) r) 
                                  (MoreA Undefined (Thunk s_inner) t1)) = 1).
            { 
              simpl. auto. 
            }
            cbv zeta.
            rewrite Hcost_eq.
            cbn -[inverse_chop_demand] in *.
            unfold debt in *.
            lia.
          }
        }

        (* Undefined mD_out *)
        {
          destruct t as [ [ t_x | | ] | ];
            try (invert_clear HfD; invert_clear H; fail).
          { 
            cbn -[ftailD' inverse_chop_demand]. 
            unfold debt in *. cbn in *. 
            lia. 
          }
          { 
            cbn -[ftailD' inverse_chop_demand]. 
            unfold debt in *. cbn in *. 
            lia. 
          }
        }
      }

      (* fd_m = Three (Triple x y z) t_m' t_m'' *)
      {
        destruct t0 as [ s_inner | ].

        (* Thunk s_inner *)
        {
          invert_clear HmD_out as [ | ? ? HsD ].
          destruct t as [ [ t_x | | ] | ];
            try (invert_clear HfD; invert_clear H; fail).

          (* OneA t_x *)
          {
            change (Tick.val (ftailD' (More (One a) (More (Three (Triple x y z) t_m' t_m'') m_spine r_d_m) r) 
                                        (MoreA (Thunk (OneA t_x)) (Thunk s_inner) t1)))
              with (Thunk (MoreA (Thunk (OneA Undefined)) 
                            (inverse_chop_demand (More (Three (Triple x y z) t_m' t_m'') m_spine r_d_m) (Thunk s_inner) t_x) 
                            t1)).
            pose proof (debt_inverse_chop_demand_Thunk_le 
                          (More (Three (Triple x y z) t_m' t_m'') m_spine r_d_m) s_inner t_x) as Hhelper.
            assert (Hcost_eq : 
              Tick.cost (ftailD' (More (One a) (More (Three (Triple x y z) t_m' t_m'') m_spine r_d_m) r) 
                                  (MoreA (Thunk (OneA t_x)) (Thunk s_inner) t1)) = 1).
            { 
              simpl. auto. 
            }
            cbv zeta.
            rewrite Hcost_eq.
            cbn -[inverse_chop_demand] in *.
            unfold debt in *.
            lia.
          }

          (* Undefined fD *)
          {
            change (Tick.val (ftailD' (More (One a) (More (Three (Triple x y z) t_m' t_m'') m_spine r_d_m) r) 
                                        (MoreA Undefined (Thunk s_inner) t1)))
              with (Thunk (MoreA (Thunk (OneA Undefined)) 
                            (inverse_chop_demand (More (Three (Triple x y z) t_m' t_m'') m_spine r_d_m) (Thunk s_inner) Undefined) 
                            t1)).
            pose proof (debt_inverse_chop_demand_Thunk_le 
                          (More (Three (Triple x y z) t_m' t_m'') m_spine r_d_m) s_inner Undefined) as Hhelper.
            assert (Hcost_eq : 
              Tick.cost (ftailD' (More (One a) (More (Three (Triple x y z) t_m' t_m'') m_spine r_d_m) r) 
                                  (MoreA Undefined (Thunk s_inner) t1)) = 1).
            { 
              simpl. auto. 
            }
            cbv zeta.
            rewrite Hcost_eq.
            cbn -[inverse_chop_demand] in *.
            unfold debt in *.
            lia.
          }
        }

        (* Undefined mD_out *)
        {
          destruct t as [ [ t_x | | ] | ];
            try (invert_clear HfD; invert_clear H; fail).
          { 
            cbn -[ftailD' inverse_chop_demand]. unfold debt in *. cbn in *. lia. 
          }
          { 
            cbn -[ftailD' inverse_chop_demand]. unfold debt in *. cbn in *. lia. 
          }
        }
      }
  }
Qed.

(* Corollary at B := A. *)
Lemma ftailD_cost (A : Type) `{LessDefined A} (q : Seq A) (outD : SeqA A) :
  outD `is_approx` ftail q ->
  let inM := ftailD q outD in
  debt (Tick.val inM) + Tick.cost inM <= 3 + debt outD.
Proof.
  intros. apply ftailD'_cost. auto.
Qed.



(* Auxiliary lemmas *)
Lemma ftailD'_front_OneA_undef_pair (A B : Type) `{LDB : LessDefined B, Exact A B}
    (a b : A) (m_spine : Seq (Tuple (Tuple A))) (r_d_m : Digit (Tuple A))
    (s_out : SeqA (TupleA B))
    (Happrox : s_out `less_defined` exact (ftail (More (One (Pair a b)) m_spine r_d_m)))
    (fmD : T (DigitA (TupleA B))) (mmD : T (SeqA (TupleA (TupleA B)))) (rmD : T (DigitA (TupleA B)))
    (Hv : Tick.val (ftailD' (More (One (Pair a b)) m_spine r_d_m) s_out) = Thunk (MoreA fmD mmD rmD)) :
  fmD = Thunk (OneA Undefined).
Proof.
  destruct m_spine as [| t_ms | fd_ms ms r_d_ms].
  
  - (* m_spine = Nil *)
    (* ftail = Unit b OR More _ _ _ depending on r_d_m. Different structure. *)
    destruct r_d_m as [w | w w' | w w' w''].
    
    + (* r_d_m = One w. ftail = More (Two b w) Nil ... no wait *)
      (* Actually ftail (More (One (Pair a b)) Nil (One w)) goes via case 8/9 of ftail. 
         Hmm wait, head (Pair _ _) = Some (Pair _ _). So case 8 of ftail. *)
      (* But also m_spine = Nil, so ftail (More (One (Pair a b)) Nil (One w))
                 = More (Two a b) (ftail Nil) (One w) -- WAIT *)
      (* Let me check ftail directly: 
         ftail (More (One (Pair a b)) Nil r_d_m) 
         For More (One _) m r: case on m=Nil, then r.
         Actually for our m = Nil and r = One w, ftail goes to case 5: Unit w. 
         Wait that's only when the FRONT of s is One, m = Nil, r = One w. ftail = Unit w. *)
      (* So ftail (More (One (Pair a b)) Nil (One w)) = Unit w. 
         Then s_out ≤ exact (Unit w) = UnitA (exact w). *)
      
      (* ftailD' (More (One (Pair a b)) Nil (One w)) s_out: case m=Nil, r=One w.
         Match s_out with UnitA yD => Tick.ret (Thunk (MoreA (Thunk (OneA Undefined)) (Thunk NilA) (Thunk (OneA yD)))). 
         So front = Thunk (OneA Undefined). ✓ *)
      
      destruct s_out as [| t_so | ];
        try (invert_clear Happrox; fail).
      cbn in Hv. inversion Hv. reflexivity.
    
    + (* r_d_m = Two w w'. ftail = More (One w) Nil (One w'). *)
      destruct s_out as [| | fD' mD' rD' ];
        try (invert_clear Happrox; fail).
      cbn in Hv. inversion Hv. reflexivity.
    
    + (* r_d_m = Three w w' w''. ftail = More (One w) Nil (Two w' w''). *)
      destruct s_out as [| | fD' mD' rD' ];
        try (invert_clear Happrox; fail).
      cbn in Hv. inversion Hv. 
      destruct rD' as [ [ | s1 s2 | ] | ];
        simpl in Hv; inversion Hv; reflexivity.
  
  - (* m_spine = Unit t_ms. head (Unit t_ms) = Some t_ms. *)
    destruct t_ms as [u v | u v w].
    
    + (* t_ms = Pair u v. Pair case fires. *)
      destruct s_out as [| | fD' mD' rD' ];
        try (invert_clear Happrox; fail).
      cbn in Hv. inversion Hv. 
      destruct fD' as [ [ | t1 t2 | ] | ];
        cbn in Hv; inversion Hv; reflexivity.
    
    + (* t_ms = Triple u v w. Triple case fires. *)
      destruct s_out as [| | fD' mD' rD' ];
        try (invert_clear Happrox; fail).
      cbn in Hv. inversion Hv. reflexivity.
  
  - (* m_spine = More fd_ms ms r_d_ms. head = Some (first slot of fd_ms). *)
    destruct fd_ms as [t_fd | t_fd t_fd' | t_fd t_fd' t_fd''];
    destruct t_fd as [u v | u v w];
      destruct s_out as [| | fD' mD' rD' ];
        try (invert_clear Happrox; fail);
      cbn in Hv; inversion Hv; try reflexivity;
      destruct fD' as [ [ | t1 t2 | ] | ];
        cbn in Hv; inversion Hv; reflexivity.
Qed.

Lemma ftailD'_front_TwoA_undef_pair (A B : Type) `{LDB : LessDefined B, Exact A B}
    (a b : A) (t_m' : Tuple A) (m_spine : Seq (Tuple (Tuple A))) (r_d_m : Digit (Tuple A))
    (s_out : SeqA (TupleA B))
    (Happrox : s_out `less_defined` exact (ftail (More (Two (Pair a b) t_m') m_spine r_d_m)))
    (fmD : T (DigitA (TupleA B))) (mmD : T (SeqA (TupleA (TupleA B)))) (rmD : T (DigitA (TupleA B)))
    (Hv : Tick.val (ftailD' (More (Two (Pair a b) t_m') m_spine r_d_m) s_out) = Thunk (MoreA fmD mmD rmD)) :
  exists xD, fmD = Thunk (TwoA Undefined xD).
Proof.
  destruct s_out as [| | fD mD rD];
    try (invert_clear Happrox; fail).
  destruct fD as [ [ | tx ty | ] | ];
    cbn in Hv; inversion Hv; eexists; reflexivity.
Qed.

Lemma ftailD'_front_ThreeA_undef_pair (A B : Type) `{LDB : LessDefined B, Exact A B}
    (a b : A) (t_m' t_m'' : Tuple A) (m_spine : Seq (Tuple (Tuple A))) (r_d_m : Digit (Tuple A))
    (s_out : SeqA (TupleA B))
    (Happrox : s_out `less_defined` exact (ftail (More (Three (Pair a b) t_m' t_m'') m_spine r_d_m)))
    (fmD : T (DigitA (TupleA B))) (mmD : T (SeqA (TupleA (TupleA B)))) (rmD : T (DigitA (TupleA B)))
    (Hv : Tick.val (ftailD' (More (Three (Pair a b) t_m' t_m'') m_spine r_d_m) s_out) = Thunk (MoreA fmD mmD rmD)) :
  exists xD yD, fmD = Thunk (ThreeA Undefined xD yD).
Proof.
  destruct s_out as [| | fD mD rD];
    try (invert_clear Happrox; fail).
  destruct fD as [ [ | | tx ty tz ] | ];
    cbn in Hv; inversion Hv; eexists; eexists; reflexivity.
Qed.




(* ----------------------------------------------------------------- *)
(** **** Main theorem: [ftailD'_spec] (clairvoyance equivalence). *)
(* ----------------------------------------------------------------- *)


Lemma ftailD'_spec : forall (A B : Type)
    `{LDB : LessDefined B, !Reflexive LDB, !Transitive LDB, Exact A B}
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
  intros A B LDB HReflexive HTransitive EAB q outD Happrox qD HqD dcost.
  revert A q B LDB HReflexive HTransitive EAB outD Happrox qD HqD dcost.
  apply (ftail_ind
    (fun A q q' =>
       forall B `{LDB : LessDefined B, !Reflexive LDB, !Transitive LDB, Exact A B}
              (outD : SeqA B),
         outD `is_approx` q' ->
         forall qD, qD = Tick.val (ftailD' q outD) ->
           let dcost := Tick.cost (ftailD' q outD) in
           ftailA qD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]])).
  
  (* Case 1: q = Nil *)
  {
    intros A B LDB HReflexive HTransitive EAB outD Happrox qD HqD dcost.
    destruct outD; try (invert_clear Happrox; fail).
    subst. simpl. mgo_.
  }
  
  (* Case 2: q = Unit x *)
  {
    intros A x B LDB HReflexive HTransitive EAB outD Happrox qD HqD dcost.
    revert Happrox.
    destruct outD; intro Happrox; try (invert_clear Happrox; fail).
    subst. simpl. mgo_.
  }

  (* === Case 3: q = More (Three a x y) m r, q' = More (Two x y) m r === *)
  {
    intros A a x y m r B LDB HReflexive HTransitive EAB outD Happrox qD HqD dcost.
    revert Happrox.
    destruct outD; intro Happrox.
    - invert_clear Happrox.
    - invert_clear Happrox.
    - invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
      subst. simpl.
      keep_mgo_.
      destruct t as [ [ | t1' t2' | ] | ].
        * invert_clear HfD. invert_clear H.
        * invert_clear HfD. invert_clear H.
          simpl. keep_mgo_. 
        * invert_clear HfD. invert_clear H.
        * simpl. keep_mgo_. 
  }

  (* === Case 4: q = More (Two a x) m r, q' = More (One x) m r === *)
  {
    intros A a x m r B LDB HReflexive HTransitive EAB outD Happrox qD HqD dcost.
    revert Happrox.
    destruct outD; intro Happrox.
    - invert_clear Happrox.
    - invert_clear Happrox.
    - invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
      subst. simpl.
      keep_mgo_.
      destruct t as [ [ t1' | | ] | ].
        * (* OneA t1' — valid case *)
          invert_clear HfD. invert_clear H.
          simpl. keep_mgo_.
        * (* TwoA — contradicts HfD (exact = OneA _) *)
          invert_clear HfD. invert_clear H.
        * (* ThreeA — contradicts *)
          invert_clear HfD. invert_clear H.
        * (* Undefined *)
          simpl. keep_mgo_.
  }

  (* === Case 5: q = More (One a) Nil (One y), q' = Unit y === *)
  {
    intros A a y B LDB HReflexive HTransitive EAB outD Happrox qD HqD dcost.
    revert Happrox.
    destruct outD; intro Happrox.
    - invert_clear Happrox.
    - invert_clear Happrox.
      subst. simpl. keep_mgo_.
    - invert_clear Happrox.
  }

  (* === Case 6: q = More (One a) Nil (Two y z), q' = More (One y) Nil (One z) === *)
  {
    intros A a y z B LDB HReflexive HTransitive EAB outD Happrox qD HqD dcost.
    revert Happrox.
    destruct outD; intro Happrox.
    - invert_clear Happrox.
    - invert_clear Happrox.
    - invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
      subst. simpl.
      keep_mgo_.
      destruct t as [ [ t1' | | ] | ];
        try (invert_clear HfD; invert_clear H; fail);
      destruct t1 as [ [ s1 | | ] | ];
        try (invert_clear HrD; invert_clear H; fail).
      
      (* OneA t1' × OneA s1 *)
      { 
        invert_clear HfD. 
        invert_clear H. 
        invert_clear HrD. 
        invert_clear H.
        simpl. keep_mgo_. 
        reflexivity. 
      }
      (* OneA t1' × Undefined *)
      { 
        invert_clear HfD. 
        invert_clear H.
        simpl. keep_mgo_. 
      }
      (* Undefined × OneA s1 *)
      { 
        invert_clear HrD. 
        invert_clear H.
        simpl. keep_mgo_. 
      }
      (* Undefined × Undefined *)
      { 
        simpl. keep_mgo_. 
      }
      (* Undefined  ×  anything *)
      {
        invert_clear HrD.
        {
          constructor.
        }
        {
          invert_clear H. reflexivity.
        }
      }
  }
  (* === Case 7: q = More (One a) Nil (Three y z w), q' = More (One y) Nil (Two z w) === *)
  {
    intros A a y z w B LDB HReflexive HTransitive EAB outD Happrox qD HqD dcost.
    revert Happrox.
    destruct outD; intro Happrox.
    - invert_clear Happrox.
    - invert_clear Happrox.
    - invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
      subst. simpl.
      keep_mgo_.
      destruct t as [ [ t1' | | ] | ];
        try (invert_clear HfD; invert_clear H; fail);
      destruct t1 as [ [ | s1 s2 | ] | ];
        try (invert_clear HrD; invert_clear H; fail).
      (* OneA t1' × TwoA s1 s2 *)
      { 
        invert_clear HfD. 
        invert_clear H. 
        invert_clear HrD. 
        invert_clear H.
        - simpl. keep_mgo_.
        - simpl. keep_mgo_.
      }
      (* OneA t1' × Undefined *)
      { 
        invert_clear HfD. 
        invert_clear H.
        simpl. keep_mgo_. 
      }
      (* Undefined × TwoA s1 s2 *)
      { 
        invert_clear HrD. 
        invert_clear H.
        simpl. keep_mgo_. 
      }
      (* Undefined × Undefined *)
      { 
        simpl. keep_mgo_. 
      }
  }

  (* === Case 8: q = More (One a) m r, head m = Some (Pair x y), recursive === *)
  {
    intros A a x y m r IH Hhead B LDB HReflexive HTransitive EAB outD Happrox qD HqD dcost.
    revert Happrox.
    destruct outD; intro Happrox.
    - invert_clear Happrox.
    - invert_clear Happrox.
    - invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD_out HrD ].
      subst. simpl.
      
      (* Destruct m to handle head matching *)
      destruct m as [| t_m | fd_m m_spine r_d_m]; [discriminate Hhead | | ].
      
      (* m = Unit t_m, t_m = Pair x y *)
      + simpl in Hhead. inversion Hhead. subst t_m. clear Hhead.
        (* qD = Thunk (MoreA (Thunk (OneA Undefined)) mD_in rD) 
          where mD_in = add_pair_to_head_demand (Unit (Pair x y)) (Tick.val ...) xD yD *)
        destruct t0 as [ s_out | ].
        * (* Thunk s_out, mD_rec = Tick.val (ftailD' (Unit (Pair x y)) s_out) *)
          invert_clear HmD_out as [ | ? ? HsD ].
          (* HsD : s_out ≤ exact (ftail (Unit (Pair x y))) = NilA *)
          destruct t as [ [ | tx ty | ] | ];
            try (invert_clear HfD; invert_clear H; fail).
          (* Two *)
          {
            invert_clear HfD. invert_clear H.
            simpl. mgo_.
            inversion HsD; subst.
            (* Now s_out = NilA *)
            simpl.   (* reduce the match s_out *)
            (* Goal should now be simpler *)
            keep_mgo_.
          }
          (* Undefined *)
          {
            simpl. mgo_.
            inversion HsD; subst.
            simpl.
            keep_mgo_.
          }
        * (* Undefined *)
          simpl head. simpl.
          (* Now Some (Pair x y) branch is selected; thunkD Undefined fires *)
          destruct t as [ [ | tx ty | ] | ];
            try (invert_clear HfD; invert_clear H; fail).
          -- (* TwoA tx ty *)
            invert_clear HfD. invert_clear H.
            simpl. mgo_.
            apply optimistic_thunk_go. mgo_.
            apply optimistic_skip. mgo_.
          -- (* Undefined *)
            simpl. mgo_.
            apply optimistic_skip. mgo_.
            apply optimistic_skip. mgo_.
      
      (* m = More fd_m m_spine r_d_m *)
      + destruct fd_m as [ t_m | t_m t_m' | t_m t_m' t_m'' ];
          simpl in Hhead; inversion Hhead; subst t_m; clear Hhead.
        
        (* fd_m = One (Pair x y) *)
        { 
          destruct t0 as [ s_out | ].
          (* Thunk *)
          {
            invert_clear HmD_out as [ | ? ? HsD ].
            (* HsD : s_out ≤ Exact_Seq (ftail (More (One (Pair x y)) m_spine r_d_m)) *)
            
            destruct t as [ [ | tx ty | ] | ];
              try (invert_clear HfD; invert_clear H; fail).
            
            (* TwoA tx ty *)     
            - invert_clear HfD. invert_clear H.
              (* H : tx ≤ exact x, H0 : ty ≤ exact y *)
              
              simpl head.
              
              (* Get Tick.val's shape via ftailD'_val_more *)
              pose proof (@ftailD'_val_more (Tuple A) (TupleA B) _ _
                            (One (Pair x y)) m_spine r_d_m s_out HsD) as Hex.
              destruct Hex as [v Hv].
              
              (* Get the approx for v *)
              pose proof (@ftailD'_approx (Tuple A) (TupleA B) _ _ _
                            (More (One (Pair x y)) m_spine r_d_m) s_out HsD) as Happrox_v.
              rewrite Hv in Happrox_v.
              invert_clear Happrox_v.
              destruct v as [ | | fmD mmD rmD ];
                [ exfalso; clear -H1; invert_clear H1 |
                  exfalso; clear -H1; invert_clear H1 | ].
              invert_clear H1.
              (* Now: Hfmd : fmD ≤ ..., HmmD : mmD ≤ ..., HrmD : rmD ≤ ... *)
              
              (* Apply helper to force fmD = Thunk (OneA Undefined) *)
              pose proof (@ftailD'_front_OneA_undef_pair A B _ _
                            x y m_spine r_d_m s_out HsD fmD mmD rmD Hv) as Hfmd_undef.
              subst fmD.
              
              (* Now: fmD has been substituted to Thunk (OneA Undefined) *)
              simpl. mgo_. rewrite Hv.
              simpl.   (* reduce add_pair_to_head_demand *)
              
              (* Cascade clairvoyant forcings *)
              mgo_.
              
              (* `let~ f' := ret (TwoA tx ty) in` — force *)
              apply optimistic_thunk_go. mgo_. 
              
              (* `let~ m' := ftailA' m in` — force; this is the recursive call *)
              apply optimistic_thunk_go.

              (* Refold the unfolded body back to ftailA *)
              change (let! _ := tick in (fun m => match m with NilA => _ | UnitA t => _ | MoreA fmD mmD0 rmD0 => _ end) $! mmD)
                with (ftailA' (MoreA (Thunk (OneA (Thunk (PairA tx ty)))) mmD rmD)).
              
              (* Bridge from IH to the recursive call via optimistic_corelax *)
              change (ftailA' (MoreA (Thunk (OneA (Thunk (PairA tx ty)))) mmD rmD))
                with (ftailA (Thunk (MoreA (Thunk (OneA (Thunk (PairA tx ty)))) mmD rmD))).
              
              eapply optimistic_corelax; assert (HPreOrder: PreOrder LDB) by (constructor; assumption).

              + (* Show: ftailA (Thunk (MoreA (Thunk (OneA Undefined)) mmD rmD))
                          ≤ ftailA (Thunk (MoreA (Thunk (OneA (Thunk (PairA tx ty)))) mmD rmD)) *)
                (* mgo_. *)

                instantiate (1 := ftailA (Thunk (MoreA (Thunk (OneA Undefined)) mmD rmD))).

                apply ftailA_mon.
                repeat constructor; reflexivity.
              + red. intros x_in x_in' n_in n_in' Hx_le Hn_le HP.
              destruct HP as (y' & m & Hret & Hout_le & Hcost_le).
              cbn in Hret. inversion Hret. subst y' m.
              
              exists (MoreA (Thunk (TwoA tx ty)) (Thunk x_in') t1), 0.
              split.
              -- reflexivity.   (* ret X X 0 *)
              -- split.
                ++ etransitivity; [exact Hout_le | ].
                  constructor; [reflexivity | constructor; exact Hx_le | reflexivity].
                ++ lia.

            + (* IH application *)
              eapply optimistic_mon.
              {
                eapply (IH (TupleA B) _ _ _ _ s_out).
                - exact HsD. (* discriminate *)
                - auto.
              }
              {
                intros out_IH cost_IH [Hout_IH Hcost_IH].
                cbn.
                exists (MoreA (Thunk (TwoA tx ty)) (Thunk out_IH) t1), 0.
                split.
                + reflexivity.
                + split.
                  * constructor.
                    -- reflexivity.
                    -- constructor. exact Hout_IH.
                    -- reflexivity.
                  * lia.
              }
          
          (* Undefined *)
          (* Undefined t case *)
          - simpl head.
            
            pose proof (@ftailD'_val_more (Tuple A) (TupleA B) _ _
                                        (One (Pair x y)) m_spine r_d_m s_out HsD) as Hex.
            destruct Hex as [v Hv].
            
            pose proof (@ftailD'_approx (Tuple A) (TupleA B) _ _ _
                                        (More (One (Pair x y)) m_spine r_d_m) s_out HsD) as Happrox_v.
            rewrite Hv in Happrox_v.
            invert_clear Happrox_v.
            destruct v as [ | | fmD mmD rmD ];
              [ exfalso; clear -H; invert_clear H |
                exfalso; clear -H; invert_clear H | ].
            invert_clear H.
            
            pose proof (@ftailD'_front_OneA_undef_pair A B _ _
                                        x y m_spine r_d_m s_out HsD fmD mmD rmD Hv) as Hfmd_undef.
            subst fmD.
            
            simpl. mgo_. rewrite Hv.
            simpl.
            
            mgo_.
            
            apply optimistic_thunk_go. mgo_. 
            apply optimistic_thunk_go.
            
            change (let! _ := tick in (fun m => match m with NilA => _ | UnitA t => _ | MoreA fmD mmD0 rmD0 => _ end) $! mmD)
              with (ftailA' (MoreA (Thunk (OneA (Thunk (PairA Undefined Undefined)))) mmD rmD)).
            
            change (ftailA' (MoreA (Thunk (OneA (Thunk (PairA Undefined Undefined)))) mmD rmD))
              with (ftailA (Thunk (MoreA (Thunk (OneA (Thunk (PairA Undefined Undefined)))) mmD rmD))).
            
            eapply optimistic_corelax; assert (HPreOrder: PreOrder LDB) by (constructor; assumption).
            + instantiate (1 := ftailA (Thunk (MoreA (Thunk (OneA Undefined)) mmD rmD))).
              apply ftailA_mon.
              repeat constructor; reflexivity.
            + red. intros x_in x_in' n_in n_in' Hx_le Hn_le HP.
              destruct HP as (y' & m & Hret & Hout_le & Hcost_le).
              cbn in Hret. inversion Hret. subst y' m.
              exists (MoreA (Thunk (TwoA Undefined Undefined)) (Thunk x_in') t1), 0.
              split.
              -- reflexivity.
              -- split.
                ++ etransitivity; [exact Hout_le | ].
                   constructor; [reflexivity | constructor; exact Hx_le | reflexivity].
                ++ lia.
            + (* IH application *)
              eapply optimistic_mon.
              {
                eapply (IH (TupleA B) _ _ _ _ s_out).
                * exact HsD.
                * auto.
              }
              {
                intros out_IH cost_IH [Hout_IH Hcost_IH].
                cbn.
                exists (MoreA (Thunk (TwoA Undefined Undefined)) (Thunk out_IH) t1), 0.
                split.
                + reflexivity.
                + split.
                  * constructor.
                    -- auto.
                    -- constructor. exact Hout_IH.
                    -- reflexivity.
                  * lia.
              }
          }
          * (* mD_out = Undefined *)
            (* (* fd_m = One (Pair x y), Undefined mD_out *) *)
            invert_clear HmD_out.   (* mD_out = Undefined now substituted *)
            simpl head.
            
            destruct t as [ [ | tx ty | ] | ];
              try (invert_clear HfD; invert_clear H; fail).
            
            + (* TwoA tx ty *)
              invert_clear HfD. invert_clear H.
              simpl.
              
              (* Now qD = Thunk (MoreA (Thunk (OneA Undefined)) 
                                        (Thunk (MoreA (Thunk (OneA (Thunk (PairA tx ty)))) Undefined Undefined))
                                        t1) *)
              
              mgo_.
              
              (* let~ f' := ret (TwoA tx ty) — force *)
              apply optimistic_thunk_go. mgo_.
              
              (* let~ m' := ftailA' (MoreA _ Undefined Undefined) — skip *)
              apply optimistic_skip.
              
              mgo_.
            
            + (* Undefined *)
              simpl.
              mgo_.
              
              (* let~ f' := ret (TwoA Undefined Undefined) — skip (since front Undefined) *)
              apply optimistic_skip.

              mgo_. 
              
              (* let~ m' := ftailA' ... — skip *)
              apply optimistic_skip.
              
              mgo_.
        }
        
        (* fd_m = Two (Pair x y) t_m' *)
        {
          destruct t0 as [ s_out | ].
          
          (* Thunk s_out *)
          - invert_clear HmD_out as [ | ? ? HsD ].
            
            destruct s_out as [ | | s_fD s_mD s_rD ];
              try (invert_clear HsD; fail).
            invert_clear HsD.
            (* Hypotheses: H1 : s_fD ≤ ..., H2 : s_mD ≤ ..., H3 : s_rD ≤ ... *)
            
            destruct t as [ [ | tx ty | ] | ].
            + (* OneA - impossible *)
              invert_clear HfD. invert_clear H2.
            
            + (* TwoA tx ty *)
              invert_clear HfD. invert_clear H2.
              simpl. mgo_.
              destruct s_fD as [ [ s_xD | | ] | ];
                try (invert_clear H; invert_clear H; fail).
              -- (* OneA s_xD *)
                invert_clear H. invert_clear H.
                simpl. mgo_.
                apply optimistic_thunk_go. mgo_.
                apply optimistic_thunk_go. mgo_.
                apply optimistic_thunk_go. mgo_.
              -- (* Undefined *)
                simpl. mgo_.
                apply optimistic_thunk_go. mgo_.
                apply optimistic_thunk_go. mgo_.
                apply optimistic_thunk_go. mgo_. 

            + (* ThreeA: also impossible. *)
              invert_clear HfD. invert_clear H2. 
            
            (* Undefined t *)
            + simpl. mgo_.
              destruct s_fD as [ [ s_xD | | ] | ];
                try (invert_clear H; invert_clear H; fail).
              -- (* OneA s_xD *)
                invert_clear H. invert_clear H.
                simpl. mgo_.
                apply optimistic_thunk_go. mgo_.
                apply optimistic_thunk_go. mgo_.
                apply optimistic_thunk_go. mgo_.
              -- (* Undefined *)
                simpl. mgo_.
                apply optimistic_thunk_go. mgo_.
                apply optimistic_thunk_go. mgo_.
                apply optimistic_thunk_go. mgo_.      
          
          (* Undefined mD_out *)
          - invert_clear HmD_out.
            simpl head.
            
            destruct t as [ [ | tx ty | ] | ];
              try (invert_clear HfD; invert_clear H; fail).
            
            + (* TwoA tx ty *)
              invert_clear HfD. invert_clear H.
              simpl.
              mgo_.
              apply optimistic_thunk_go. mgo_.
              apply optimistic_skip. mgo_.
            + (* Undefined *)
              simpl.
              mgo_.
              apply optimistic_skip. mgo_.
              apply optimistic_skip. mgo_.
        }
        
        (* fd_m = Three (Pair x y) t_m' t_m'' *)
        {
          destruct t0 as [ s_out | ].
          
          (* Thunk s_out *)
          - invert_clear HmD_out as [ | ? ? HsD ].
            destruct s_out as [ | | s_fD s_mD s_rD ];
              try (invert_clear HsD; fail).
            invert_clear HsD.
            (* Hypotheses: H1 : s_fD ≤ ..., H2 : s_mD ≤ ..., H3 : s_rD ≤ ... *)
            
            destruct t as [ [ | tx ty | ] | ].
            + (* OneA - impossible *)
              invert_clear HfD. invert_clear H2.
            + (* TwoA tx ty *)
              invert_clear HfD. invert_clear H2.
              simpl. mgo_.
              destruct s_fD as [ [ | s_xD s_yD | ] | ];
                try (invert_clear H; invert_clear H; fail).
              -- (* TwoA s_xD s_yD *)
                invert_clear H. invert_clear H.
                simpl. mgo_.
                apply optimistic_thunk_go. mgo_.
                apply optimistic_thunk_go. mgo_.
                apply optimistic_thunk_go. mgo_.
              -- (* Undefined *)
                simpl. mgo_.
                apply optimistic_thunk_go. mgo_.
                apply optimistic_thunk_go. mgo_.
                apply optimistic_thunk_go. mgo_.
            + (* ThreeA: also impossible. *)
              invert_clear HfD. invert_clear H2.
            
            (* Undefined t *)
            + simpl. mgo_.
              destruct s_fD as [ [ | s_xD s_yD | ] | ];
                try (invert_clear H; invert_clear H; fail).
              -- (* TwoA s_xD s_yD *)
                invert_clear H. invert_clear H.
                simpl. mgo_.
                apply optimistic_thunk_go. mgo_.
                apply optimistic_thunk_go. mgo_.
                apply optimistic_thunk_go. mgo_.
              -- (* Undefined *)
                simpl. mgo_.
                apply optimistic_thunk_go. mgo_.
                apply optimistic_thunk_go. mgo_.
                apply optimistic_thunk_go. mgo_.
          
          (* Undefined mD_out *)
          - invert_clear HmD_out.
            simpl head.
            destruct t as [ [ | tx ty | ] | ];
              try (invert_clear HfD; invert_clear H; fail).
            + (* TwoA tx ty *)
              invert_clear HfD. invert_clear H.
              simpl.
              mgo_.
              apply optimistic_thunk_go. mgo_.
              apply optimistic_skip. mgo_.
            + (* Undefined *)
              simpl.
              mgo_.
              apply optimistic_skip. mgo_.
              apply optimistic_skip. mgo_.
        }
  }

  (* === Case 9: q = More (One a) m r, head m = Some (Triple x y z), non-recursive === *)
  {
    intros A a x y z m r Hhead B LDB HReflexive HTransitive EAB outD Happrox qD HqD dcost.
    revert Happrox.
    destruct outD; intro Happrox.
    - invert_clear Happrox.
    - invert_clear Happrox.
    - invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD_out HrD ].
      subst. simpl.
      
      (* Need to destruct m to expose head m = Some (Triple x y z) *)
      destruct m as [| t_m | fd_m m_spine r_d_m]; [ discriminate Hhead | | ].
      
      (* m = Unit t_m, t_m = Triple x y z *)
      + simpl in Hhead. inversion Hhead. subst t_m. clear Hhead.
        keep_mgo_.
        destruct t as [ [ t_x | | ] | ];
          try (invert_clear HfD; invert_clear H; fail).
        (* OneA t_x *)
        { 
          invert_clear HfD. invert_clear H.
          simpl. keep_mgo_. 
          destruct t0 as [ s_inner | ].
          - (* Thunk s_inner, HmD_out : Thunk s_inner ≤ Thunk (UnitA (exact (Pair y z))) *)
            invert_clear HmD_out as [ | ? ? HsD ].
            (* HsD : s_inner ≤ UnitA (exact (Pair y z)) *)
            destruct s_inner as [| t_pair | ];
              try (invert_clear HsD; fail).
            (* UnitA t_pair *)
            invert_clear HsD.
            (* H0 : t_pair ≤ Thunk (PairA (exact y) (exact z)) *)
            simpl.   (* unfold inverse_chop_demand at Unit case *)
            destruct t_pair as [ pA | ].
            + (* Thunk pA, pA ≤ PairA (exact y) (exact z) *)
              invert_clear H0.
              invert_clear H0.
              (* pA = PairA t_y t_z with t_y ≤ exact y, t_z ≤ exact z *)
              simpl.   (* inverse_chop_tuple t_x (Thunk (PairA t_y t_z)) = Thunk (TripleA t_x t_y t_z) *)
              mgo_. keep_mgo_.
            + (* Undefined *)
              simpl.   (* inverse_chop_tuple t_x Undefined = Thunk (TripleA t_x Undefined Undefined) *)
              mgo_. keep_mgo_.
          - (* Undefined *)
            simpl.   (* inverse_chop_demand (Unit _) Undefined t_x = Thunk (UnitA (Thunk (TripleA t_x Undefined Undefined))) *)
            mgo_. keep_mgo_.
        }
        (* Undefined *)
        { 
          simpl. keep_mgo_.
          destruct t0 as [ s_inner | ].
          - invert_clear HmD_out as [ | ? ? HsD ].
            destruct s_inner as [| t_pair | ]; try (invert_clear HsD; fail).
            invert_clear HsD.
            destruct t_pair as [ pA | ];
              [invert_clear H; invert_clear H | ];
              simpl; mgo_;
              keep_mgo_.
          - simpl; keep_mgo_.
        }
      
      (* m = More fd_m m_spine r_d_m *)
      + destruct fd_m as [ t_m | t_m t_m' | t_m t_m' t_m'' ];
          simpl in Hhead; inversion Hhead; subst t_m; clear Hhead.
        (* fd_m = One (Triple x y z) *)
        { 
          keep_mgo_.
          destruct t as [ [ t_x | | ] | ];
            try (invert_clear HfD; invert_clear H; fail).
          { 
            invert_clear HfD. invert_clear H. simpl. keep_mgo_.
            destruct t0 as [ s_inner | ].
            - (* Thunk s_inner. HmD_out : Thunk s_inner ≤ Thunk (MoreA ...) *)
              invert_clear HmD_out as [ | ? ? HsD ].
              (* HsD : s_inner ≤ MoreA (exact (One (Pair y z))) (Thunk (Exact_Seq m_spine)) (exact r_d_m) *)
              destruct s_inner as [| | fD' mD' rD' ];
                try (invert_clear HsD; fail).
              invert_clear HsD.   (* gives HfD' : fD' ≤ ..., HmD' : mD' ≤ ..., HrD' : rD' ≤ ... *)
              
              destruct fD' as [ dA | ].
              + (* Thunk dA *)
                invert_clear H0.   (* H1 : dA ≤ OneA (Thunk (exact (Pair y z))) *)
                destruct dA as [ t_inner | | ];
                  try (invert_clear H1; fail).
                (* OneA t_inner *)
                invert_clear H1.   (* H3 : t_inner ≤ Thunk (exact (Pair y z)) *)
                simpl.
                (* Now inverse_chop_digit t_x (OneA t_inner) = OneA (inverse_chop_tuple t_x t_inner). *)
                destruct t_inner as [ pA | ].
                * (* Thunk pA *)
                  invert_clear H0.
                  invert_clear H0.   (* pA = PairA t_y t_z with t_y, t_z ≤ exact y, z *)
                  simpl. 
                  mgo_.
                  repeat (apply optimistic_thunk_go; mgo_).
                  keep_mgo_;
                    repeat constructor; try assumption; try reflexivity.
                  invert_clear H0.
                  simpl.
                  keep_mgo_.
                  
                * (* Undefined *)
                  simpl.
                  mgo_.
                  repeat (apply optimistic_thunk_go; mgo_).
                * invert_clear H0.   (* H3 : t_inner ≤ Thunk (exact (Pair y z)) *)
                  destruct t_inner as [ pA | ].
                  {
                    invert_clear H0.
                    (* New hypothesis: pA ≤ PairA (exact y) (exact z) *)
                    match goal with
                    | H : pA `less_defined` _ |- _ => invert_clear H
                    end.
                    simpl.
                    keep_mgo_.
                  }
                  {
                    simpl. keep_mgo_.
                  }
                * invert_clear H0.
                * invert_clear H0.
              + (* Undefined fD' *)
                (* Helper uses undef_inverse_chop_digit (One _) t_x = OneA (Thunk (TripleA t_x Undefined Undefined)) *)
                simpl.
                mgo_.
                repeat (apply optimistic_thunk_go; mgo_).

            - (* t0 = Undefined *)
              simpl.
              mgo_.
              repeat (apply optimistic_thunk_go; mgo_).
          }
          { 
            simpl. keep_mgo_. 

            destruct t0 as [ s_inner | ].
            - (* Thunk s_inner *)
              invert_clear HmD_out as [ | ? ? HsD ].
              destruct s_inner as [| | fD' mD' rD' ];
                try (invert_clear HsD; fail).
              invert_clear HsD.
              
              destruct fD' as [ dA | ].
              + destruct dA as [ t_inner | t1' t2' | t1' t2' t3' ].
                * (* OneA t_inner *)
                  (* split on mD' for the Goal-3 analog and on t_inner *)
                  destruct mD' as [ x0 | ];
                  destruct t_inner as [ pA | ].

                    (* Handle each combination *)
                  (* OneA-Thunk-x0-Thunk-pA: same as Goal 3 with Undefined as front *)
                  {
                    invert_clear H.
                    invert_clear H.   (* OneA-OneA: gives Thunk pA ≤ Thunk (PairA ...) *)
                    invert_clear H.   (* Thunk-Thunk: gives pA ≤ PairA _ _ *)
                    invert_clear H.   (* PairA-PairA: gives t_y, t_z, and constraints *)

                    (* Now pA is destructured *)
                    simpl. 
                    keep_mgo_.
                  }
                  (* OneA-Thunk-x0-Undefined: ... *)
                  {
                    invert_clear H.
                    invert_clear H.
                    invert_clear H.
                    simpl.
                    keep_mgo_.
                  }
                  (* OneA-Undefined-Thunk-pA: same as Goal 1 with Undefined as front *)
                  {
                    invert_clear H.
                    invert_clear H.
                    invert_clear H.
                    invert_clear H.
                    simpl.
                    keep_mgo_.
                  }
                  (* OneA-Undefined-Undefined: same as Goal 2 with Undefined as front *)
                  {
                    invert_clear H.
                    invert_clear H.
                    invert_clear H.
                    simpl.
                    keep_mgo_.
                  }
                * (* TwoA — discharge via H0 *)
                  repeat (invert_clear H).   (* or whatever the new name is *)
                * (* ThreeA — discharge via H0 *)
                  repeat (invert_clear H).
              + (* Undefined fD' — uses undef_inverse_chop_digit (One _) Undefined *)
                simpl.
                mgo_.
                keep_mgo_.

            - (* t0 = Undefined *)
              simpl.
              mgo_.
              keep_mgo_.
          }
        }
        (* fd_m = Two (Triple x y z) t_m' *)
        { 
          keep_mgo_.
          destruct t as [ [ t_x | | ] | ];
            try (invert_clear HfD; invert_clear H; fail).
          { 
            invert_clear HfD. invert_clear H. simpl. 
            destruct t0 as [ s_inner | ].
            - (* Thunk s_inner *)
              invert_clear HmD_out as [ | ? ? HsD ].
              destruct s_inner as [| | fD' mD' rD' ];
                try (invert_clear HsD; fail).
              invert_clear HsD.
              
              destruct fD' as [ dA | ].
              + destruct dA as [ | t_inner t2 | ].
                * (* OneA — impossible *)
                  invert_clear H0. invert_clear H0.
                * (* TwoA t_inner t2 — valid *)
                  invert_clear H0. invert_clear H0.
                  destruct t_inner as [ pA | ].
                  -- (* Thunk pA *)
                    match goal with H : Thunk pA `less_defined` _ |- _ => invert_clear H end.
                    destruct pA as [ t_y t_z | t_y t_z t_w ];
                      try (match goal with H : _ `less_defined` _ |- _ => invert_clear H end; fail).
                    match goal with H : PairA _ _ `less_defined` _ |- _ => invert_clear H end.
                    simpl.
                    mgo_.
                    repeat (apply optimistic_thunk_go; mgo_).
                  -- (* Undefined *)
                    simpl.
                    mgo_.
                    repeat (apply optimistic_thunk_go; mgo_).
                * (* ThreeA — impossible *)
                  invert_clear H0. invert_clear H0.
              + (* Undefined fD' *)
                simpl.
                mgo_.
                repeat (apply optimistic_thunk_go; mgo_).

            - (* t0 = Undefined *)
              simpl.
              mgo_.
              repeat (apply optimistic_thunk_go; mgo_). 
          }
          { 
            simpl.
            destruct t0 as [ s_inner | ].
            - (* Thunk s_inner *)
              invert_clear HmD_out as [ | ? ? HsD ].
              destruct s_inner as [| | fD' mD' rD' ];
                try (invert_clear HsD; fail).
              invert_clear HsD.
              
              destruct fD' as [ dA | ].
              + destruct dA as [ | t_inner t2 | ].
                * invert_clear H. invert_clear H.
                * (* TwoA t_inner t2 *)
                  match goal with H : Thunk (TwoA _ _) `less_defined` _ |- _ => invert_clear H end.
                  match goal with H : TwoA _ _ `less_defined` _ |- _ => invert_clear H end.
                  destruct t_inner as [ pA | ].
                  -- (* Thunk pA *)
                    match goal with H : Thunk pA `less_defined` _ |- _ => invert_clear H end.
                    destruct pA as [ t_y t_z | t_y t_z t_w ];
                      try (match goal with H : _ `less_defined` _ |- _ => invert_clear H end; fail).
                    match goal with H : PairA _ _ `less_defined` _ |- _ => invert_clear H end.
                    simpl.
                    mgo_.
                    repeat (apply optimistic_thunk_go; mgo_).
                  -- (* Undefined *)
                    simpl.
                    mgo_.
                    repeat (apply optimistic_thunk_go; mgo_).
                * invert_clear H. invert_clear H.
              + (* Undefined fD' *)
                simpl.
                mgo_.
                repeat (apply optimistic_thunk_go; mgo_).

            - (* t0 = Undefined *)
              simpl.
              mgo_.
              repeat (apply optimistic_thunk_go; mgo_).
          }
        }
        (* fd_m = Three (Triple x y z) t_m' t_m'' *)
        { 
          keep_mgo_.
          destruct t as [ [ t_x | | ] | ];
            try (invert_clear HfD; invert_clear H; fail).
          { 
            invert_clear HfD. invert_clear H. simpl. keep_mgo_.
            destruct t0 as [ s_inner | ].
            - (* Thunk s_inner *)
              invert_clear HmD_out as [ | ? ? HsD ].
              destruct s_inner as [| | fD' mD' rD' ];
                try (invert_clear HsD; fail).
              invert_clear HsD.
              
              destruct fD' as [ dA | ].
              + (* Thunk dA *)
                destruct dA as [ | | t_inner t2 t3 ].
                * (* OneA — impossible *)
                  repeat (invert_clear H0).
                * (* TwoA — impossible *)
                  repeat (invert_clear H0).
                * (* ThreeA t_inner t2 t3 — valid *)
                  (* H : Thunk (ThreeA t_inner t2 t3) ≤ exact (Three (Pair y z) t_m' t_m'') *)
                  invert_clear H0.
                  invert_clear H0.
                  simpl. 
                  destruct t_inner as [ pA | ].
                  {
                    invert_clear H0.
                    destruct pA as [ t_y t_z | t_y t_z t_w ]; try invert_clear H0.
                    simpl.
                    keep_mgo_.
                  }
                  {
                    simpl.
                    keep_mgo_.
                  }
                  
                  
              + (* Undefined fD' *)
                simpl.
                mgo_.
                repeat (apply optimistic_thunk_go; mgo_).

            - (* t0 = Undefined *)
              simpl.
              mgo_.
              repeat (apply optimistic_thunk_go; mgo_).
          }
          { 
            simpl. 
            destruct t0 as [ s_inner | ].
            - (* Thunk s_inner *)
              invert_clear HmD_out as [ | ? ? HsD ].
              destruct s_inner as [| | fD' mD' rD' ];
                try (invert_clear HsD; fail).
              invert_clear HsD.
              
              destruct fD' as [ dA | ].
              + destruct dA as [ | | t_inner t2 t3 ].
                * match goal with H : Thunk (OneA _) `less_defined` _ |- _ => invert_clear H; invert_clear H end.
                  (* or whatever discharges OneA ≤ ThreeA *)
                * match goal with H : Thunk (TwoA _ _) `less_defined` _ |- _ => invert_clear H; invert_clear H end.
                * (* ThreeA t_inner t2 t3 — valid *)
                  match goal with H : Thunk (ThreeA _ _ _) `less_defined` _ |- _ => invert_clear H end.
                  match goal with H : ThreeA _ _ _ `less_defined` _ |- _ => invert_clear H end.
                  destruct t_inner as [ pA | ].
                  -- (* Thunk pA *)
                    match goal with H : Thunk pA `less_defined` _ |- _ => invert_clear H end.
                    destruct pA as [ t_y t_z | t_y t_z t_w ];
                      try (match goal with H : _ `less_defined` _ |- _ => invert_clear H end; fail).
                    match goal with H : PairA _ _ `less_defined` _ |- _ => invert_clear H end.
                    simpl.
                    mgo_.
                    repeat (apply optimistic_thunk_go; mgo_).
                  -- (* Undefined *)
                    simpl.
                    mgo_.
                    repeat (apply optimistic_thunk_go; mgo_).
              + (* Undefined fD' *)
                simpl.
                mgo_.
                repeat (apply optimistic_thunk_go; mgo_).

            - (* t0 = Undefined *)
              simpl.
              mgo_.
              repeat (apply optimistic_thunk_go; mgo_).
          }
        }
  }
Qed.

(* Corollary at B := A. *)
Lemma ftailD_spec (A : Type) `{LDA : LessDefined A, !Reflexive LDA, !Transitive LDA}
    (q : Seq A) (outD : SeqA A) :
  outD `is_approx` ftail q ->
  forall qD, qD = Tick.val (ftailD q outD) ->
    let dcost := Tick.cost (ftailD q outD) in
    ftailA qD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros. apply ftailD'_spec; auto.
Qed.

