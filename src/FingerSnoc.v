(** * FingerSnoc — fsnoc operation, demand analysis, and debt machinery

    Symmetric counterpart of [FingerCons.v]: appends an element to the
    REAR of a finger tree.  Every lemma here has a direct dual in
    [FingerCons.v]; the proof structure and case shapes mirror that file
    with front/rear swapped.

    See Claessen 2020 §8 for the symmetric treatment of cons/snoc.

    Debit machinery ([Debitable_T], [Debitable_SeqA], [safe_DigitA],
    [safe_T], and their sub-additivity lemmas) lives in [FingerCore.v]
    — NOT redefined here. *)


From Coq Require Import Arith Psatz Relations RelationClasses List.
From Clairvoyance Require Import Core Approx ApproxM Tick Prod Option.
From Hammer Require Import Tactics.
From Clairvoyance Require Import FingerCore.

Import ListNotations.

Import Tick.Notations.
Open Scope tick_scope.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

#[local] Existing Instance Exact_id | 1.
(* ================================================================= *)
(** ** Operations                                                      *)
(* ================================================================= *)

(** *** snoc — insert at the rear

    Three cases (mirror of [fcons]):
    - [Nil]:   become a singleton.
    - [Unit y]: promote to [More] with front [One y], rear [One x],
      empty middle.
    - [More f m r]:
      + [r = One a]:     grow to [Two a x].
      + [r = Two a b]:   grow to [Three a b x].
      + [r = Three a b c]: overflow!  Keep [Two c x] at the rear,
        bundle [a] and [b] into [Pair a b] and snoc it into the middle.
        The rear goes from dangerous (Three) to safe (Two). *)

Fixpoint fsnoc {A : Type} (s : Seq A) (x : A) : Seq A :=
  match s with
  | Nil              =>
      let u' := x in
      Unit u'
  | Unit y           =>
      let f' := One y in
      let m' := Nil in
      let r' := One x in
      More f' m' r'
  | More f m r =>
      let (m, r) :=
        match r with
        | One a =>
            let r' := Two a x in
            (m, r')
        | Two a b =>
            let r' := Three a b x in
            (m, r')
        | Three a b c =>
            let pab := Pair a b in
            let m' := fsnoc m pab in
            let r' := Two c x in
            (m', r')
        end in
      More f m r
  end.


(** *** Custom induction principle for [fsnoc] *)
Lemma fsnoc_ind :
  forall (P : forall (A : Type), A -> Seq A -> Seq A -> Prop),
    (forall A x, P A x Nil (Unit x)) ->
    (forall A x y, P A x (Unit y) (More (One y) Nil (One x))) ->
    (forall A x a f m, P A x (More f m (One a)) (More f m (Two a x))) ->
    (forall A x a b f m, P A x (More f m (Two a b)) (More f m (Three a b x))) ->
    (forall A x a b c f m,
        P (Tuple A) (Pair a b) m (fsnoc m (Pair a b)) ->
        P A x (More f m (Three a b c)) (More f (fsnoc m (Pair a b)) (Two c x))) ->
    forall A (x : A) (s : Seq A), P A x s (fsnoc s x).
Proof.
  intros ? H1 H2 H3 H4 H5. fix SELF 3. intros ? x s.
  refine (match s with
          | Nil => _
          | Unit y => _
          | More f m (One a) => _
          | More f m (Two a b) => _
          | More f m (Three a b c) => _
          end).
  - apply H1.
  - apply H2.
  - apply H3.
  - apply H4.
  - apply H5. apply SELF.
Qed.

(** *** Helper: [fsnoc] on a non-[Nil] sequence always produces [More]. *)
Lemma fsnoc_go_deep (A : Type) (x : A) (q : Seq A) :
  (q <> Nil) -> exists f m r, fsnoc q x = More f m r.
Proof.
  intro H. destruct q.
  - contradiction.
  - exists (One a), Nil, (One x). reflexivity.
  - destruct d0.
    + exists d, q, (Two a x). reflexivity.
    + exists d, q, (Three a a0 x). reflexivity.
    + exists d, (fsnoc q (Pair a a0)), (Two a1 x). reflexivity.
Qed.


(* ================================================================= *)
(** ** Section 2: Clairvoyant version [fsnocA']                        *)
(* ================================================================= *)

From Clairvoyance Require Import Core.

(* Note that this definition *is* maximally lazy. *)
Fixpoint fsnocA' (A : Type) (q : SeqA A) (x : T A) : M (SeqA A) :=
  tick >>
  (match q with
  | NilA =>
      ret (UnitA x)
  | UnitA y =>
      let~ f' := ret (OneA y) in
      let~ m' := ret NilA in
      let~ r' := ret (OneA x) in
      ret (MoreA f' m' r')
  | MoreA f m r =>
      let! r_val := force r in
      match r_val with
      | OneA a =>
          let~ r' := ret (TwoA a x) in
          ret (MoreA f m r')
      | TwoA a b =>
          let~ r' := ret (ThreeA a b x) in
          ret (MoreA f m r')
      | ThreeA a b c =>
          let~ r' := ret (TwoA c x) in
          let~ pab := ret (PairA a b) in
          (* The termination checker rejects the imperative form
             let! m := force m in ... ; use forcing instead. *)
          let~ m' := forcing m (fun m => fsnocA' m pab) in
          ret (MoreA f m' r')
      end
  end).


Definition fsnocA (A : Type) (q : T (SeqA A)) (x : T A) : M (SeqA A) :=
  forcing q (fun q => fsnocA' q x).

Lemma fsnocA_mon (A : Type) `{LDA : LessDefined A, PreOrder A LDA} x' x (q' q : T (SeqA A))
  : x' `less_defined` x ->
    q' `less_defined` q ->
    fsnocA q' x' `less_defined` fsnocA q x.
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
           ++ (* pab demand *)
              intros x11 x12 Hx1112.
              invert_clear H2; try solve [solve_mon].
              invert_clear IH as [? IH |]; try solve [solve_mon].
              apply bind_mon.
              ** apply thunk_mon. simpl.
                 apply IH; try solve [auto]. typeclasses eauto.
              ** intros x13 x14 Hx1314. apply ret_mon. solve_mon.
           ++ (* Thunk case of Hx910 *)
              apply bind_mon; try solve [ solve_mon ].
              intros x11 x12 Hx1112.
              invert_clear H2; try solve [solve_mon].
              invert_clear IH as [? IH |]; try solve [solve_mon].
              apply bind_mon.
              ** apply thunk_mon. simpl.
                 apply IH; try solve [auto]. typeclasses eauto.
              ** intros x13 x14 Hx1314. apply ret_mon. solve_mon.
Qed.


(* ================================================================= *)
(** ** Section 3: Demand function [fsnocD']                            *)
(* ================================================================= *)

Fixpoint fsnocD' (A B : Type) `{Exact A B}
    (s : Seq A) (x : A) (outD : SeqA B)
    : Tick (T (SeqA B)) :=
  Tick.tick >>
  match s with
  | Nil =>
      (* fsnoc Nil x = Unit x *)
      match outD with
      | UnitA _ => Tick.ret (Thunk NilA)
      | _       => bottom
      end

  | Unit y =>
      (* fsnoc (Unit y) x = More (One y) Nil (One x) *)
      match outD with
      | MoreA fD _ _ =>
          let yD := match fD with
                    | Thunk (OneA yD) => yD
                    | _               => Undefined
                    end in
          Tick.ret (Thunk (UnitA yD))
      | _ => bottom
      end

  | More f m (One a) =>
      (* fsnoc (More f m (One a)) x = More f m (Two a x) *)
      match outD with
      | MoreA fD mD rD =>
          let aD := match rD with
                    | Thunk (TwoA aD _) => aD
                    | _                 => Undefined
                    end in
          Tick.ret (Thunk (MoreA fD mD (Thunk (OneA aD))))
      | _ => bottom
      end

  | More f m (Two a b) =>
      (* fsnoc (More f m (Two a b)) x = More f m (Three a b x) *)
      match outD with
      | MoreA fD mD rD =>
          let '(aD, bD) := match rD with
                           | Thunk (ThreeA aD bD _) => (aD, bD)
                           | _                      => (Undefined, Undefined)
                           end in
          Tick.ret (Thunk (MoreA fD mD (Thunk (TwoA aD bD))))
      | _ => bottom
      end

  | More f m (Three a b c) =>
      (* fsnoc (More f m (Three a b c)) x = More f (fsnoc m (Pair a b)) (Two c x) *)
      match outD with
      | MoreA fD mD rD =>
          let cD := match rD with
                    | Thunk (TwoA cD _) => cD
                    | _                 => Undefined
                    end in
          let+ mD_in := thunkD (fsnocD' m (Pair a b)) mD in
          Tick.ret (Thunk (MoreA fD mD_in (Thunk (ThreeA (exact a) (exact b) cD))))
      | _ => bottom
      end
  end.

Definition fsnocD (A : Type) : Seq A -> A -> SeqA A -> Tick (T (SeqA A)) :=
  fsnocD'.

Lemma fsnocD'_approx : forall (A B : Type)
    `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (s : Seq A) (x : A) (outD : SeqA B),
    outD `is_approx` fsnoc s x ->
    Tick.val (fsnocD' s x outD) `is_approx` s.
Proof.
  intros ? ? LDB RLDB EAB ? ? ?. revert A x s B LDB RLDB EAB outD.
  apply (fsnoc_ind (fun A x s s' =>
    forall B `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
           (outD : SeqA B),
      outD `less_defined` exact s' ->
      Tick.val (fsnocD' s x outD) `less_defined` exact s)); intros until outD.
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
            | MoreA _ _ _ => _
            | _ => bottom
            end); intro Happrox; teardown;
      repeat match goal with
        | H : ?x `less_defined` ?y |- _ =>
            (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
        end; repeat constructor; auto.
  }
  (* More f m (One a) *)
  {
    refine (match outD with
            | MoreA _ _ _ => _
            | _ => _
            end); try solve [ repeat constructor; reflexivity ].
    intro Happrox. teardown; repeat match goal with
        | H : ?x `less_defined` ?y |- _ =>
            (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
        end; repeat constructor; auto.
  }
  (* More f m (Two a b) *)
  {
    intro Happrox.
    refine (match outD as o
              return o `less_defined` exact (More f m (Three a b x)) ->
                    Tick.val (fsnocD' (More f m (Two a b)) x o) `less_defined`
                    exact (More f m (Two a b))
            with
            | MoreA fD mD rD => _
            | _ => _
            end Happrox); clear Happrox; try auto.
    intro Happrox.
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
    simpl.
    destruct rD as [ rA | ].
    * (* rD = Thunk rA *)
      destruct rA as [ t1 | t1 t2 | t1 t2 t3 ].
      -- (* OneA — contradicts HrD *)
         invert_clear HrD. invert_clear H0.
      -- (* TwoA — contradicts HrD *)
         invert_clear HrD. invert_clear H0.
      -- (* ThreeA t1 t2 t3 *)
         invert_clear HrD. invert_clear H0.
         repeat constructor; assumption.
    * (* rD = Undefined *)
      simpl. repeat constructor; try assumption.
  }
  (* More f m (Three a b c) *)
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
      destruct rD as [ rA | ].
      * (* rD = Thunk rA *)
        destruct rA as [ t1 | t1 t2 | t1 t2 t3 ].
        -- (* OneA — contradicts HrD *)
          invert_clear HrD. invert_clear H1.
        -- (* TwoA *)
          invert_clear HrD. invert_clear H1.
          repeat match goal with
          | H : ?x `less_defined` ?y |- _ =>
              (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
          end; repeat constructor; auto; reflexivity.
        -- (* ThreeA — contradicts HrD *)
          invert_clear HrD. invert_clear H1.
      * (* rD = Undefined *)
        repeat match goal with
          | H : ?x `less_defined` ?y |- _ =>
              (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
          end; repeat constructor; auto; reflexivity.
    }
    (* Subgoal 2: mD' = Thunk mA — recursive call *)
    {
      specialize (H _ _ _ _ mA HmA).
      simpl.
      destruct (Tick.val (fsnocD' m (Pair a b) mA)) as [ sD | ] eqn:EfsnocD.
      * (* Thunk sD *)
        destruct rD as [ rA | ].
        -- destruct rA as [ t1 | t1 t2 | t1 t2 t3 ].
          ++ (* OneA — contradicts HrD *)
              invert_clear HrD. invert_clear H1.
          ++ (* TwoA *)
              invert_clear HrD. invert_clear H1.
              simpl.
              repeat match goal with
              | H : ?x `less_defined` ?y |- _ =>
                  (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
              end; repeat constructor; auto; reflexivity.
          ++ (* ThreeA — contradicts HrD *)
              invert_clear HrD. invert_clear H1.
        -- (* rD = Undefined *)
          simpl.
          repeat match goal with
              | H : ?x `less_defined` ?y |- _ =>
                  (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
              end; repeat constructor; auto; reflexivity.
      * (* Undefined *)
        destruct rD as [ rA | ].
        -- destruct rA as [ t1 | t1 t2 | t1 t2 t3 ].
          ++ invert_clear HrD. invert_clear H1.
          ++ invert_clear HrD. invert_clear H1.
              simpl.
              repeat match goal with
              | H : ?x `less_defined` ?y |- _ =>
                  (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
              end; repeat constructor; auto; reflexivity.
          ++ invert_clear HrD. invert_clear H1.
        -- simpl.
           repeat match goal with
              | H : ?x `less_defined` ?y |- _ =>
                  (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
              end; repeat constructor; auto; reflexivity.
    }
  }
Qed.

Corollary fsnocD_approx (A : Type) `{LDA : LessDefined A, !Reflexive LDA}
  (q : Seq A) (x : A) (outD : SeqA A) :
  outD `is_approx` fsnoc q x -> Tick.val (fsnocD' q x outD) `is_approx` q.
Proof.
  eapply fsnocD'_approx.
Qed.

Lemma fsnocD'_exact (A B : Type) `{Exact A B} (s : Seq A) (x : A) :
  Tick.val (fsnocD' s x (exact (fsnoc s x))) = exact s.
Proof.
  generalize dependent B. generalize dependent A.
  induction s.
  - (* Nil *) reflexivity.
  - (* Unit *) reflexivity.
  - (* More f m r *)
    destruct d0 as [| | a b c].
    + (* One *) reflexivity.
    + (* Two *) reflexivity.
    + (* Three a b c *)
      simpl. intros.
      unfold exact in IHs.
      rewrite (IHs (Pair a b) (TupleA B) _).
      reflexivity.
Qed.


(* ================================================================= *)
(** ** Section 4: Spec lemma [fsnocD'_spec]                            *)
(* ================================================================= *)

#[local] Existing Instance Reflexive_LessDefined_T.
#[local] Existing Instance Reflexive_LessDefined_prodA.

Lemma fsnocD'_spec (A B : Type) :
  forall `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (s : Seq A) (x : A) (outD : SeqA B),
    outD `is_approx` fsnoc s x ->
    forall sD, sD = Tick.val (fsnocD' s x outD) ->
      let dcost := Tick.cost (fsnocD' s x outD) in
      fsnocA sD (exact x) [[ fun out cost =>
                               outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros LDB HReflexive EAB s x outD Happrox sD HsD dcost.
  revert A x s B LDB HReflexive EAB outD Happrox sD HsD dcost.
  apply (fsnoc_ind
    (fun A x s s' =>
       forall B `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
              (outD : SeqA B),
         outD `is_approx` s' ->
         forall sD, sD = Tick.val (fsnocD' s x outD) ->
           let dcost := Tick.cost (fsnocD' s x outD) in
           fsnocA sD (exact x) [[ fun out cost =>
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
    - (* fD: destruct since yD comes from fD *)
      destruct t as [ [ | | ] | ].
      + reflexivity.
      + invert_clear Ht. invert_clear H.
      + invert_clear Ht. invert_clear H.
      + constructor.
    - exact Ht0.
    - exact Ht1.
  }
  (* Case 3: s = More f m (One a), s' = More f m (Two a x) *)
  {
    intros A x a f m B LDB HReflexive EAB outD Happrox sD HsD dcost.
    revert Happrox.
    destruct outD; intro Happrox; try (invert_clear Happrox; fail).
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
    subst. simpl.
    keep_mgo_.
    (* Force the rear digit — need to case split on t1 *)
    destruct t1 as [ [ | | ] | ].
      * (* OneA *)
        invert_clear HrD. invert_clear H.
      * (* TwoA *)
        invert_clear HrD. invert_clear H.
        simpl. solve [solve_mon].
      * (* ThreeA — contradicts HrD *)
        invert_clear HrD. invert_clear H.
      * (* Undefined *)
        simpl. repeat constructor.
  }

  (* Case 4: s = More f m (Two a b), s' = More f m (Three a b x) *)
  {
    intros A x a b f m B LDB HReflexive EAB outD Happrox sD HsD dcost.
    revert Happrox.
    destruct outD; intro Happrox; try (invert_clear Happrox; fail).
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
    subst. simpl.
    keep_mgo_.
    destruct t1 as [ [ | | ] | ].
      * (* OneA — contradicts HrD *)
        invert_clear HrD. invert_clear H.
      * (* TwoA — contradicts HrD since exact rear = ThreeA *)
        invert_clear HrD. invert_clear H.
      * (* ThreeA *)
        invert_clear HrD. invert_clear H.
        simpl. keep_mgo_.
      * (* Undefined *)
        simpl. keep_mgo_.
  }

  (* Case 5: s = More f m (Three a b c), s' = More f (fsnoc m (Pair a b)) (Two c x) *)
  {
    intros A x a b c f m IH B LDB HReflexive EAB outD Happrox sD HsD dcost.
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
        change (((fun m0 => fsnocA' m0 (Thunk (PairA (exact a) (exact b)))) $! Tick.val (fsnocD' m (Pair a b) mA))) with (fsnocA (Tick.val (fsnocD' m (Pair a b) mA)) (exact (Pair a b))).
        eapply IH; try eauto. typeclasses eauto.
      }
      {
        intros ? ? [Hout Hcost]. keep_mgo_.
        (* field-level goals: use HfD, HrD, Hout, Hcost *)
        destruct t1 as [ [ | | ] | ];
                  try (invert_clear HrD; invert_clear H);
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

      destruct t1 as [ [ | | ] | ];
      try (invert_clear HrD; invert_clear H);
      simpl; repeat constructor; try assumption; reflexivity.
    }
  }
Qed.

Corollary fsnocD_spec (A : Type) :
  forall `{LDA : LessDefined A, !Reflexive LDA}
    (s : Seq A) (x : A) (outD : SeqA A),
    outD `is_approx` fsnoc s x ->
    forall sD, sD = Tick.val (fsnocD s x outD) ->
      let dcost := Tick.cost (fsnocD s x outD) in
      fsnocA sD (exact x) [[ fun out cost =>
                               outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros. eapply fsnocD'_spec; eauto.
Qed.


(* ================================================================= *)
(** ** Section 5: Cost lemmas                                          *)
(* ================================================================= *)

(** Debit machinery ([Debitable_T], [Debitable_SeqA], [safe_DigitA],
    [safe_T], [safe_DigitA_lub_subadditive], [safe_T_lub_subadditive],
    [debt_SeqA_lub_subadditive]) lives in [FingerCore.v]. *)

Lemma fsnocD'_cost : forall (A B : Type) `{LessDefined B, Exact A B}
    (s : Seq A) (x : A) (outD : SeqA B),
    outD `is_approx` fsnoc s x ->
    let inM := fsnocD' s x outD in
    let cost := Tick.cost inM in
    let inD := Tick.val inM in
    debt inD + cost <= 2 + debt outD.
Proof.
  intros A B LDB EAB s x. revert A x s B LDB EAB.
  apply (fsnoc_ind (fun (A : Type) (x : A) (s : Seq A) (s' : Seq A) =>
    forall B LDB EAB outD,
      outD `is_approx` s' ->
      let inM := fsnocD' s x outD in
      let cost := Tick.cost inM in
      let inD := Tick.val inM in
      debt inD + cost <= 2 + debt outD)).

  (* Nil: fsnoc Nil x = Unit x *)
  {
    intros A x B LDB EAB outD Happrox.
    destruct outD; try (invert_clear Happrox; fail).
    simpl. lia.
  }

  (* Unit y: fsnoc (Unit y) x = More (One y) Nil (One x) *)
  {
    intros A x y B LDB EAB outD Happrox.
    destruct outD; try (invert_clear Happrox; fail).
    simpl. lia.
  }

  (* One a: fsnoc (More f m (One a)) x = More f m (Two a x) *)
  {
    intros A x a f m B LDB EAB outD Happrox.
    destruct outD; try (invert_clear Happrox; fail).
    simpl.
    destruct t1 as [ [ | | ] | ]; simpl; sauto unfold:debt.
  }

  (* Two a b: fsnoc (More f m (Two a b)) x = More f m (Three a b x) *)
  {
    intros A x a b f m B LDB EAB outD Happrox.
    destruct outD; try (invert_clear Happrox; fail).
    simpl.
    destruct t1 as [ [ | | ] | ]; simpl; sauto unfold:debt.
  }

  (* Three a b c: RECURSIVE
       fsnoc (More f m (Three a b c)) x = More f (fsnoc m (Pair a b)) (Two c x) *)
  {
    intros A x a b c f m IH B LDB EAB outD Happrox.
    destruct outD; try (invert_clear Happrox; fail).
    invert_clear Happrox as [ | | ? ? ? ? ? ? HfD HmD HrD ].
    simpl.
    destruct t0 as [ mA | ].

    (* Thunk mA — recursive call fires *)
    {
      simpl.
      invert_clear HmD as [ | ? ? HmA ].
      specialize (IH _ _ _ mA HmA).
      simpl in IH.
      destruct (Tick.val (fsnocD' m (Pair a b) mA)) as [ sD | ].
      (* Thunk sD *)
      {
        assert (HIH : debt sD + Tick.cost (fsnocD' m (Pair a b) mA) <= 2 + debt mA).
        {
          change (debt (Thunk sD)) with (debt sD) in IH.
          change (debt (Thunk mA)) with (debt mA) in IH.
          lia.
        }
        destruct t1 as [ rA | ].
        - (* Thunk rA *)
          destruct rA as [ | | ].
          + (* OneA — contradicts HrD *)
            exfalso. invert_clear HrD. invert_clear H.
          + (* TwoA — the valid case *)
            cbn in *. lia.
          + (* ThreeA — contradicts HrD *)
            exfalso. invert_clear HrD. invert_clear H.
        - (* Undefined *)
          simpl debt in *.
          destruct t as [ dA | ].
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
      destruct t1 as [ [ | | ] | ]; simpl; sauto unfold:debt.
    }
  }

  (* Undefined — middle not demanded *)
  {
    simpl thunkD. simpl Tick.val. simpl Tick.cost.
    destruct t as [ [ | | ] | ]; destruct t1 as [ [ | | ] | ]; simpl; lia.
  }
  }
Qed.


Corollary fsnocD_cost (A : Type) `{LessDefined A}
    (s : Seq A) (x : A) (outD : SeqA A) :
    outD `is_approx` fsnoc s x ->
    let inM := fsnocD s x outD in
    let cost := Tick.cost inM in
    let inD := Tick.val inM in
    debt inD + cost <= 2 + debt outD.
Proof.
  intros. apply fsnocD'_cost. auto.
Qed.

Lemma fsnocD'_cost_bottom (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (s : Seq A) (x : A) :
  let inM := fsnocD' s x (bottom_of (exact (fsnoc s x))) in
  debt (Tick.val inM) + Tick.cost inM <= 3.
Proof.
  destruct s as [ | y | f m r ].
  - (* s = Nil *)
    simpl. lia.
  - (* s = Unit y *)
    simpl. lia.
  - (* s = More f m r *)
    destruct r as [ a | a b | a b c ]; simpl; lia.
Qed.
