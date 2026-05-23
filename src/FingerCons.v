(** * FingerCons — fcons operation, demand analysis, and debt machinery *)

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

