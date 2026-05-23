(** * FingerPhysicist — empty operation and the physicist's argument *)

From Coq Require Import Arith Psatz Relations RelationClasses List.
From Clairvoyance Require Import Core Approx ApproxM Tick Prod Option.
From Hammer Require Import Tactics.
From Clairvoyance Require Import FingerCore FingerCons FingerSnoc FingerHead FingerTail.

Import ListNotations.

Import Tick.Notations.
Open Scope tick_scope.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

#[local] Existing Instance Exact_id | 1.
#[local] Existing Instance Reflexive_LessDefined_T.
#[local] Existing Instance Reflexive_LessDefined_prodA.
#[local] Existing Instance Transitive_LessDefined_T.
#[local] Existing Instance Transitive_LessDefined_prodA.

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
  | Head
  | FTail.

  (* --- eval: pure semantics --- *)
  #[export] Instance eval : Eval op value :=
    fun op args => match op, args with
                | Empty, [] => [empty]
                | FCons x, [q] => [fcons x q]
                | Head, [q] => []  (* Head returns an element, not a queue *)
                | FTail, [q] => [ftail q]
                | _, _ => []
                end.

  (* --- budget: amortized cost per operation --- *)
  #[export] Instance budget : Budget op value :=
    fun o _ => 4.

  (* --- exec: clairvoyant semantics --- *)
  #[export] Instance exec : Exec op valueA :=
    fun o args => match o, args with
               | Empty, [] => let! q := emptyA in ret [Thunk q]
               | FCons x, [q] => let! q' := fconsA (exact x) q in ret [Thunk q']
               | Head, [q] => let! _ := headA q in ret []
               | FTail, [q] => let! q' := ftailA q in ret [Thunk q']
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
    - (* FTail *)
      invert_clear H0; try solve [ solve_mon ].
      apply bind_mon.
      + apply ftailA_mon. assumption.
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
      | FTail, [q], [outD] =>
          let outD := forceD (bottom_of (exact (ftail q))) outD in
          let+ qD := ftailD q outD in
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
    (* FTail *)
    {
      destruct args as [ | q args' ]; [ intro; simpl; apply bottom_is_least; reflexivity | ].
      destruct args' as [ | ? ? ]; [ | intro; simpl; apply bottom_is_least; reflexivity ].
      destruct output as [ | outD output' ];
        [intros; simpl; apply bottom_is_least; reflexivity | ].
      destruct output' as [ | ? ? ];
      [ | intro; simpl; apply bottom_is_least; reflexivity ].
      (* args = [q], output = [outD] *)
      intro Happrox.
      invert_clear Happrox as [ | ? ? ? ? HoutD _ ].
      simpl.
      assert (Hin : forceD (bottom_of (exact (ftail q))) outD `less_defined` exact (ftail q)).
      {
        destruct outD as [ outA | ]; simpl.
        - invert_clear HoutD. assumption.
        - apply bottom_is_least. reflexivity.
      }
      eapply ftailD_approx in Hin.
      simpl. repeat constructor. exact Hin.
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
    - (* FTail *)
      simpl. intro args0.
      refine (match args0 with
              | [] => _
              | [q] => _
              | _ => _
              end); try solve [ invert_clear 1; invert_clear 1; mgo_ ].
      invert_clear 1.
      invert_clear H0.
      intros n xD HxD.
      unfold demand in HxD. simpl in HxD.
      rename x into outD.
      destruct (ftailD q (forceD (bottom_of (exact (ftail q))) outD))
        as [n_inner qD] eqn:EftailD.
      simpl in HxD. invert_clear HxD.
      mgo_.
      eapply optimistic_mon; [ eapply ftailD_spec | ].
      + eapply less_defined_forceD; [ apply bottom_is_least; reflexivity | eassumption ].
      + rewrite EftailD. reflexivity.
      + intros out cost [Hout Hcost].
        mgo_.
        {
          destruct outD as [ outA | ]; simpl in Hout.
          - constructor; exact Hout.
          - constructor.
        }
        {
          rewrite EftailD in Hcost. simpl in Hcost. lia.
        }
    Unshelve. 
    all: destruct PA; assumption.
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
            | FTail, [q], [outD] => _
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
    - (* FTail *)
      invert_clear 1 as [ | ? ? ? ? HoutD _ ].
      intros input cost HxD. unfold demand in HxD. simpl in HxD.
      destruct (ftailD q (forceD (bottom_of (exact (ftail q))) outD))
        as [cost' qD'] eqn:EftailD.
      simpl in HxD. invert_clear HxD.
      (* Goal: sumof potential [qD'] + cost' ≤ 3 + sumof potential [outD] *)
      destruct outD as [ outA | ]; simpl in *.
      + (* outD = Thunk outA: use ftailD'_cost *)
        invert_clear HoutD.
        rename H into HleA.  (* HleA : Thunk outA ≤ exact (ftail q) ⇒ outA ≤ exact (ftail q) after inversion *)
        eapply (ftailD'_cost) in HleA.
        unfold ftailD in EftailD.
        rewrite EftailD in HleA. simpl in HleA.
        unfold potential.
        change (match qD' with Thunk qA => debt qA | Undefined => 0 end) with (debt qD').
        lia.
      + (* outD = Undefined *)
        destruct q as [ | y | d m r ]; simpl in *.
        (* q = Nil *)
        {
          invert_clear EftailD. destruct output; cbn in *; lia.
        }
        (* q = Unit y *)
        {
          invert_clear EftailD. destruct output; cbn in *; lia.
        }
        (* q = More d m r *)
        {
          destruct d as [ a | a b | a b c ].
          - (* d = One a *)
            Show.
            destruct m as [ | t_m | fd_m m_spine r_d_m ];
            [ destruct r as [ ra | ra rb | ra rb rc ]
            | destruct t_m as [ pa pb | pa pb pc ]
            | destruct fd_m as [ tm_h | tm_h tm_h2 | tm_h tm_h2 tm_h3 ];
              destruct tm_h as [ pa pb | pa pb pc ] ];
            simpl in EftailD; invert_clear EftailD; cbn in *; lia.
          - (* d = Two a b *)
            simpl in EftailD; invert_clear EftailD; destruct args; cbn in *; lia.
          - (* d = Three a b c *)
            simpl in EftailD; invert_clear EftailD; destruct args; cbn in *; lia.
        }
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
