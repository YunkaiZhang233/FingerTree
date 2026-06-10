(* wip/step_lemma.v — fconsA_elemD_step.

   Cases 1-4 are PROVEN and already integrated into src/FingerConcat.v (just
   before glueD'_spec), together with the proven foldr_fcons_clairvoyant_spec
   and the closed glueD'_spec Nil arm.  This scratch keeps the full lemma so
   that CASE 5 (the recursive More (Three ...) case) can be developed here in
   isolation, then ported into the file.

   Compile:  ~/.opam/thesis/bin/coqc -Q src Clairvoyance wip/step_lemma.v
   Case-5 roadmap: see the case-5 comment below and docs/CONCAT_SPEC_PLAN.md. *)

From Coq Require Import List RelationClasses Lia.
From Clairvoyance Require Import Core Tick Approx FingerCore FingerCons FingerSnoc FingerConcat.
Import ListNotations.
Set Implicit Arguments.
#[local] Existing Instance Reflexive_LessDefined_T.
Ltac kill_digit H :=
  try (invert_clear H;
       match goal with
       | Hd : (OneA _) `less_defined` _ |- _ => invert_clear Hd
       | Hd : (TwoA _ _) `less_defined` _ |- _ => invert_clear Hd
       | Hd : (ThreeA _ _ _) `less_defined` _ |- _ => invert_clear Hd
       end; fail).
Ltac force_all := mgo_; repeat (apply optimistic_thunk_go; mgo_).

Lemma fconsA_elemD_step (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (x : A) (s : Seq A) (outD : SeqA B) (e : T B) (q : SeqA B) :
  outD `is_approx` fcons x s ->
  fcons_elemD s outD `less_defined` e ->
  (match Tick.val (fconsD' x s outD) with
   | Thunk d => d | Undefined => bottom_of (exact s) end) `less_defined` q ->
  fconsA' q e
  [[ fun out cost => outD `less_defined` out /\ cost <= Tick.cost (fconsD' x s outD) ]].
Proof.
  revert e q. revert A x s B LDB Reflexive0 H outD.
  apply (fcons_ind (fun A x s s' =>
    forall B `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
           (outD : SeqA B) (e : T B) (q : SeqA B),
      outD `less_defined` exact s' ->
      fcons_elemD s outD `less_defined` e ->
      (match Tick.val (fconsD' x s outD) with
       | Thunk d => d | Undefined => bottom_of (exact s) end) `less_defined` q ->
      fconsA' q e
      [[ fun out cost => outD `less_defined` out /\ cost <= Tick.cost (fconsD' x s outD) ]])).
  - (* Case 1: s = Nil *)
    intros A0 x0 B0 LDB0 HRefl0 EAB0 outD e q Happrox Helem Hq.
    destruct outD as [ | xD | fD mD rD ]; try (invert_clear Happrox; fail).
    cbn [fcons_elemD] in Helem. simpl in Hq. invert_clear Hq.
    cbn [fconsA']. force_all.
  - (* Case 2: s = Unit y *)
    intros A0 x0 y0 B0 LDB0 HRefl0 EAB0 outD e q Happrox Helem Hq.
    destruct outD as [ | xD | fD mD rD ]; try (invert_clear Happrox; fail).
    invert_clear Happrox as [ | | ? ? ? ? ? ? Hf Hm Hr ].
    destruct fD as [ [ f1 | f1 f2 | f1 f2 f3 ] | ]; kill_digit Hf;
    destruct rD as [ [ ra | ra rb | ra rb rc ] | ]; kill_digit Hr;
      cbn [fcons_elemD] in Helem; simpl in Hq; invert_clear Hq;
      cbn [fconsA']; force_all.
  - (* Case 3: s = More (One a) m r *)
    intros A0 x0 a0 m0 r0 B0 LDB0 HRefl0 EAB0 outD e q Happrox Helem Hq.
    destruct outD as [ | xD | fD mD rD ]; try (invert_clear Happrox; fail).
    invert_clear Happrox as [ | | ? ? ? ? ? ? Hf Hm Hr ].
    destruct fD as [ [ f1 | f1 f2 | f1 f2 f3 ] | ]; kill_digit Hf;
      cbn [fcons_elemD] in Helem; simpl in Hq;
      invert_clear Hq as [ | | ? ? ? ? ? ? Hqf Hqm Hqr ];
      invert_clear Hqf as [ | ? ? Hz ]; invert_clear Hz as [ ? ? Hf2q | | ];
      cbn [fconsA']; force_all.
  - (* Case 4: s = More (Two a b) m r *)
    intros A0 x0 a0 b0 m0 r0 B0 LDB0 HRefl0 EAB0 outD e q Happrox Helem Hq.
    destruct outD as [ | xD | fD mD rD ]; try (invert_clear Happrox; fail).
    invert_clear Happrox as [ | | ? ? ? ? ? ? Hf Hm Hr ].
    destruct fD as [ [ f1 | f1 f2 | f1 f2 f3 ] | ]; kill_digit Hf;
      cbn [fcons_elemD] in Helem; simpl in Hq;
      invert_clear Hq as [ | | ? ? ? ? ? ? Hqf Hqm Hqr ];
      invert_clear Hqf as [ | ? ? Hz ]; invert_clear Hz as [ | ? ? ? ? Haq Hbq | ];
      cbn [fconsA']; force_all.
  - (* Case 5: s = More (Three a b c) m r -- RECURSIVE.  ROADMAP (next session):
       intros A0 x0 a0 b0 c0 m0 r0 IH B0 ... outD e q Happrox Helem Hq.
       destruct outD; invert Happrox -> Hf Hm Hr; destruct fD (kill_digit Hf);
       invert Hq -> Hqf Hqm Hqr; invert Hqf -> qf = Thunk (ThreeA qa qb qc),
       Haq:f2<=qa, Hbq:exact b0<=qb, Hcq:exact c0<=qc; destruct mD as [dc|];
       cbn [thunkD] in Hqm; (invert Hm -> Hmc: dc <= exact (fcons (Pair b0 c0) m0));
       cbn [fconsA']; mgo_; apply optimistic_thunk_go (x3, force f'/pbc/m').
       At the recursion `(fun m => fconsA' m (Thunk (PairA qb qc))) $! m2`:
         apply optimistic_thunk_go;   (* force m2 = qm *)
         eapply optimistic_mon; [ eapply IH | intros out n [Hout Hcost]; mgo_ ].
       IH side-conditions:
         (1) dc <= exact (fcons (Pair b0 c0) m0)            -- Hmc
         (2) fcons_elemD m0 dc <= Thunk (PairA qb qc)       -- trans (fcons_elemD_approx)
                                                               (exact (Pair b0 c0) <= PairA qb qc via Hbq,Hcq)
         (3) forced (fconsD' (Pair b0 c0) m0 dc) <= forced m2  -- from Hqm by forced-monotonicity
       The mD = Undefined sub-case: thunkD on Undefined; the output middle is
       Undefined so the recursion's optimistic_skip suffices.  *)
    admit.
Admitted.
