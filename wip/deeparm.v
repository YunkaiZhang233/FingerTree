(* wip/deeparm.v — develop the deep More/More arm of glueD'_spec.
   coqc -Q src Clairvoyance wip/deeparm.v *)

From Coq Require Import List RelationClasses Lia.
From Clairvoyance Require Import Core Tick Approx ApproxM FingerCore FingerCons FingerSnoc FingerConcat.
Import ListNotations.
Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

#[local] Existing Instance Reflexive_LessDefined_T.

Lemma glueD'_spec_deep :
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
  - admit. (* Nil *)
  - admit. (* Unit *)
  - intros A0 f m r IHm B0 LDB0 Refl0 Trans0 EAB0 as_ s2 outD Hlen Happrox s1D asD s2D Htriple dcost.
    destruct s2 as [ | y | u2 m2 v2 ].
    + admit.
    + admit.
    + (* arm 6: deep More/More *)
      destruct outD as [ | | u1D m'D v2D ];
        [ cbn [glue] in Happrox; invert_clear Happrox
        | cbn [glue] in Happrox; invert_clear Happrox
        | ].
      cbn [glue] in Happrox.
      invert_clear Happrox as [ | | ? ? ? ? ? ? Hu1 Hm Hv2 ].
      cbn [glueD'] in Htriple, dcost; cbv zeta in Htriple, dcost.
      set (middle := toTuples (digitToList r ++ as_ ++ digitToList u2)) in *.
      set (m'D_forced := match m'D with
                         | Thunk q => q
                         | Undefined => bottom_of (exact (glue m middle m2))
                         end) in *.
      assert (Hm_forced : m'D_forced `is_approx` glue m middle m2).
      { unfold m'D_forced. destruct m'D as [ q | ] eqn:Eq.
        - invert_clear Hm. assumption.
        - apply bottom_is_least. reflexivity. }
      assert (Hmiddle_len : List.length middle <= 3).
      { unfold middle. apply toTuples_length_bound.
        rewrite !List.app_length. destruct r, u2; simpl; lia. }
      pose proof (@glueD'_approx (Tuple A0) m (TupleA B0) _ _ _ middle m2 m'D_forced
                    Hmiddle_len Hm_forced) as Happ_rec.
      destruct (Tick.val (glueD' m middle m2 m'D_forced)) as [ [m1D middleD] m2D ] eqn:Eval.
      destruct Happ_rec as [ Hm1D [ HmiddleD Hm2D ] ].
      (* roundtrip *)
      assert (HLlen : 2 <= List.length (digitToList r ++ as_ ++ digitToList u2) <= 9).
      { rewrite !List.app_length. destruct r, u2; cbn [digitToList List.length]; lia. }
      assert (Hn123 : List.length (digitToList r) + List.length as_ + List.length (digitToList u2)
                      = List.length (digitToList r ++ as_ ++ digitToList u2)).
      { rewrite !List.app_length. lia. }
      destruct (@unbundle_roundtrip A0 B0 _ _ _
                    (digitToList r ++ as_ ++ digitToList u2) middleD
                    (List.length (digitToList r)) (List.length as_) (List.length (digitToList u2))
                    ltac:(destruct r; cbn [digitToList List.length]; lia)
                    ltac:(destruct u2; cbn [digitToList List.length]; lia)
                    Hn123 HLlen HmiddleD)
        as [ v1' [ u2' [ asD' [ Hunb Hretup ] ] ] ].
      (* reduce Htriple to read off s1D, asD, s2D *)
      cbn [Tick.val Tick.bind Tick.tick] in Htriple.
      rewrite Eval in Htriple.
      rewrite Hunb in Htriple.
      cbn [Tick.val Tick.ret] in Htriple.
      invert_clear Htriple.
      (* dcost = 1 + cost of the recursive call *)
      assert (Hdcost : dcost = 1 + Tick.cost (glueD' m middle m2 m'D_forced)).
      { subst dcost. cbn [Tick.cost Tick.bind Tick.tick]. rewrite Eval, Hunb.
        cbn [Tick.cost Tick.ret]. lia. }
      clearbody dcost. rewrite Hdcost.
      (* IH on the recursive middle *)
      specialize (IHm (TupleA B0) _ _ _ _ middle m2 m'D_forced Hmiddle_len Hm_forced
                    m1D middleD m2D (eq_sym Eval)).
      cbv zeta in IHm.
      (* corelax the IH spec onto the re-bundled tuples the clairvoyant recomputes *)
      assert (HPO_B0 : PreOrder (less_defined (a := B0))) by (constructor; assumption).
      assert (Hcomp : glueA m1D (toTuplesA (digitToListA v1' ++ asD' ++ digitToListA u2')) m2D
                      [[ fun out cost => m'D_forced `less_defined` out
                                         /\ cost <= Tick.cost (glueD' m middle m2 m'D_forced) ]]).
      { eapply optimistic_corelax; [ | apply uc_cost | exact IHm ].
        apply glueA_mon; [ reflexivity | exact Hretup | reflexivity ]. }
      (* m'D is dominated by Thunk m'D_forced unconditionally *)
      assert (Hmdf : m'D `less_defined` Thunk m'D_forced).
      { unfold m'D_forced. destruct m'D as [ q | ]; [ reflexivity | apply LessDefined_Undefined ]. }
      (* drive the clairvoyant glueA' *)
      unfold glueA. unfold glueA in Hcomp.
      cbn [forcing glueA'].
      apply optimistic_bind. apply optimistic_tick.
      cbn [force]. apply optimistic_bind. apply optimistic_ret. cbn beta.
      apply optimistic_bind. apply optimistic_ret. cbn beta.
      apply optimistic_bind. apply optimistic_thunk_go.
      eapply optimistic_mon; [ exact Hcomp | ].
      intros cval n [ Hcval Hcost ].
      apply optimistic_ret.
      split.
      * constructor;
          [ reflexivity
          | etransitivity; [ exact Hmdf | constructor; exact Hcval ]
          | reflexivity ].
      * lia.
Admitted.
