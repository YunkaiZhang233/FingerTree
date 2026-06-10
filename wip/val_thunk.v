(* wip/val_thunk.v — glueD' always returns Thunk outer spine demands.

   coqc -Q src Clairvoyance wip/val_thunk.v *)

From Coq Require Import List RelationClasses Lia.
From Clairvoyance Require Import Core Tick Approx ApproxM FingerCore FingerCons FingerSnoc FingerConcat.
Import ListNotations.
Set Implicit Arguments.

#[local] Existing Instance Reflexive_LessDefined_T.

Lemma glueD'_val_thunk {A : Type} (s1 : Seq A) :
  forall (B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
         (as_ : list A) (s2 : Seq A) (outD : SeqA B),
    List.length as_ <= 3 ->
    outD `is_approx` glue s1 as_ s2 ->
    exists q1 asD q2,
      Tick.val (glueD' s1 as_ s2 outD) = (Thunk q1, asD, Thunk q2).
Proof.
  destruct s1 as [ | x | u1 m1 v1 ]; intros B LDB Refl0 EAB as_ s2 outD Hlen Happrox.
  - (* Nil *)
    cbn [glueD']. cbv zeta.
    destruct (foldr_fconsD'_val_thunk as_ s2 outD) as [ q2 Hq2 ].
    unfold Tick.bind, Tick.ret, Tick.tick; cbn [Tick.val]. rewrite Hq2.
    do 3 eexists; reflexivity.
  - (* Unit x *)
    destruct s2 as [ | y | u2 m2 v2 ].
    + (* Nil *)
      cbn [glue] in Happrox.
      cbn [glueD']. cbv zeta.
      destruct (@foldl_fsnocD'_val_thunk A B _ _ _ as_ (Unit x) outD Happrox) as [ q1 Hq1 ].
      unfold Tick.bind, Tick.ret, Tick.tick; cbn [Tick.val]. rewrite Hq1.
      do 3 eexists; reflexivity.
    + (* Unit y *)
      cbn [glueD']. cbv zeta.
      destruct (foldr_fconsD'_val_thunk (x :: as_) (Unit y) outD) as [ q2 Hq2 ].
      unfold Tick.bind, Tick.ret, Tick.tick; cbn [Tick.val]. rewrite Hq2.
      destruct (foldr_fcons_elems (x :: as_) (Unit y) outD) as [ | xD asD' ];
        do 3 eexists; reflexivity.
    + (* More u2 m2 v2 *)
      cbn [glueD']. cbv zeta.
      destruct (foldr_fconsD'_val_thunk (x :: as_) (More u2 m2 v2) outD) as [ q2 Hq2 ].
      unfold Tick.bind, Tick.ret, Tick.tick; cbn [Tick.val]. rewrite Hq2.
      destruct (foldr_fcons_elems (x :: as_) (More u2 m2 v2) outD) as [ | xD asD' ];
        do 3 eexists; reflexivity.
  - (* More u1 m1 v1 *)
    destruct s2 as [ | y | u2 m2 v2 ].
    + (* Nil *)
      cbn [glue] in Happrox.
      cbn [glueD']. cbv zeta.
      destruct (@foldl_fsnocD'_val_thunk A B _ _ _ as_ (More u1 m1 v1) outD Happrox) as [ q1 Hq1 ].
      unfold Tick.bind, Tick.ret, Tick.tick; cbn [Tick.val]. rewrite Hq1.
      do 3 eexists; reflexivity.
    + (* Unit y *)
      cbn [glue] in Happrox.
      cbn [glueD']. cbv zeta.
      destruct (@foldl_fsnocD'_val_thunk A B _ _ _ (as_ ++ [y]) (More u1 m1 v1) outD Happrox) as [ q1 Hq1 ].
      unfold Tick.bind, Tick.ret, Tick.tick; cbn [Tick.val]. rewrite Hq1.
      do 3 eexists; reflexivity.
    + (* More u2 m2 v2 — deep arm: outD forced MoreA by approx *)
      cbn [glue] in Happrox.
      invert_clear Happrox as [ | | ? ? ? ? ? ? Hu1 Hm Hv2 ].
      cbn [glueD']. cbv zeta.
      unfold Tick.bind, Tick.ret, Tick.tick; cbn [Tick.val].
      destruct (Tick.val (glueD' m1 (toTuples (digitToList v1 ++ as_ ++ digitToList u2)) m2
                  match _ with Thunk q => q | Undefined => _ end)) as [ [m1D middleD] m2D ].
      destruct (unbundle middleD (length (digitToList v1)) (length as_) (length (digitToList u2)))
        as [ [ v1D asD0 ] u2D ].
      do 3 eexists; reflexivity.
Qed.
