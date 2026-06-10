(* wip/flat_retuple.v — step D of the deep More/More arm.

   coqc -Q src Clairvoyance wip/flat_retuple.v *)

From Coq Require Import List RelationClasses Lia.
From Clairvoyance Require Import Core Tick Approx ApproxM FingerCore FingerCons FingerSnoc FingerConcat.
Import ListNotations.
Set Implicit Arguments.

#[local] Existing Instance Reflexive_LessDefined_T.

(* Invert each per-tuple element-demand, distributing over the Undefined/Thunk
   split via ';' (a [repeat match] would only process the focused goal). *)
Ltac inv_elems :=
  match goal with
  | Hd : _ `less_defined` (exact (Pair _ _))    |- _ => invert_clear Hd; inv_elems
  | Hd : _ `less_defined` (exact (Triple _ _ _)) |- _ => invert_clear Hd; inv_elems
  | H  : _ `less_defined` (PairA _ _)            |- _ => invert_clear H; inv_elems
  | H  : _ `less_defined` (TripleA _ _ _)        |- _ => invert_clear H; inv_elems
  | _ => idtac
  end.

Ltac crunch_retuple :=
  cbn [toTuples tupleArities List.length List.map] in *;
  repeat match goal with
         | H : Forall2 _ _ (_ :: _) |- _ => inversion H; subst; clear H
         | H : Forall2 _ _ []       |- _ => inversion H; subst; clear H
         end;
  inv_elems;
  cbn [tupleArities List.combine List.map List.concat unbundleTuple
       toTuplesA List.repeat List.app];
  repeat first [ apply Forall2_nil
               | apply Forall2_cons; [ first [ reflexivity | apply LessDefined_Undefined ] | ] ].

(* Re-tupling the unbundle flattening of [middleD] dominates [middleD]. *)
Lemma flat_retuple {A B : Type} `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
  (L : list A) (middleD : list (T (TupleA B))) :
  length L <= 9 ->
  Forall2 less_defined middleD (List.map exact (toTuples L)) ->
  Forall2 less_defined middleD
    (toTuplesA (List.concat (List.map (fun '(k,t) => unbundleTuple k t)
                            (List.combine (tupleArities (List.length L)) middleD)))).
Proof.
  intros Hlen HmD.
  do 10 (destruct L as [| ? L]; [ crunch_retuple | ]).
  cbn [List.length] in Hlen; lia.
Qed.
