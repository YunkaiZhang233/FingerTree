(* wip/roundtrip.v — the spec-side unbundle round-trip (dual of unbundle_flat_approx).

   coqc -Q src Clairvoyance wip/roundtrip.v *)

From Coq Require Import List RelationClasses Lia.
From Clairvoyance Require Import Core Tick Approx ApproxM FingerCore FingerCons FingerSnoc FingerConcat.
Import ListNotations.
Set Implicit Arguments.

#[local] Existing Instance Reflexive_LessDefined_T.

(* ---- flat_retuple (already validated in flat_retuple.v) ---- *)
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

(* ---- listToDigitA / digitToListA round trip on lengths 1..3 ---- *)
Lemma listToDigitA_thunk {B : Type} (l : list (T B)) :
  1 <= length l <= 3 ->
  exists d, listToDigitA l = Thunk d /\ digitToListA d = l.
Proof.
  intro Hlen.
  destruct l as [| a l]; [ cbn [List.length] in Hlen; lia | ].
  destruct l as [| b l]; [ exists (OneA a); split; reflexivity | ].
  destruct l as [| c l]; [ exists (TwoA a b); split; reflexivity | ].
  destruct l as [| dd l]; [ exists (ThreeA a b c); split; reflexivity | ].
  cbn [List.length] in Hlen; lia.
Qed.

(* ---- the round-trip ---- *)
Lemma unbundle_roundtrip {A B : Type} `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (L : list A) (middleD : list (T (TupleA B)))
    (n_v1 n_as n_u2 : nat) :
  1 <= n_v1 <= 3 ->
  1 <= n_u2 <= 3 ->
  n_v1 + n_as + n_u2 = List.length L ->
  2 <= List.length L <= 9 ->
  Forall2 less_defined middleD (List.map exact (toTuples L)) ->
  exists v1 u2 asD,
    unbundle middleD n_v1 n_as n_u2 = (Thunk v1, asD, Thunk u2) /\
    Forall2 less_defined middleD
            (toTuplesA (digitToListA v1 ++ asD ++ digitToListA u2)).
Proof.
  intros Hv1 Hu2 Hn Hlen HmD.
  unfold unbundle; cbv zeta.
  rewrite Hn.
  set (flat := List.concat (List.map (fun '(k, t) => unbundleTuple k t)
                 (List.combine (tupleArities (List.length L)) middleD))) in *.
  assert (Hfa : Forall2 less_defined flat (List.map exact L)).
  { unfold flat. apply unbundle_flat_approx; [ lia | exact HmD ]. }
  assert (Hflatlen : List.length flat = List.length L).
  { apply Forall2_length in Hfa. rewrite List.map_length in Hfa. exact Hfa. }
  destruct (listToDigitA_thunk (firstn n_v1 flat)) as [ v1 [ Hv1eq Hv1dl ] ].
  { rewrite firstn_length, Hflatlen. lia. }
  destruct (listToDigitA_thunk (skipn (n_v1 + n_as) flat)) as [ u2 [ Hu2eq Hu2dl ] ].
  { rewrite skipn_length, Hflatlen. lia. }
  exists v1, u2, (firstn n_as (skipn n_v1 flat)).
  rewrite Hv1eq, Hu2eq.
  split; [ reflexivity | ].
  rewrite Hv1dl, Hu2dl.
  assert (Hreass : firstn n_v1 flat ++ firstn n_as (skipn n_v1 flat)
                   ++ skipn (n_v1 + n_as) flat = flat).
  { replace (n_v1 + n_as) with (n_as + n_v1) by lia.
    rewrite <- skipn_skipn.
    rewrite firstn_skipn.
    rewrite firstn_skipn.
    reflexivity. }
  rewrite Hreass.
  unfold flat. apply flat_retuple; [ lia | exact HmD ].
Qed.
