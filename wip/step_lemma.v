(* wip/step_lemma.v — the kernel of glueD'_spec, in progress.

   Compile (needs src/*.vo built):
     ~/.opam/thesis/bin/coqc -Q src Clairvoyance wip/step_lemma.v

   This file is NOT in _CoqProject; `make` ignores it.  When [fconsA_elemD_step]
   is fully [Qed], paste it into src/FingerConcat.v just before [glueD'_spec],
   then `make` so the .vo refreshes.

   STATEMENT.  The *extracted* element demand [fcons_elemD s outD] together with
   any spine [q] that is at least the spine demand [Tick.val (fconsD' x s outD)]
   reconstructs [outD] within the demand cost.  This is the single-fcons-step
   analogue of [fconsD'_spec] (FingerCons.v), but with the extracted element
   demand instead of [exact x], and with [q] allowed to over-approximate the
   spine demand (the fold feeds it a [q] produced by the inner fold, which is
   only known to be >= the demand).

   STATUS: case 1 (s = Nil) proven; cases 2–5 admitted.  Model each on the
   matching case of [fconsD'_spec] in FingerCons.v (lines ~439–573). *)

From Coq Require Import List RelationClasses Lia.
From Clairvoyance Require Import Core Tick Approx FingerCore FingerCons FingerSnoc FingerConcat.
Import ListNotations.
Set Implicit Arguments.

Lemma fconsA_elemD_step (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (x : A) (s : Seq A) (outD : SeqA B) (q : SeqA B) :
  outD `is_approx` fcons x s ->
  (match Tick.val (fconsD' x s outD) with
   | Thunk d => d | Undefined => bottom_of (exact s) end) `less_defined` q ->
  fconsA' q (fcons_elemD s outD)
  [[ fun out cost => outD `less_defined` out /\ cost <= Tick.cost (fconsD' x s outD) ]].
Proof.
  revert q. revert A x s B LDB Reflexive0 H outD.
  apply (fcons_ind (fun A x s s' =>
    forall B `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
           (outD : SeqA B) (q : SeqA B),
      outD `less_defined` exact s' ->
      (match Tick.val (fconsD' x s outD) with
       | Thunk d => d | Undefined => bottom_of (exact s) end) `less_defined` q ->
      fconsA' q (fcons_elemD s outD)
      [[ fun out cost => outD `less_defined` out /\ cost <= Tick.cost (fconsD' x s outD) ]])).

  (* ---- Case 1: s = Nil, s' = Unit x.  PROVEN. ----
     fconsD' x Nil outD forces NilA (so q = NilA by Hq), fcons_elemD Nil
     (UnitA xD) = xD, and fconsA' NilA xD = tick >> ret (UnitA xD) = outD. *)
  { 
   intros A0 x0 B0 LDB0 HRefl0 EAB0 outD q Happrox Hq.
    destruct outD as [ | xD | fD mD rD ]; try (invert_clear Happrox; fail).
    cbn [fcons_elemD].
    simpl in Hq.
    invert_clear Hq.
    cbn [fconsA']. mgo_. 
   }

  (* ---- Case 2: s = Unit y, s' = More (One x) Nil (One y). ----
     fconsD' forces UnitA yD (yD read off rD); Hq forces q = UnitA y' with
     yD <= y'.  fconsA' (UnitA y') xD forces the three let~ into
     MoreA (OneA xD) NilA (OneA y').  Need outD = MoreA fD mD rD <= that:
       fD <= Thunk (OneA xD)  (xD = fcons_elemD extracts from fD),
       mD <= Thunk NilA       (from Happrox),
       rD <= Thunk (OneA y')  (yD<=y', rD relates to yD).
     Template: fconsD'_spec case 2 (the optimistic_thunk_go / invert_clear
     Happrox as [|| ... Ht Ht0 Ht1] block). *)
   {
      admit. 
   }

  (* ---- Case 3: s = More (One a) m r, s' = More (Two x a) m r. ----
     fconsD' returns Thunk (MoreA (Thunk (OneA aD)) mD rD); fcons_elemD reads xD
     from the TwoA front of outD.  fconsA' q xD forces front to TwoA xD a'.
     Template: fconsD'_spec case 3 (keep_mgo_, destruct front digit). *)
   { 
      admit. 
   }

  (* ---- Case 4: s = More (Two a b) m r, s' = More (Three x a b) m r. ----
     Symmetric to case 3 with ThreeA front.  Template: fconsD'_spec case 4. *)
   { 
      admit. 
   }

  (* ---- Case 5: s = More (Three a b c) m r — RECURSIVE. ----
     fcons x (More (Three a b c) m r) = More (Two x a) (fcons (Pair b c) m) r.
     Uses the IH at Tuple level on the middle spine.  Template: fconsD'_spec
     case 5 (the optimistic_thunk_go cascade + eapply IH + optimistic_mon).
     The IH here is the [fcons_ind] hypothesis, not glueD'_spec's IHm. *)
   { 
      admit. 
   }
Admitted.
