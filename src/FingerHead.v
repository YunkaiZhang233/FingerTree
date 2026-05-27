(** * FingerHead — head operation, demand analysis, and spec *)

From Coq Require Import Arith Psatz Relations RelationClasses List.
From Clairvoyance Require Import Core Approx ApproxM Tick Prod Option.
From Hammer Require Import Tactics.
From Clairvoyance Require Import FingerCore FingerCons.

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

(**
==============
Head Operations

head (Unit x) = Some x
head (More (One x) _ _ ) = Some x
head (More (Two x _) _ _ ) = Some x
head (More (Three x _ _) _ _ ) = Some x
*)
Definition head {A : Type} (s : Seq A) : option A :=
  match s with
  | Nil => None
  | Unit x => Some x
  | More (One x) _ _ => Some x
  | More (Two x _) _ _ => Some x
  | More (Three x _ _) _ _ => Some x
  end.


(* Demand function *)
Definition headD' {A B : Type} `{Exact A B} (s : Seq A) (outD : option (T B))
    : Tick (T (SeqA B)) :=
  Tick.tick >>
  match s, outD with
  | Nil, None => Tick.ret (Thunk NilA)
  | Unit x, Some xD =>
      Tick.ret (Thunk (UnitA xD))
  | Unit x, None => Tick.ret (Thunk (UnitA Undefined))
  | More (One x) m r, Some xD =>
      Tick.ret (Thunk (MoreA (Thunk (OneA xD)) Undefined Undefined))
  | More (One x) m r, None =>
      Tick.ret (Thunk (MoreA (Thunk (OneA Undefined)) Undefined Undefined))
  | More (Two x _) m r, Some xD =>
      Tick.ret (Thunk (MoreA (Thunk (TwoA xD Undefined)) Undefined Undefined))
  | More (Two x _) m r, None =>
      Tick.ret (Thunk (MoreA (Thunk (TwoA Undefined Undefined)) Undefined Undefined))
  | More (Three x _ _) m r, Some xD =>
      Tick.ret (Thunk (MoreA (Thunk (ThreeA xD Undefined Undefined)) Undefined Undefined))
  | More (Three x _ _) m r, None =>
      Tick.ret (Thunk (MoreA (Thunk (ThreeA Undefined Undefined Undefined)) Undefined Undefined))
  | _, _ => bottom
  end.

(* Specialization *)
Definition headD (A : Type) : Seq A -> option (T A) -> Tick (T (SeqA A)) :=
  headD'.

(* Functional correctness *)
Lemma headD'_approx : forall (A B : Type)
    `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (s : Seq A) (outD : option (T B)),
    outD `is_approx` head s ->
    Tick.val (headD' s outD) `is_approx` s.
Proof.
  intros A B LDB RLDB EAB s outD Happrox.
  destruct s as [ | a | d s' d0 ]; destruct outD as [ xD | ]; simpl in *.
  - (* Nil, Some xD — bottom case, Happrox : Some xD ≤ None is impossible *)
    invert_clear Happrox.
  - (* Nil, None *) repeat constructor.
  - (* Unit a, Some xD *) repeat constructor. invert_clear Happrox. assumption.
  - (* Unit a, None *) repeat constructor.
  - (* More d s' d0, Some xD *)
    destruct d; repeat constructor; invert_clear Happrox; assumption.
  - (* More d s' d0, None *)
    destruct d; repeat constructor.
Qed.

Corollary headD_approx (A : Type) `{LDA : LessDefined A, !Reflexive LDA}
    (s : Seq A) (outD : option (T A)) :
    outD `is_approx` head s ->
    Tick.val (headD s outD) `is_approx` s.
Proof.
  eapply headD'_approx.
Qed.

(* Cost — one tick, no recursion. *)
Lemma headD'_cost : forall (A B : Type) `{Exact A B}
    (s : Seq A) (outD : option (T B)),
    Tick.cost (headD' s outD) <= 1.
Proof.
  intros. destruct s; destruct outD; simpl; try lia.
  all: destruct d; simpl; lia.
Qed.

Corollary headD_cost (A : Type) `{Exact A}
    (s : Seq A) (outD : option (T A)) :
    Tick.cost (headD s outD) <= 1.
Proof.
  eapply headD'_cost.
Qed.

Definition headA' (A : Type) (q : SeqA A) : M (option (T A)) :=
  tick >>
    match q with
    | NilA => ret None
    | UnitA x => ret (Some x)
    | MoreA fD _ _ =>
        forcing fD (fun f =>
          match f with
          | OneA x => ret (Some x)
          | TwoA x _ => ret (Some x)
          | ThreeA x _ _ => ret (Some x)
          end)
    end.
 
Definition headA (A : Type) (q : T (SeqA A)) : M (option (T A)) :=
  forcing q headA'.

Lemma headA_mon (A : Type) `{LDA : LessDefined A, PreOrder A LDA}
    (q1 q2 : T (SeqA A)) :
    q1 `less_defined` q2 ->
    headA q1 `less_defined` headA q2.
Proof.
  invert_clear 1; try solve [ solve_mon ].
  (* Both Thunk: q1 = Thunk x1, q2 = Thunk y1, x1 ≤ y1 *)
  rename x into x1. rename y into y1. rename H0 into Hxy.
  simpl. unfold headA'. apply bind_mon; [ reflexivity | ].
  intros x x' Hxx'.
  (* match x1 ≤ match y1, given Hxy : x1 ≤ y1 *)
  invert_clear Hxy; try solve [ solve_mon ].
Qed.

Lemma headD'_spec : forall (A B : Type)
    `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (s : Seq A) (outD : option (T B)),
    outD `is_approx` head s ->
    forall sD, sD = Tick.val (headD' s outD) ->
      let dcost := Tick.cost (headD' s outD) in
      headA sD [[ fun out cost =>
                     outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros A B LDB RLDB EAB s outD Happrox sD HsD dcost.
  destruct s as [ | a | d s' d0 ].
  3: destruct d.
  all: destruct outD;
       simpl in *;
       try (invert_clear Happrox; fail).
  - (* Nil, None *)              subst. unfold headA, headA'. mgo_.
  - (* Unit a, Some t *)         subst. unfold headA, headA'. mgo_.
  - (* More (One _), Some t *)   subst. unfold headA, headA'. simpl. mgo_.
  - (* More (Two _ _), Some t *) subst. unfold headA, headA'. simpl. mgo_.
  - (* More (Three _ _ _), Some t *) subst. unfold headA, headA'. simpl. mgo_.
Qed.

Corollary headD_spec : forall (A : Type) `{LDA : LessDefined A, !Reflexive LDA}
    (s : Seq A) (outD : option (T A)),
    outD `is_approx` head s ->
    forall sD, sD = Tick.val (headD s outD) ->
      let dcost := Tick.cost (headD s outD) in
      headA sD [[ fun out cost =>
                     outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros.
  apply headD'_spec; auto.
Qed.

