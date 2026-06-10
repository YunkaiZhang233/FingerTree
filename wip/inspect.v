(* wip/inspect.v — goal-inspection harness for glueD'_spec arms.

   Compile (needs src/*.vo built):
     ~/.opam/thesis/bin/coqc -Q src Clairvoyance wip/inspect.v

   It prints the goal for each arm to stdout, then [Abort]s (so coqc exits 0
   and nothing is added to the build).  This is how you see the *exact* goal
   shape an arm presents before writing tactics — do this instead of guessing.

   To inspect a different arm: copy the [Goal] block, set s1/s2 to the arm's
   shape, run the same preamble as glueD'_spec, and [idtac] the goal at the
   point you care about.  The reusable incantation is:
       match goal with |- ?g => idtac g end. *)

From Coq Require Import List RelationClasses Lia.
From Clairvoyance Require Import Core Tick Approx FingerCore FingerCons FingerSnoc FingerConcat.
Import ListNotations.
Set Implicit Arguments.

(* ===== Nil arm: the goal after the standard preamble + mgo_. ===== *)
Goal forall (A0 B0 : Type) (LDB0 : LessDefined B0) (Refl0 : Reflexive LDB0)
            (Trans0 : Transitive LDB0) (EAB0 : Exact A0 B0)
            (as_ : list A0) (s2 : Seq A0) (outD : SeqA B0),
  length as_ <= 3 ->
  outD `is_approx` glue Nil as_ s2 ->
  forall s1D asD s2D,
    (s1D, asD, s2D) = Tick.val (glueD' Nil as_ s2 outD) ->
    let dcost := Tick.cost (glueD' Nil as_ s2 outD) in
    glueA s1D asD s2D [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros A0 B0 LDB0 Refl0 Trans0 EAB0 as_ s2 outD Hlen Happrox s1D asD s2D Htriple dcost.
  cbn [glueD'] in Htriple, dcost.
  cbn [Tick.val Tick.bind Tick.ret] in Htriple.
  invert_clear Htriple.
  unfold glueA.
  destruct (Tick.val (foldr_fconsD' as_ s2 outD)) as [ q2 | ] eqn:Es2D; [ | admit ].
  simpl. mgo_. subst dcost. cbn [glue] in Happrox.
  idtac "===== NIL ARM GOAL (after preamble + mgo_) =====".
  match goal with |- ?g => idtac g end.
  simpl.
Abort.
