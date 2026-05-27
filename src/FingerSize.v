(** * FingerSize — Structural metrics for finger trees.

    Contains:
    - [Seq_ind_poly]: polymorphic induction principle for [Seq].
    - [depth]: structural depth of a sequence's spine.
    - [digit_size], [size]: leaf-count metrics.
    - [size_lower_bound]: [2^(depth s) <= size s] for nonempty [s].
    - [depth_log_size]: [depth s <= log2 (size s)] for nonempty [s].

    This file is a leaf dependency for complexity proofs.  It depends
    only on [FingerCore.v] (for [Seq], [Digit], [Tuple]) and on Coq's
    standard library for [Nat.log2] and related arithmetic.

    Future work: a tighter analysis using [log_3] is possible (since
    [Tuple]s can hold 3 elements), but [log_2] is sufficient for the
    [O(log n)] asymptotic. *)

From Coq Require Import Arith Lia.
From Clairvoyance Require Import FingerCore.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.


(* ================================================================= *)
(** ** Polymorphic induction principle for [Seq]                       *)
(* ================================================================= *)

(** [Seq] has non-uniform recursion ([More] embeds [Seq (Tuple A)]),
    so Coq's auto-generated [Seq_ind] is not powerful enough.  This
    custom principle threads a polymorphic motive through the inductive
    structure. *)
Lemma Seq_ind_poly (P : forall A, Seq A -> Prop) :
  (forall A, P A Nil) ->
  (forall A x, P A (Unit x)) ->
  (forall A f m r, P (Tuple A) m -> P A (More f m r)) ->
  forall A (s : Seq A), P A s.
Proof.
  intros HNil HUnit HMore.
  fix SELF 2.
  destruct s.
  - apply HNil.
  - apply HUnit.
  - apply HMore. apply SELF.
Qed.


(* ================================================================= *)
(** ** Depth                                                           *)
(* ================================================================= *)

(** *** [depth]: structural depth of a sequence's spine. *)
Fixpoint depth {A : Type} (s : Seq A) : nat :=
  match s with
  | Nil        => 0
  | Unit _     => 0
  | More _ m _ => S (depth m)
  end.


(* ================================================================= *)
(** ** Size                                                            *)
(* ================================================================= *)

(** *** [digit_size]: number of elements in a Digit (1, 2, or 3). *)
Definition digit_size {A : Type} (d : Digit A) : nat :=
  match d with
  | One _       => 1
  | Two _ _     => 2
  | Three _ _ _ => 3
  end.

(** *** [size]: number of leaves in a finger tree, counted in the
    current element type.

    At depth [k], each leaf of [m : Seq (Tuple^k A)] represents at
    least 2 elements of the underlying type (since a [Tuple] is a
    [Pair] of 2 or a [Triple] of 3).  We use the conservative count
    of 2 (lower bound), which is enough for the [2^depth <= size]
    inequality.

    A tighter analysis using ratio 3 (max) yields the same [O(log n)]
    asymptotic. *)
Fixpoint size {A : Type} (s : Seq A) : nat :=
  match s with
  | Nil        => 0
  | Unit _     => 1
  | More u m v => digit_size u + 2 * size m + digit_size v
  end.


(** *** Helper: decide if a sequence is Nil. *)
Lemma Seq_nil_dec {A : Type} (s : Seq A) : s = Nil \/ s <> Nil.
Proof.
  destruct s; [left; reflexivity | right; discriminate | right; discriminate].
Qed.


(* ================================================================= *)
(** ** Size-depth relationship                                         *)
(* ================================================================= *)

(** *** Lower bound: size grows at least exponentially in depth.

    For any nonempty [s], we have [2^(depth s) <= size s].

    Proof by polymorphic induction on [s]:
    - [Nil]: contradicts nonemptiness.
    - [Unit _]: depth 0, size 1.  2^0 = 1 <= 1. ✓
    - [More u m v]: depth = S(depth m), size = digit u + 2*size m + digit v.
      Case on whether [m] is [Nil]:
      + [m = Nil]: size m = 0, so size >= 1 + 0 + 1 = 2 = 2^1 = 2^(depth (More _ Nil _)). ✓
      + [m <> Nil]: by IH, size m >= 2^(depth m).
        So size >= 1 + 2 * 2^(depth m) + 1 >= 2 * 2^(depth m) = 2^(S (depth m)). ✓ *)
Lemma size_lower_bound (A : Type) (s : Seq A) :
  s <> Nil -> 2 ^ depth s <= size s.
Proof.
  revert s. apply (Seq_ind_poly
    (fun A s => s <> Nil -> 2 ^ depth s <= size s)).
  - (* Nil case: contradicts hypothesis *)
    intros A0 Hne. contradiction.
  - (* Unit x case *)
    intros A0 x _.
    simpl. lia.
  - (* More f m r case *)
    intros A0 f m r IH _.
    simpl depth. simpl size.
    destruct (@Seq_nil_dec (Tuple A0) m) as [Hm_nil | Hm_nonnil].
    + (* m = Nil: size m = 0, depth m = 0 *)
      subst m. simpl size.
      destruct f as [a | a b | a b c];
        destruct r as [d | d e | d e g];
        simpl digit_size; simpl Nat.pow; lia.
    + (* m <> Nil: use IH *)
      specialize (IH Hm_nonnil).
      destruct f as [a | a b | a b c];
        destruct r as [d | d e | d e g];
        simpl digit_size; simpl Nat.pow; nia.
Qed.


(** *** Auxiliary: positive size for nonempty sequences. *)
Lemma size_pos (A : Type) (s : Seq A) :
  s <> Nil -> 0 < size s.
Proof.
  intro Hne.
  destruct s as [| x | u m v]; [contradiction | simpl; lia | ].
  simpl. destruct u; simpl; lia.
Qed.


(** *** Corollary: depth is bounded by log2 of size.

    For any nonempty [s], [depth s <= log2 (size s)]. *)
Corollary depth_log_size (A : Type) (s : Seq A) :
  s <> Nil -> depth s <= Nat.log2 (size s).
Proof.
  intro Hne.
  pose proof (size_lower_bound Hne) as Hsize.
  pose proof (size_pos Hne) as Hpos.
  (* We have: 2^(depth s) <= size s, want: depth s <= log2 (size s).
     Use Nat.log2_spec: for 0 < n, 2^(log2 n) <= n < 2^(S (log2 n)).
     By contradiction: if depth s > log2 (size s), then
     2^(depth s) >= 2^(S (log2 (size s))) > size s, contradiction. *)
  pose proof (Nat.log2_spec _ Hpos) as [Hlow Hhigh].
  destruct (Nat.le_gt_cases (depth s) (Nat.log2 (size s))) as [Hle | Hgt]; [auto | exfalso].
  apply (Nat.lt_irrefl (size s)).
  eapply Nat.lt_le_trans; [exact Hhigh | ].
  eapply Nat.le_trans; [ | exact Hsize].
  apply Nat.pow_le_mono_r; lia.
Qed.


(* ================================================================= *)
(** ** End of FingerSize                                                *)
(* ================================================================= *)


(** *** Notes for [FingerConcat] integration

    After importing [FingerSize.v], the corollary [concatD_cost_logsize]
    can be stated:

    [[
    Corollary concatD_cost_logsize (A : Type) `{LessDefined A}
        (q1 q2 : Seq A) (outD : SeqA A) :
      q1 <> Nil -> q2 <> Nil ->
      outD `is_approx` concat q1 q2 ->
      Tick.cost (concatD q1 q2 outD) <=
        glue_cost_const_1 * (Nat.log2 (size q1) + Nat.log2 (size q2))
        + glue_cost_const_2.
    Proof.
      intros Hq1 Hq2 Happrox.
      pose proof (concatD_cost _ _ _ Happrox) as Hcost.
      pose proof (depth_log_size q1 Hq1) as Hlog1.
      pose proof (depth_log_size q2 Hq2) as Hlog2.
      nia.
    Qed.
    ]]

    Note that [depth] is currently defined in [FingerConcat.v]; if you
    want to use [FingerSize]'s [depth], either remove the duplicate
    from [FingerConcat] or rename one of them to avoid collision.
    Recommendation: keep [depth] only in [FingerSize.v]. *)