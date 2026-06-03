(** * FingerMonoid — the measure-monoid interface for annotated finger trees.

    Finger trees à la Hinze–Paterson (2006) are parameterised over a
    *monoid* of measures together with a *measure* on elements.  The same
    annotated structure and the same [splitTree] then recover different
    abstract types purely by changing the monoid:

      - the SIZE monoid        (nat, 0, +, ‖x‖ = 1)        → random access;
      - the INTERVAL monoid     (min/max of element keys)    → min-max queue;
      - the LAST-VALUE monoid   (rightmost key)              → ordered sequence.

    See X. Leroy, "Persistent data structures", lecture 5 (2023), and
    Hinze & Paterson, "Finger trees: a simple general-purpose data
    structure", JFP 16(2), 2006.

    This file is independent of the Clairvoyance library; it provides only
    the algebraic interface and its instances.  Place it before
    [FingerSplit.v] in the build (e.g. as [Clairvoyance.FingerMonoid]). *)

From Coq Require Import Arith Lia.

Set Implicit Arguments.

(* ================================================================= *)
(** ** The monoid interface                                            *)
(* ================================================================= *)

(** A monoid: a carrier [M] with a neutral element and an associative
    binary operation, together with the three laws.  We bundle the laws
    into the class so that any instance carries its proof obligations,
    exactly as Leroy's [module type MONOID] is refined to a structure
    proving the equational theory. *)

Class Monoid (M : Type) : Type := {
  mzero : M;
  madd  : M -> M -> M;
  madd_zero_l : forall x,     madd mzero x = x;
  madd_zero_r : forall x,     madd x mzero = x;
  madd_assoc  : forall x y z, madd (madd x y) z = madd x (madd y z);
}.

Declare Scope monoid_scope.
Infix "<+>" := madd (at level 50, left associativity) : monoid_scope.
Open Scope monoid_scope.

(* ================================================================= *)
(** ** A few derived facts (handy when proving split's contract)       *)
(* ================================================================= *)

Section MonoidFacts.
  Context {M : Type} `{Monoid M}.

  (** Reassociation used pervasively when re-bracketing scanned measures
      [i <+> ‖pr‖ <+> ‖m‖ <+> ‖sf‖]. *)
  Lemma madd_assoc4 (a b c d : M) :
    a <+> b <+> c <+> d = a <+> (b <+> (c <+> d)).
  Proof. now rewrite !madd_assoc. Qed.

  Lemma madd_shift (a b c : M) :
    a <+> b <+> c = a <+> (b <+> c).
  Proof. apply madd_assoc. Qed.

End MonoidFacts.

(* ================================================================= *)
(** ** Instance 1 — the size monoid (random access)                    *)
(* ================================================================= *)

(** [M = nat], [0], [+].  With the element measure [‖x‖ = 1] (threaded as
    [md := fun _ => 1] in [FingerSplit.v]), the scanned measure at a
    position is the index, and [splitTree (fun sz => i <? sz) 0] locates
    the [i]-th element. *)

#[refine] #[global] Instance Monoid_size : Monoid nat := {
  mzero := 0;
  madd  := Nat.add;
}.
Proof. all: intros; lia. Defined.

(* ================================================================= *)
(** ** Instances 2 and 3 — sketched (the payoff of going generic)      *)
(* ================================================================= *)

(** These are the other two applications Leroy lists; both reuse the
    *identical* [splitTree].  Spelled out here over a fixed key type
    [nat] to keep them concrete; generalising the key to an arbitrary
    [compare] is routine.  Left as definitions you can switch on once the
    cost result is in place. *)

(** *** Interval monoid → min-max priority queue.
    [M = option (nat * nat)] holding (min,max); [‖x‖ = Some (x,x)].
    [extract_min] splits on [fun o => match o with Some(m,_) => m =? lo
    | None => false end] where [lo] is the global minimum from
    [measureSeq]. *)
Definition Interval := option (nat * nat).

#[refine] #[global] Instance Monoid_interval : Monoid Interval := {
  mzero := None;
  madd  := fun a b =>
    match a, b with
    | None, _ => b
    | _, None => a
    | Some (l1,h1), Some (l2,h2) => Some (Nat.min l1 l2, Nat.max h1 h2)
    end;
}.
Proof.
  - now intros [[??]|].
  - now intros [[??]|].
  - intros [[??]|] [[??]|] [[??]|]; cbn; try reflexivity;
      f_equal; f_equal; lia.
Defined.

(** *** Last-value monoid → ordered sequence / binary search.
    [M = option nat]; [‖x‖ = Some x]; [a <+> b] keeps the rightmost.
    On a sequence kept sorted, [split (fun o => match o with Some v =>
    key <=? v | None => false end) None] performs the BST-style search. *)
#[refine] #[global] Instance Monoid_lastval : Monoid (option nat) := {
  mzero := None;
  madd  := fun a b => match b with None => a | Some _ => b end;
}.
Proof.
  - now intros [|].
  - now intros [|].
  - now intros [|] [|] [|].
Defined.

(* ================================================================= *)
(** ** End of FingerMonoid                                              *)
(* ================================================================= *)