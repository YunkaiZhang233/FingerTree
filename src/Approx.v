(** * Approximations *)

(** Concepts for reasoning about approximations.

  "Approximations" are the values used in clairvoyant programs (functions
  with explicit cost semantics in the clairvoyance monad). "Pure values" are those
  used in non-monadic functions.

  - [less_defined]: an order relation between approximations (technically, just a preorder).
  - [lub]: least upper bound function on approximations.
  - [exact]: an embedding of pure values into approximations.
  - [is_approx]: a relation between approximations and pure values.

  Remarks:
  - [x `is_approx` y] is equivalent to [x `less_defined` exact y],
    and is now defined as such.
  - However, [exact] is not always definable, while [is_approx] might still
    have a reasonable definition. For instance, this is the case for functions.
    That's why our paper introduces [is_approx] as a separate concept.
    We haven't run into a use case of [is_approx] for functions or infinite data
    types so far though, so we reverted to defining [is_approx] as a notation using
    [less_defined] and [exact] for simplicity.
 *)

(** This part is a reference implementation of the definitions discussed in
    Section 5.3. *)

(** In the paper, we start by giving an [exact] function defined on lists. We
  mention later in the section that we would also want to be able to overload
  the [exact] function (and the [is_approx] and [less_defined] relations) for
  other types. One way of doing that is using type classes, as we show here. *)

From Coq Require Import Arith List Lia Morphisms Relations SetoidClass Setoid.
From Clairvoyance Require Import Core Relations.
From Clairvoyance Require Setoid.

Import ListNotations.

(* Type classes declared under this flag will have less confusing resolution.
  We will exclude [Exact] because in [Exact a b],
  [b] is supposed to be determined by [a], so it's fine to leave it as a flexible metavariable. *)

Definition is_defined {a} (t : T a) : Prop :=
  match t with
  | Thunk _ => True
  | Undefined => False
  end.

(** * [less_defined]: approximation ordering *)

(** [x `less_defined` y] *)

Class LessDefined a := less_defined : a -> a -> Prop.
Infix "`less_defined`" := less_defined (at level 42).

#[global] Hint Mode LessDefined ! : typeclass_instances.

(** [less_defined] should be a preorder (reflexive and transitive).
  (The paper says "order", which is imprecise. That was an oversight.)

  Every instance [LessDefined t] should be accompanied by an instance:
  [[
  #[global] Instance PreOrder_t : PreOrder (less_defined (a := t)).
  ]] *)

(** As a preorder, we expect to be able to do rewriting (in monotonic contexts).
  This instance registers [less_defined] as a relation for rewriting.
  Having [PreOrder] instances lying around is technically sufficient,
  but this helps automation in some cases. *)
#[global] Instance RewriteRelation_less_defined {a} `{LessDefined a}
  : RewriteRelation (less_defined (a := a)) := {}.

(** ** [less_defined] instance for [T]. *)

Inductive LessDefined_T {a : Type} `{LessDefined a} : LessDefined (T a) :=
| LessDefined_Undefined x : Undefined `less_defined` x
| LessDefined_Thunk x y :
    x `less_defined` y -> Thunk x `less_defined` Thunk y.

#[global] Hint Constructors LessDefined_T : core.
#[global] Existing Instance LessDefined_T.

(** An inversion lemma *)
Lemma less_defined_Thunk_inv {a} `{LessDefined a}
  : forall x y : a, Thunk x `less_defined` Thunk y -> x `less_defined` y.
Proof. inversion 1; auto. Qed.

#[local]
Instance Reflexive_LessDefined_T {a} `{LessDefined a} `{!Reflexive (less_defined (a := a))}
  : Reflexive (less_defined (a := T a)).
Proof. intros []; constructor; auto. Qed.

#[local]
Instance Transitive_LessDefined_T {a} `{LessDefined a} `{!Transitive (less_defined (a := a))}
  : Transitive (less_defined (a := T a)).
Proof.
  intros ? ? ? []; [ constructor | inversion 1; subst; constructor; etransitivity; eassumption ].
Qed.

(** [PreOrder] instance for [less_defined] at [T]. *)
#[global]
Instance PreOrder_LessDefined_T {a : Type} `{LessDefined a} `{Ho : !PreOrder (less_defined (a := a))}
  : PreOrder (less_defined (a := T a)).
Proof.
  constructor; exact _.
Qed.

(* Not sure we will ever need this, but it doesn't hurt to leave it here. *)
#[global]
Instance PartialOrder_LessDefined_T {a : Type} `{LessDefined a}
    `{Ho : PartialOrder _ eq (less_defined (a := a))}
  : PartialOrder eq (less_defined (a := T a)).
Proof.
constructor.
- intros ->. autounfold. constructor; reflexivity.
- inversion 1. induction H1.
  + inversion H2; reflexivity.
  + inversion H2; subst. f_equal. apply Ho. constructor; assumption.
Qed.

(** * [exact]: embedding pure values as approximations *)
Class Exact a b : Type := exact : a -> b.

(** This corresponds to the [exact_max] in Section 5.3: [exact] embeddings should be
  maximal elements. *)
Class ExactMaximal a b {Hless : LessDefined a} (Hexact : Exact b a) :=
  exact_maximal : forall (xA : a) (x : b), exact x `less_defined` xA -> exact x = xA.

Arguments ExactMaximal : clear implicits.
Arguments ExactMaximal a b {Hless Hexact}.

(** I don't think we've actually needed this fact so far. *)

(** ** [exact] instance for [T] *)

(** When [exact] doesn't reduce by [cbn], we may register rewrite lemmas in the
    hint database [exact] for doing simplification by [autorewrite with exact]. *)
Create HintDb exact.

#[global]
Instance Exact_T {a b} {r: Exact a b} : Exact a (T b)
  := fun x => Thunk (exact x).

#[global]
Instance ExactMaximal_T {a b} `{AA : ExactMaximal a b} : ExactMaximal (T a) b.
Proof.
  red. intros xA x H. inversion H; subst.
  unfold exact, Exact_T. f_equal. apply exact_maximal. assumption.
Qed.

(** * [is_approx]: relating approximations and pure values *)

(** In our paper, the definition of [is_approx] can be anything as long as it
    satisfies the [approx_exact] proposition. In this file, we choose the most
    direct definition that satisfies the [approx_exact] law. *)
Notation is_approx xA x := (xA `less_defined` exact x) (only parsing).
Infix "`is_approx`" := is_approx (at level 42, only parsing).

(** This corresponds to the proposition [approx_exact] in Section 5.3.

  And because of our particular definition, this is true by
  definition. However, this cannot be proved generically if the definition of
  [is_approx] can be anything. *)
Theorem approx_exact {a b} `{Exact b a} `{LessDefined a} :
  forall (x : b) (xA : a),
    xA `is_approx` x <-> xA `less_defined` (exact x).
Proof. reflexivity. Qed.

(** This corresponds to the proposition [approx_down] in Section 5.3.

  Again, because of the particular definition of [is_approx] we use here, this
  can be proved simply by the law of transitivity. *)
Lemma approx_down {a b} `{Hld : LessDefined a} `{Exact b a} `{PartialOrder _ eq (less_defined (a := a))}:
  forall (x : b) (xA yA : a),
    xA `less_defined` yA -> yA `is_approx` x -> xA `is_approx` x.
Proof.
  intros. etransitivity; eassumption.
Qed.
