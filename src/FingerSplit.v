(** * FingerSplit — annotated finger trees: worst-case O(log n) split and
      random access (Claessen-simplified, Hinze–Paterson measures).

    SCOPE: worst-case [O(log n)] COST bounds for [splitTree], [index],
    and [split] (Sections 1–7), plus full demand-correctness for random
    access (Section 8): [indexD_approx], [indexD_spec] and the
    size-monoid [index_spec], proved against the pruned clairvoyant
    lookup [lookupTreeA].  The pure [index] is the non-reconstructing
    [lookupTree] descent — see Section 2b for why the pivot-projection
    of [splitTree] is not demand-isolated.  Split's own correctness
    lemmas await the faithful reconstruction demand (improvement-plan
    Item 4) and are not stated.

    Measures are taken over an abstract [Monoid] (see [FingerMonoid.v]); random
    access is the [Monoid_size] instantiation; the same [splitTree] gives
    priority queues / ordered sequences under [Monoid_interval] /
    [Monoid_lastval].

    Headline results (this file):
      [indexD_cost]      : Tick.cost (indexD md i t xD)      ≤ c·depth t + c'
      [splitTreeD_cost]  : Tick.cost (splitTreeD md d p i t o) ≤ c·depth t + c'
      [index_O_log_n]    : ... ≤ c · log2 (size t) + c'
      [indexD_approx]    : the demand approximates the input tree
      [indexD_spec]      : the demand suffices to produce the demanded pivot
      [index_spec]       : size monoid — demand-correct AND O(log n)          *)

From Coq Require Import Arith Psatz Relations RelationClasses List.
From Clairvoyance Require Import Core Approx ApproxM Tick Prod Option.
From Clairvoyance Require Import FingerCore FingerSize.
From Clairvoyance Require Import FingerMonoid.   (* the Monoid interface *)

Import ListNotations.
Import Tick.Notations.
Open Scope tick_scope.
Open Scope monoid_scope.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

#[local] Existing Instance Exact_id | 1.

(* ================================================================= *)
(** ** Section 1: Annotated pure structure                             *)
(* ================================================================= *)

(** Each tuple caches its own measure; each [MMore] caches the measure
    of its middle spine.  [Digit] is reused from [FingerCore.v] (1–3). *)

Inductive MTuple (M A : Type) : Type :=
  | MPair   : M -> A -> A -> MTuple M A
  | MTriple : M -> A -> A -> A -> MTuple M A.
Arguments MPair   {M A}.
Arguments MTriple {M A}.

Inductive MSeq (M A : Type) : Type :=
  | MNil  : MSeq M A
  | MUnit : A -> MSeq M A
  | MMore : M -> Digit A -> MSeq M (MTuple M A) -> Digit A -> MSeq M A.
Arguments MNil  {M A}.
Arguments MUnit {M A}.
Arguments MMore {M A}.

(** *** O(1) measure readers (the whole point of the annotation). *)

Definition measureMTuple {M A} (t : MTuple M A) : M :=
  match t with MPair m _ _ => m | MTriple m _ _ _ => m end.

Definition measureDigit {M A} `{Monoid M} (md : A -> M) (d : Digit A) : M :=
  match d with
  | One x       => md x
  | Two x y     => md x <+> md y
  | Three x y z => md x <+> md y <+> md z
  end.

Definition measureSeq {M A} `{Monoid M} (md : A -> M) (s : MSeq M A) : M :=
  match s with
  | MNil           => mzero
  | MUnit x        => md x
  | MMore vm pr _ sf => measureDigit md pr <+> vm <+> measureDigit md sf
  end.   (* reads the cached [vm]; never traverses the spine *)

(** *** Smart constructors maintaining the cache. *)

Definition mpair {M A} `{Monoid M} (md : A -> M) (x y : A) : MTuple M A :=
  MPair (md x <+> md y) x y.
Definition mtriple {M A} `{Monoid M} (md : A -> M) (x y z : A) : MTuple M A :=
  MTriple (md x <+> md y <+> md z) x y z.

Definition mdeep {M A} `{Monoid M} (md : A -> M)
    (pr : Digit A) (m : MSeq M (MTuple M A)) (sf : Digit A) : MSeq M A :=
  MMore (measureSeq measureMTuple m) pr m sf.   (* cache = ‖middle‖, O(1) *)

(** *** Digit/tuple plumbing. *)

Definition digitToList {A} (d : Digit A) : list A :=
  match d with One x => [x] | Two x y => [x;y] | Three x y z => [x;y;z] end.

Definition tupleToDigit {M A} (t : MTuple M A) : Digit A :=
  match t with MPair _ x y => Two x y | MTriple _ x y z => Three x y z end.

(** A list of 0..3 elements as a (sub-)tree; O(1), no spine, no cascade. *)
Definition toTree {M A} `{Monoid M} (md : A -> M) (xs : list A) : MSeq M A :=
  match xs with
  | []      => MNil
  | [x]     => MUnit x
  | [x;y]   => mdeep md (One x) MNil (One y)
  | [x;y;z] => mdeep md (Two x y) MNil (One z)
  | _       => MNil                       (* unreachable: |xs| ≤ 3 *)
  end.

(** *** [depth] / [size] — port of [FingerSize.v] (verbatim shapes). *)
Fixpoint depth {M A} (s : MSeq M A) : nat :=
  match s with MNil => 0 | MUnit _ => 0 | MMore _ _ m _ => S (depth m) end.

Fixpoint size {M A} (s : MSeq M A) : nat :=
  match s with
  | MNil => 0 | MUnit _ => 1
  | MMore _ pr m sf => digit_size pr + 2 * size m + digit_size sf
  end.
(* [size_lower_bound], [depth_log_size], [size_pos] transfer unchanged
   (tuples still hold ≥ 2 elements); see M1. *)

(* ================================================================= *)
(** ** Section 2: Pure split                                           *)
(* ================================================================= *)

(** [splitDigit p i d] scans a 1–3 digit; at most one side is empty.
    Returns (left elements, pivot, right elements). *)
Definition splitDigit {M A} `{Monoid M} (md : A -> M)
    (p : M -> bool) (i : M) (d : Digit A) : list A * A * list A :=
  match d with
  | One x => ([], x, [])
  | Two x y =>
      if p (i <+> md x) then ([], x, [y]) else ([x], y, [])
  | Three x y z =>
      if p (i <+> md x) then ([], x, [y; z])
      else if p (i <+> md x <+> md y) then ([x], y, [z])
      else ([x; y], z, [])
  end.

(** [viewL]/[viewR]: uncons / unsnoc.  Polymorphic-recursive [Fixpoint]
    on the middle (the [glue {struct s1}] pattern).  The KEY structural
    fact (proved in M4) is visible here: when the front [One] empties, we
    refill by borrowing a whole tuple, yielding a [Two]/[Three] front
    (size ≥ 2) — so a [viewL] cascade only runs through consecutive
    [One]-front levels. *)
Fixpoint viewL {M A} `{Monoid M} (md : A -> M) (dflt : A) (t : MSeq M A)
    {struct t} : option (A * MSeq M A) :=
  match t with
  | MNil    => None
  | MUnit x => Some (x, MNil)
  | MMore vm pr m sf =>
      match pr with
      | Two x y     => Some (x, mdeep md (One y) m sf)
      | Three x y z => Some (x, mdeep md (Two y z) m sf)
      | One x =>
          match viewL measureMTuple (MPair mzero dflt dflt) m with
          | None         => Some (x, toTree md (digitToList sf))
          | Some (t1, m') => Some (x, mdeep md (tupleToDigit t1) m' sf)
          end
      end
  end.

Fixpoint viewR {M A} `{Monoid M} (md : A -> M) (dflt : A) (t : MSeq M A)
    {struct t} : option (MSeq M A * A) :=
  match t with
  | MNil    => None
  | MUnit x => Some (MNil, x)
  | MMore vm pr m sf =>
      match sf with
      | Two x y     => Some (mdeep md pr m (One x), y)
      | Three x y z => Some (mdeep md pr m (Two x y), z)
      | One x =>
          match viewR measureMTuple (MPair mzero dflt dflt) m with
          | None         => Some (toTree md (digitToList pr), x)
          | Some (m', t1) => Some (mdeep md pr m' (tupleToDigit t1), x)
          end
      end
  end.

(** [deepL]/[deepR]: rebuild a side from a 0–2 residual.  Empty residual
    ⇒ borrow from the middle (front/rear becomes [Two]/[Three]).
    NON-recursive: the cascade lives entirely in [viewL]/[viewR]. *)
Definition deepL {M A} `{Monoid M} (md : A -> M) (dflt : A)
    (pr : list A) (m : MSeq M (MTuple M A)) (sf : Digit A) : MSeq M A :=
  match pr with
  | [x]     => mdeep md (One x) m sf
  | [x;y]   => mdeep md (Two x y) m sf
  | [x;y;z] => mdeep md (Three x y z) m sf
  | [] =>
      match viewL measureMTuple (MPair mzero dflt dflt) m with
      | None          => toTree md (digitToList sf)
      | Some (t1, m') => mdeep md (tupleToDigit t1) m' sf
      end
  | _ => MNil
  end.

Definition deepR {M A} `{Monoid M} (md : A -> M) (dflt : A)
    (pr : Digit A) (m : MSeq M (MTuple M A)) (sf : list A) : MSeq M A :=
  match sf with
  | [x]     => mdeep md pr m (One x)
  | [x;y]   => mdeep md pr m (Two x y)
  | [x;y;z] => mdeep md pr m (Three x y z)
  | [] =>
      match viewR measureMTuple (MPair mzero dflt dflt) m with
      | None          => toTree md (digitToList pr)
      | Some (m', t1) => mdeep md pr m' (tupleToDigit t1)
      end
  | _ => MNil
  end.

(** [splitTree p i t]: descend to the position where [p] flips, returning
    (smaller, pivot, bigger).  Polymorphic-recursive on the middle, the
    [glue {struct t}] pattern; [dflt] makes the unreachable [MNil] case
    total.  Cf. Leroy's BST [split], with [deepL]/[deepR] for [node]. *)
Fixpoint splitTree {M A} `{Monoid M} (md : A -> M) (dflt : A)
    (p : M -> bool) (i : M) (t : MSeq M A) {struct t}
    : MSeq M A * A * MSeq M A :=
  match t with
  | MNil    => (MNil, dflt, MNil)          (* unreachable: ¬p(0) ∧ p(‖t‖) *)
  | MUnit x => (MNil, x, MNil)
  | MMore vm pr m sf =>
      let vpr  := i <+> measureDigit md pr in
      let vm_t := vpr <+> vm in
      if p vpr then
        let '(l, x, r) := splitDigit md p i pr in
        (toTree md l, x, deepL md dflt r m sf)
      else if p vm_t then
        let '(ml, xs, mr) :=
          splitTree measureMTuple (MPair mzero dflt dflt) p vpr m in
        let '(l, x, r) :=
          splitDigit md p (vpr <+> measureSeq measureMTuple ml) (tupleToDigit xs) in
        (deepR md dflt pr ml l, x, deepL md dflt r mr sf)
      else
        let '(l, x, r) := splitDigit md p vm_t sf in
        (deepR md dflt pr m l, x, toTree md r)
  end.

(* ================================================================= *)
(** ** Section 2b: Pure lookup (the non-reconstructing descent)         *)
(* ================================================================= *)

(** [lookupDigit p i d]: scan a 1–3 digit, returning the accumulated
    measure up to (but excluding) the pivot together with the pivot.
    The scan conditions are syntactically those of [splitDigit], so the
    two functions locate the same pivot. *)
Definition lookupDigit {M A} `{Monoid M} (md : A -> M)
    (p : M -> bool) (i : M) (d : Digit A) : M * A :=
  match d with
  | One x => (i, x)
  | Two x y =>
      if p (i <+> md x) then (i, x) else (i <+> md x, y)
  | Three x y z =>
      if p (i <+> md x) then (i, x)
      else if p (i <+> md x <+> md y) then (i <+> md x, y)
      else (i <+> md x <+> md y, z)
  end.

(** [lookupTree p i t]: descend to the pivot WITHOUT reconstructing the
    halves — the [lookupTree] of Hinze–Paterson's library (cf.
    [Data.Sequence]), with the prefix measure threaded up through the
    recursion instead of being recomputed from the left half.

    Why this function exists: projecting the pivot out of [splitTree]
    is NOT demand-isolated.  At each recursive level the pivot's
    position inside the borrowed tuple [xs] is found by splitting at
    base [vpr <+> ‖ml‖], where [ml] is the recursively reconstructed
    left half — so a lazy consumer of the pivot alone still forces the
    cached-measure chain of every left half down the descent (for the
    size monoid, [p = (i <?)] inspects its argument, so the forcing is
    real).  Bounding THAT cost needs the §C.2 chain-telescoping
    argument, i.e. the faithful-split machinery.  [lookupTree] threads
    the base measure [b] through the recursion instead, touching only
    the descent path: the demand pattern [(⊥, xD, ⊥)] is faithful for
    it, and the branch structure (and hence the tick structure) is
    identical to [splitTree]'s. *)
Fixpoint lookupTree {M A} `{Monoid M} (md : A -> M) (dflt : A)
    (p : M -> bool) (i : M) (t : MSeq M A) {struct t} : M * A :=
  match t with
  | MNil    => (i, dflt)                   (* unreachable under the contract *)
  | MUnit x => (i, x)
  | MMore vm pr m sf =>
      let vpr  := i <+> measureDigit md pr in
      let vm_t := vpr <+> vm in
      if p vpr then lookupDigit md p i pr
      else if p vm_t then
        let '(b, xs) :=
          lookupTree measureMTuple (MPair mzero dflt dflt) p vpr m in
        lookupDigit md p b (tupleToDigit xs)
      else lookupDigit md p vm_t sf
  end.

(** Cache validity: every [MMore] cache equals the measure of its
    middle.  Trees built by the smart constructor [mdeep] satisfy this
    by construction; the correctness lemmas below assume it (the cost
    lemmas do not need it).  Note the predicate is independent of the
    element measure [md]: spine-level measures are always cache reads
    ([measureMTuple]). *)
Fixpoint mseq_valid {M A} `{Monoid M} (t : MSeq M A) : Prop :=
  match t with
  | MNil | MUnit _ => True
  | MMore vm _ m _ => vm = measureSeq measureMTuple m /\ mseq_valid m
  end.

(* ================================================================= *)
(** ** Section 3: Random access and friends (Leroy's get/set/delete)   *)
(* ================================================================= *)

(** Specialise to the size monoid: [md := fun _ => 1], [p := i <? ·]. *)
Section RandomAccess.
  Context {A : Type}.
  Definition sz1 : A -> nat := fun _ => 1.

  (** Read the [i]-th element ([dflt] returned iff out of bounds).
      Defined via the non-reconstructing [lookupTree] descent — see the
      comment there for why the pivot-projection of [splitTree] would
      not be demand-isolated.  [lookupTree] follows the same branch
      conditions as [splitTree], so the two locate the same pivot. *)
  Definition index (dflt : A) (i : nat) (t : MSeq nat A) : A :=
    snd (lookupTree sz1 dflt (fun s => i <? s) 0 t).

  (** [concat] is your [FingerConcat.glue]/[concat], ported to [MSeq];
      [fcons] is the annotated cons.  Stubs for the API shape: *)
  (* Definition update (dflt v : A) (i : nat) (t : MSeq nat A) : MSeq nat A :=
       let '(l, _, r) := splitTree sz1 dflt (fun s => i <? s) 0 t in
       concat l (fcons v r).
     Definition delete (dflt : A) (i : nat) (t : MSeq nat A) : MSeq nat A :=
       let '(l, _, r) := splitTree sz1 dflt (fun s => i <? s) 0 t in
       concat l r. *)
End RandomAccess.

(* ================================================================= *)
(** ** Section 4: Approximation types (cost scope only)                *)
(* ================================================================= *)

(** [T]-wrapped fields for laziness; cached measures stay un-thunked
    (computed eagerly, O(1), untickeded).  Reuses [DigitA] from
    [FingerCore.v].  Only [Exact]/[BottomOf]/[LessDefined] are provided —
    [Lub]/[LubLaw] and the order laws are correctness scope (omit, per the
    [FingerConcat.v] precedent). *)

Inductive MTupleA (M A : Type) : Type :=
  | MPairA   : M -> T A -> T A -> MTupleA M A
  | MTripleA : M -> T A -> T A -> T A -> MTupleA M A.
Arguments MPairA   {M A}.
Arguments MTripleA {M A}.

Inductive MSeqA (M A : Type) : Type :=
  | MNilA  : MSeqA M A
  | MUnitA : T A -> MSeqA M A
  | MMoreA : M -> T (DigitA A) -> T (MSeqA M (MTupleA M A)) -> T (DigitA A) -> MSeqA M A.
Arguments MNilA  {M A}.
Arguments MUnitA {M A}.
Arguments MMoreA {M A}.

(** Cached measures are strict fields, so they can be read off an
    approximation without forcing anything further — the approximation
    side of [measureMTuple]. *)
Definition measureMTupleA {M A} (t : MTupleA M A) : M :=
  match t with MPairA m _ _ => m | MTripleA m _ _ _ => m end.

#[global] Instance Exact_MTuple {M} : forall A B `{Exact A B}, Exact (MTuple M A) (MTupleA M B) :=
  fun A B _ t => match t with
    | MPair m x y    => MPairA m (exact x) (exact y)
    | MTriple m x y z => MTripleA m (exact x) (exact y) (exact z)
    end.

#[global] Instance Exact_MSeq {M} : forall A B `{Exact A B}, Exact (MSeq M A) (MSeqA M B) :=
  fix go A B _ s := match s with
    | MNil           => MNilA
    | MUnit x        => MUnitA (exact x)
    | MMore vm pr m sf => MMoreA vm (exact pr) (Thunk (go _ _ _ m)) (exact sf)
    end.

#[global] Instance BottomOf_MSeqA {M A} : BottomOf (MSeqA M A) :=
  fun s => match s with
    | MNilA         => MNilA
    | MUnitA _      => MUnitA Undefined
    | MMoreA vm _ _ _ => MMoreA vm Undefined Undefined Undefined
    end.

Inductive LessDefined_MTupleA {M A} `{LessDefined A} : LessDefined (MTupleA M A) :=
  | LD_MPairA (m : M) x1 x2 y1 y2 :
      x1 `less_defined` x2 -> y1 `less_defined` y2 ->
      MPairA m x1 y1 `less_defined` MPairA m x2 y2
  | LD_MTripleA (m : M) x1 x2 y1 y2 z1 z2 :
      x1 `less_defined` x2 -> y1 `less_defined` y2 -> z1 `less_defined` z2 ->
      MTripleA m x1 y1 z1 `less_defined` MTripleA m x2 y2 z2.
#[global] Existing Instance LessDefined_MTupleA.
#[global] Hint Constructors LessDefined_MTupleA : core.

Inductive LessDefined_MSeqA {M A} `{LessDefined A} : LessDefined (MSeqA M A) :=
  | LD_MNilA  : MNilA `less_defined` MNilA
  | LD_MUnitA x1 x2 : x1 `less_defined` x2 -> MUnitA x1 `less_defined` MUnitA x2
  | LD_MMoreA vm f1 f2 m1 m2 r1 r2 :
      f1 `less_defined` f2 -> m1 `less_defined` m2 -> r1 `less_defined` r2 ->
      MMoreA vm f1 m1 r1 `less_defined` MMoreA vm f2 m2 r2.
#[global] Existing Instance LessDefined_MSeqA.
#[global] Hint Constructors LessDefined_MSeqA : core.

(** *** Order laws (correctness scope) — mirrors FingerCore.v's
    [DigitA]/[TupleA]/[SeqA] ladder, innermost-first. *)

Lemma LessDefined_MTupleA_refl {M A} `{LessDefined A} :
  (forall (x : A), x `less_defined` x) ->
  forall (t : MTupleA M A), t `less_defined` t.
Proof.
  intros HR [m x y | m x y z];
    repeat match goal with t : T A |- _ => destruct t end;
    auto.
Qed.
#[global] Hint Resolve LessDefined_MTupleA_refl : core.

#[global] Instance Reflexive_LessDefined_MTupleA {M A}
  `{LessDefined A, !Reflexive (less_defined (a := A))} :
  Reflexive (@less_defined (MTupleA M A) _).
Proof. unfold Reflexive. auto. Qed.

Lemma LessDefined_MSeqA_refl {M} :
  forall (A : Type) (LD : LessDefined A),
    (forall (x : A), x `less_defined` x) ->
    forall (s : MSeqA M A), s `less_defined` s.
Proof.
  fix SELF 4.
  intros A LD HR [ | xT | vm prT mT sfT ].
  - constructor.
  - constructor. destruct xT; constructor; auto.
  - constructor.
    + destruct prT as [d|]; constructor.
      apply LessDefined_DigitA_refl; auto.
    + destruct mT as [m'|]; constructor.
      apply (SELF (MTupleA M A) _
               (fun t => @LessDefined_MTupleA_refl M A LD HR t) m').
    + destruct sfT as [d|]; constructor.
      apply LessDefined_DigitA_refl; auto.
Qed.
#[global] Hint Resolve LessDefined_MSeqA_refl : core.

#[global] Instance Reflexive_LessDefined_MSeqA {M A}
  `{LessDefined A, !Reflexive (less_defined (a := A))} :
  Reflexive (@less_defined (MSeqA M A) _).
Proof. unfold Reflexive. intro s. apply LessDefined_MSeqA_refl; auto. Qed.

(** The demand on [splitTree]'s output triple: [Undefined] = not demanded. *)
Definition SplitDmd (M A : Type) : Type :=
  (T (MSeqA M A) * T A * T (MSeqA M A))%type.

(* ================================================================= *)
(** ** Section 5: Demand functions (tick-faithful; values are M9)      *)
(* ================================================================= *)

(** Reconstruction demand helpers.  COST behaviour is what matters here:
    each is O(1) when its output demand is forced, and **cost 0 when the
    demand is [Undefined]** — this is what zeroes reconstruction for
    [index].  [viewLD]/[viewRD] carry the cascade; their cost is governed
    by [lvc]/[rvc] (Section 6).  Bodies below are cost-faithful scaffolds;
    the returned input demands are placeholders for M9 (cf. [unbundle]). *)

Definition toTreeD {M A} (outD : T (MSeqA M A)) : Tick unit :=
  match outD with Undefined => Tick.ret tt | Thunk _ => Tick.tick >> Tick.ret tt end.
Arguments toTreeD: simpl nomatch.

(* viewLD/viewRD : the one-uncons demands; recurse into the middle on a
   [One] front (the cascade).  Fixpoints on the (pure) tree so the cost
   recurrence matches [lvc]/[rvc] exactly: one [Tick.tick] per visited
   [MMore], plus a recursive call when the touched digit is [One].  The
   returned input demand is [Undefined] for now (M9 placeholder) — what
   we prove here is the cost bound, which is independent of [outD]. *)
Fixpoint viewLD {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (t : MSeq M A) (outD : T (MSeqA M B)) {struct t} : Tick (T (MSeqA M B)) :=
  Tick.tick >>
  match t with
  | MNil    => Tick.ret Undefined
  | MUnit _ => Tick.ret Undefined
  | MMore _ pr m _ =>
      match pr with
      | One _ =>
          let+ _ := viewLD (A := MTuple M A) (B := MTupleA M B)
                      measureMTuple (MPair mzero dflt dflt) m Undefined in
          Tick.ret Undefined
      | Two _ _     => Tick.ret Undefined
      | Three _ _ _ => Tick.ret Undefined
      end
  end.
Arguments viewLD : simpl nomatch.

Fixpoint viewRD {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (t : MSeq M A) (outD : T (MSeqA M B)) {struct t} : Tick (T (MSeqA M B)) :=
  Tick.tick >>
  match t with
  | MNil    => Tick.ret Undefined
  | MUnit _ => Tick.ret Undefined
  | MMore _ _ m sf =>
      match sf with
      | One _ =>
          let+ _ := viewRD (A := MTuple M A) (B := MTupleA M B)
                      measureMTuple (MPair mzero dflt dflt) m Undefined in
          Tick.ret Undefined
      | Two _ _     => Tick.ret Undefined
      | Three _ _ _ => Tick.ret Undefined
      end
  end.
Arguments viewRD : simpl nomatch.
(* deepLD r m sf outD : cost 0 if outD = Undefined; else one [viewLD] (if
   the residual is empty) + O(1).  Promoted from Parameter so [indexD_cost]
   can compute: at [Undefined] the body reduces to [Tick.ret Undefined]
   (cost 0), zeroing the reconstruction along the [index] descent.  The
   returned input demand is an M9 placeholder. *)
Definition deepLD {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (r : list A) (m : MSeq M (MTuple M A)) (sf : Digit A) (outD : T (MSeqA M B))
    : Tick (T (MSeqA M (MTupleA M B))) :=
  match outD with
  | Undefined => Tick.ret Undefined
  | Thunk _ =>
      match r with
      | [] => let+ _ := viewLD (A := MTuple M A) (B := MTupleA M B)
                          measureMTuple (MPair mzero dflt dflt) m Undefined in
              Tick.ret Undefined
      | _  => Tick.ret Undefined
      end
  end.
Arguments deepLD : simpl nomatch.

Definition deepRD {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (pr : Digit A) (m : MSeq M (MTuple M A)) (l : list A) (outD : T (MSeqA M B))
    : Tick (T (MSeqA M (MTupleA M B))) :=
  match outD with
  | Undefined => Tick.ret Undefined
  | Thunk _ =>
      match l with
      | [] => let+ _ := viewRD (A := MTuple M A) (B := MTupleA M B)
                          measureMTuple (MPair mzero dflt dflt) m Undefined in
              Tick.ret Undefined
      | _  => Tick.ret Undefined
      end
  end.
Arguments deepRD : simpl nomatch.

(** *** The pivot demand threaded through the recursion.

    [pivotNodeDmd md p b xs xD] is the demand a one-level lookup places
    on the borrowed pivot tuple [xs] when scanned at base measure [b]:
    components the scan measures are demanded in full (computing [md]
    of an element forces it, for a generic [md]); the pivot component
    carries the incoming element demand [xD] when it is not itself
    measured; components beyond the pivot are not demanded.  The scan
    conditions are syntactically [lookupDigit]'s on [tupleToDigit xs],
    hence [splitDigit]'s. *)
Definition pivotNodeDmd {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M)
    (p : M -> bool) (b : M) (xs : MTuple M A) (xD : T B) : MTupleA M B :=
  match xs with
  | MPair c x y =>
      if p (b <+> md x)
      then MPairA c (Thunk (exact x)) Undefined
      else MPairA c (Thunk (exact x)) xD
  | MTriple c x y z =>
      if p (b <+> md x)
      then MTripleA c (Thunk (exact x)) Undefined Undefined
      else if p (b <+> md x <+> md y)
      then MTripleA c (Thunk (exact x)) (Thunk (exact y)) Undefined
      else MTripleA c (Thunk (exact x)) (Thunk (exact y)) xD
  end.
Arguments pivotNodeDmd : simpl never.

(** [pivotDmd]: locate the pivot tuple of the middle [m] by the pure
    [lookupTree] recompute (demand functions take pure inputs, so the
    descent is replayable for free), and wrap [pivotNodeDmd] around it.
    This is what the recursive call of [splitTreeD] passes as the pivot
    demand — the half-demands stay [Undefined] (the reconstruction
    scaffold; see SPLIT_NOTE §7 / M9). *)
Definition pivotDmd {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (p : M -> bool) (i : M) (m : MSeq M (MTuple M A)) (xD : T B)
    : T (MTupleA M B) :=
  let '(b, xs) := lookupTree measureMTuple (MPair mzero dflt dflt) p i m in
  Thunk (pivotNodeDmd md p b xs xD).
Arguments pivotDmd : simpl never.

(** [splitTreeD]: one [Tick.tick] per visited [MMore]; reconstruction
    gated by the half-demands [lD]/[rD]; recurse on the middle with the
    genuine pivot demand [pivotDmd] (so the demand placed on the input
    suffices to produce the demanded pivot — [indexD_spec] below).  When
    [lD = rD = Undefined] (the [index] case) every [toTreeD]/[deepLD]/
    [deepRD] costs 0, leaving only the per-level tick + the descent. *)
Fixpoint splitTreeD {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (p : M -> bool) (i : M) (t : MSeq M A) (outD : SplitDmd M B) {struct t}
    : Tick (T (MSeqA M B)) :=
  Tick.tick >>
  match t with
  | MNil    => Tick.ret Undefined
  | MUnit x => let '(_, xD, _) := outD in Tick.ret (Thunk (MUnitA xD))
  | MMore vm pr m sf =>
      let '(lD, xD, rD) := outD in
      let vpr  := i <+> measureDigit md pr in
      let vm_t := vpr <+> vm in
      if p vpr then
        let+ _  := toTreeD lD in
        let+ mD := deepLD md dflt [] m sf rD in
        Tick.ret (Thunk (MMoreA vm (exact pr) mD (exact sf)))
      else if p vm_t then
        let+ mD := splitTreeD (A := MTuple M A) (B := MTupleA M B)
                     measureMTuple (MPair mzero dflt dflt) p vpr m
                     (Undefined, pivotDmd md dflt p vpr m xD, Undefined) in
        let+ _  := deepRD md dflt pr m [] lD in
        let+ _  := deepLD md dflt [] m sf rD in
        Tick.ret (Thunk (MMoreA vm (exact pr) mD (exact sf)))
      else
        let+ _  := deepRD md dflt pr m [] lD in
        let+ _  := toTreeD rD in
        Tick.ret (Thunk (MMoreA vm (exact pr) (Thunk (bottom_of (exact m))) (exact sf)))
  end.

Arguments splitTreeD : simpl nomatch.

(** Random access demand: the halves are NOT demanded. *)
Definition indexD {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (p : M -> bool) (i : M) (t : MSeq M A) (xD : T B) : Tick (T (MSeqA M B)) :=
  splitTreeD md dflt p i t (Undefined, xD, Undefined).


(* ================================================================= *)
(** ** Section 6: Cost — the one new lemma (M7) and the theorems        *)
(* ================================================================= *)

Definition split_c1 : nat := 12.   (* tune during proof *)
Definition split_c2 : nat := 24.

(** *** The one-step view cost (internal potential for M7).
    [lvc s] = ticks of [viewLD] at full demand: a [One] front empties and
    recurses; a [Two]/[Three] front is O(1). *)
Fixpoint lvc {M A} (s : MSeq M A) : nat :=
  match s with
  | MNil | MUnit _ => 1
  | MMore _ (One _)       m _ => S (lvc m)
  | MMore _ (Two _ _)     _ _ => 1
  | MMore _ (Three _ _ _) _ _ => 1
  end.
Fixpoint rvc {M A} (s : MSeq M A) : nat :=
  match s with
  | MNil | MUnit _ => 1
  | MMore _ _ m (One _)       => S (rvc m)
  | MMore _ _ _ (Two _ _)     => 1
  | MMore _ _ _ (Three _ _ _) => 1
  end.

Lemma lvc_le_depth {M A} (s : MSeq M A) : lvc s <= S (depth s).
Proof.
  revert A s. fix SELF 2.
  destruct s as [|x|vm pr m sf].
  - simpl. lia.
  - simpl. lia.
  - destruct pr as [a|a b|a b c]; simpl.
    + specialize (SELF (MTuple M A) m). lia.
    + lia.
    + lia.
Qed.

Lemma rvc_le_depth {M A} (s : MSeq M A) : rvc s <= S (depth s).
Proof. 
    revert A s. fix SELF 2.
    destruct s as [|x|vm pr m sf]. 
    - simpl. lia.
    - simpl. lia.
    - destruct sf as [a|a b|a b c]; simpl.
      + specialize (SELF (MTuple M A) m). lia.
      + lia.
      + lia.
Qed.

(** [viewLD] cost is exactly the internal potential. *)
Lemma viewLD_cost {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (t : MSeq M A) (outD : T (MSeqA M B)) :
  Tick.cost (viewLD md dflt t outD) <= lvc t.
Proof.
  generalize dependent outD.
  generalize dependent t.
  generalize dependent dflt.
  generalize dependent md.
  generalize dependent B.
  generalize dependent A.
  fix SELF 6.
  intros A B HE md dflt t outD.
  destruct t as [|x|vm pr m sf].
  - simpl. lia.
  - simpl. lia.
  - destruct pr as [a|a b|a b c].
    + simpl.
      specialize (SELF (MTuple M A) (MTupleA M B) _
                       measureMTuple (MPair mzero dflt dflt) m Undefined).
      lia.
    + simpl. lia.
    + simpl. lia.
Qed.

Lemma viewRD_cost {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (t : MSeq M A) (outD : T (MSeqA M B)) :
  Tick.cost (viewRD md dflt t outD) <= rvc t.
Proof.
  generalize dependent outD.
  generalize dependent t.
  generalize dependent dflt.
  generalize dependent md.
  generalize dependent B.
  generalize dependent A.
  fix SELF 6.
  intros A B HE md dflt t outD.
  destruct t as [|x|vm pr m sf].
  - simpl. lia.
  - simpl. lia.
  - destruct sf as [a|a b|a b c].
    + simpl.
      specialize (SELF (MTuple M A) (MTupleA M B) _
                       measureMTuple (MPair mzero dflt dflt) m Undefined).
      lia.
    + simpl. lia.
    + simpl. lia.
Qed.

Lemma toTreeD_cost {M A} (outD : T (MSeqA M A)) : Tick.cost (toTreeD outD) <= 1.
Proof. 
  destruct outD; simpl; lia. 
Qed.

Lemma deepLD_cost {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (r : list A) (m : MSeq M (MTuple M A)) (sf : Digit A) (rD : T (MSeqA M B)) :
  Tick.cost (deepLD md dflt r m sf rD) <= lvc m.
Proof.
  unfold deepLD. destruct rD as [r0|].
  - destruct r as [|a r'].
    + pose proof (viewLD_cost (A := MTuple M A) (B := MTupleA M B)
                    measureMTuple (MPair mzero dflt dflt) m Undefined) as Hv.
      simpl Tick.cost. lia.
    + simpl Tick.cost. lia.
  - simpl Tick.cost. lia.
Qed.

Lemma deepRD_cost {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (pr : Digit A) (m : MSeq M (MTuple M A)) (l : list A) (lD : T (MSeqA M B)) :
  Tick.cost (deepRD md dflt pr m l lD) <= rvc m.
Proof.
  unfold deepRD. destruct lD as [l0|].
  - destruct l as [|a l'].
    + pose proof (viewRD_cost (A := MTuple M A) (B := MTupleA M B)
                    measureMTuple (MPair mzero dflt dflt) m Undefined) as Hv.
      simpl Tick.cost. lia.
    + simpl Tick.cost. lia.
  - simpl Tick.cost. lia.
Qed.


(** *** M6 — random access: clean descent bound, NO reconstruction.
    With both halves [Undefined], every [toTreeD]/[deepLD]/[deepRD] costs
    0, so each level is O(1) and the recursion is one level shallower;
    [glueD'_cost]-shaped induction via the polymorphic principle. *)
Theorem indexD_cost {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (p : M -> bool) (i : M) (t : MSeq M A) (xD : T B) :
  Tick.cost (indexD md dflt p i t xD) <= split_c1 * depth t + split_c2.
Proof.
  unfold indexD.
  generalize dependent xD.
  generalize dependent t.
  generalize dependent i.
  generalize dependent p.
  generalize dependent dflt.
  generalize dependent md.
  generalize dependent B.
  generalize dependent A.
  fix SELF 8.
  intros A B HE md dflt p i t xD.
  destruct t as [|x|vm pr m sf].
  - simpl. unfold split_c1, split_c2. lia.
  - simpl. unfold split_c1, split_c2. lia.
  - simpl depth.
    simpl. unfold split_c1, split_c2.
    simpl depth.
    destruct (p (i <+> measureDigit md pr)).
      * simpl Tick.cost. unfold split_c1, split_c2. lia.
      * destruct (p (i <+> measureDigit md pr <+> vm)).
        -- specialize (SELF (MTuple M A) (MTupleA M B) _
                     measureMTuple (MPair mzero dflt dflt) p
                     (i <+> measureDigit md pr) m
                     (pivotDmd md dflt p (i <+> measureDigit md pr) m xD)).
           simpl Tick.cost. unfold split_c1, split_c2 in *. lia.
        -- simpl Tick.cost. unfold split_c1, split_c2. lia.
Qed.

(** *** M8 — full split: descent (M6) + two reconstructions (M7). *)
Theorem splitTreeD_cost {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (p : M -> bool) (i : M) (t : MSeq M A) (outD : SplitDmd M B) :
  Tick.cost (splitTreeD md dflt p i t outD) <= (split_c1 + 2) * depth t + (split_c2 + 3).
Proof.
  destruct t as [|x|vm pr m sf].
  - simpl. unfold split_c1, split_c2. lia.
  - simpl. unfold split_c1, split_c2.     
    destruct outD as [ [lD xD] rD]; simpl; lia.
  - destruct outD as [ [lD xD] rD].
    pose proof (toTreeD_cost lD) as HtL.
    pose proof (toTreeD_cost rD) as HtR.
    pose proof (deepLD_cost md dflt (@nil A) m sf rD) as HdL.
    pose proof (deepRD_cost md dflt pr m (@nil A) lD) as HdR.
    pose proof (lvc_le_depth m) as Hlm.
    pose proof (rvc_le_depth m) as Hrm.
    pose proof (indexD_cost (A := MTuple M A) (B := MTupleA M B)
                  measureMTuple (MPair mzero dflt dflt) p
                  (i <+> measureDigit md pr) m
                  (pivotDmd md dflt p (i <+> measureDigit md pr) m xD)) as Hidx.
    unfold indexD in Hidx.
    simpl depth. simpl.
    destruct (p (i <+> measureDigit md pr)).
    + simpl Tick.cost. unfold split_c1, split_c2 in *. lia.
    + destruct (p (i <+> measureDigit md pr <+> vm)).
      * simpl Tick.cost. unfold split_c1, split_c2 in *. lia.
      * simpl Tick.cost. unfold split_c1, split_c2 in *. lia.
Qed.




(* ================================================================= *)
(** ** Section 7 Aux: alternatives*)


Lemma MSeq_ind_poly {M} (P : forall A, MSeq M A -> Prop) :
  (forall A, P A MNil) ->
  (forall A x, P A (MUnit x)) ->
  (forall A vm f m r, P (MTuple M A) m -> P A (MMore vm f m r)) ->
  forall A (s : MSeq M A), P A s.
Proof. 
  intros HNil HUnit HMore. fix SELF 2.
  intros A s; destruct s as [|x|vm f m r]; [apply HNil|apply HUnit|apply HMore; apply SELF]. 
Qed.

Lemma MSeq_nil_dec {M A} (s : MSeq M A) : s = MNil \/ s <> MNil.
Proof. 
  destruct s; [left; reflexivity|right; discriminate|right; discriminate]. 
Qed.

Lemma size_lower_bound {M} : forall A (s : MSeq M A), s <> MNil -> 2 ^ depth s <= size s.
Proof.
  apply (MSeq_ind_poly (M := M) (fun A s => s <> MNil -> 2 ^ depth s <= size s)).
  - intros A Hne; contradiction.
  - intros A x _; simpl; lia.
  - intros A vm f m r IH _.
    simpl depth; simpl size.
    destruct (@MSeq_nil_dec M _ m) as [Hm | Hm].
    + subst m; simpl size.
      destruct f as [a|a b|a b c]; destruct r as [d|d e|d e g];
        simpl digit_size; simpl Nat.pow; lia.
    + specialize (IH Hm).
      destruct f as [a|a b|a b c]; destruct r as [d|d e|d e g];
        simpl digit_size; simpl Nat.pow; nia.
Qed.

Lemma size_pos {M} : forall A (s : MSeq M A), s <> MNil -> 0 < size s.
Proof. 
  intros A s Hne; destruct s as [|x|vm u m v]; [contradiction|simpl;lia|];
  simpl; destruct u; simpl; lia. 
Qed.

Corollary depth_log_size {M} : forall A (s : MSeq M A), s <> MNil -> depth s <= Nat.log2 (size s).
Proof.
  intros A s Hne.
  pose proof (@size_lower_bound _ _ s Hne) as Hsize.
  pose proof (@size_pos _ _ s Hne) as Hpos.
  pose proof (@Nat.log2_spec _ Hpos) as [Hlow Hhigh].
  destruct (Nat.le_gt_cases (depth s) (Nat.log2 (size s))) as [Hle|Hgt]; [auto|exfalso].
  apply (Nat.lt_irrefl (size s)).
  eapply Nat.lt_le_trans; [exact Hhigh|].
  eapply Nat.le_trans; [|exact Hsize]. apply Nat.pow_le_mono_r; lia.
Qed.

(* ================================================================= *)
(** ** Section 7: O(log n) corollaries (mirror concatD_cost_O_log_n)    *)
(* ================================================================= *)

(** Needs [depth_log_size]/[size_pos] ported to [MSeq] (M1). *)
Corollary index_O_log_n {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (p : M -> bool) (i : M) (t : MSeq M A) (xD : T B) :
  t <> MNil -> Tick.cost (indexD md dflt p i t xD) <= split_c1 * Nat.log2 (size t) + split_c2.
Proof.
  intro Hne.
  pose proof (indexD_cost md dflt p i t xD) as Hc.
  pose proof (@depth_log_size _ _ t Hne) as Hd.
  unfold split_c1, split_c2 in *. nia.
Qed.

Corollary split_O_log_n {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (p : M -> bool) (i : M) (t : MSeq M A) (outD : SplitDmd M B) :
  t <> MNil ->
  Tick.cost (splitTreeD md dflt p i t outD)
    <= (split_c1 + 2) * Nat.log2 (size t) + (split_c2 + 3).
Proof.
  intro Hne.
  pose proof (splitTreeD_cost md dflt p i t outD) as Hc.
  pose proof (@depth_log_size _ _ t Hne) as Hd.
  unfold split_c1, split_c2 in *. nia.
Qed.

(* ================================================================= *)
(** ** Section 8: Demand-correctness for random access                 *)
(* ================================================================= *)

(** Closes the [index] half of the correctness scope: [indexD_approx]
    (the demand returned by [indexD] is a genuine approximation of the
    input tree) and [indexD_spec] (the demand suffices for a clairvoyant
    execution to produce the demanded pivot within the demanded cost),
    proved against the pruned clairvoyant lookup [lookupTreeA] — the
    translation of the non-reconstructing [lookupTree] (see Section 2b
    for why the pivot-projection of [splitTree] is not the right
    function to translate).

    The full split contract ([split_correct], and [splitTreeD_approx]/
    [splitTreeD_spec] against a faithful reconstruction demand) remains
    future work — SPLIT_NOTE §5 / M9. *)

(** *** 8a. Order and measure facts *)

Lemma LessDefined_MTupleA_trans {M A} `{LessDefined A} :
  (forall (x y z : A), x `less_defined` y -> y `less_defined` z -> x `less_defined` z) ->
  forall (x y z : MTupleA M A),
    x `less_defined` y -> y `less_defined` z -> x `less_defined` z.
Proof.
  intro.
  repeat invert_clear 1;
    repeat match goal with
      | H : ?x `less_defined` ?y |- _ => invert_clear H
      end;
    repeat constructor; eauto.
Qed.
#[global] Hint Resolve LessDefined_MTupleA_trans : core.

#[global] Instance Transitive_LessDefined_MTupleA {M A}
  `{LessDefined A, Transitive A less_defined} :
  Transitive (@less_defined (MTupleA M A) _).
Proof. unfold Transitive. eauto. Qed.

(** Any approximation below [exact t] carries [t]'s true cached measure:
    the [LessDefined] constructors pin the strict measure field. *)
Lemma measureMTupleA_coh {M A B} `{LessDefined B} `{Exact A B}
    (t : MTuple M A) (v : MTupleA M B) :
  v `less_defined` exact t -> measureMTupleA v = measureMTuple t.
Proof.
  destruct t as [c x y | c x y z]; cbn; intro Hv; invert_clear Hv; reflexivity.
Qed.

Lemma bottom_of_MSeqA_le {M A} `{LessDefined A} (s : MSeqA M A) :
  bottom_of s `less_defined` s.
Proof. destruct s; repeat constructor. Qed.

(** *** 8b. The pivot demand approximates the pivot tuple *)

Lemma pivotNodeDmd_approx {M} {A B} `{Monoid M}
    `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (md : A -> M) (p : M -> bool) (b : M) (xs : MTuple M A) (xD : T B) :
  xD `is_approx` snd (lookupDigit md p b (tupleToDigit xs)) ->
  pivotNodeDmd md p b xs xD `less_defined` exact xs.
Proof.
  destruct xs as [c x y | c x y z]; unfold pivotNodeDmd, lookupDigit, tupleToDigit;
  [ destruct (p (b <+> md x))
  | destruct (p (b <+> md x)); [ | destruct (p (b <+> md x <+> md y)) ] ];
  cbn; intro Hx; repeat constructor; auto; reflexivity.
Qed.

(** [indexD] returns a [Thunk] demand on any non-empty input. *)
Lemma indexD_val_thunk {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M)
    (dflt : A) (p : M -> bool) (i : M) (t : MSeq M A) (xD : T B) :
  t <> MNil ->
  exists sD, Tick.val (indexD md dflt p i t xD) = Thunk sD.
Proof.
  destruct t as [|x|vm pr m sf]; intro Hne.
  - contradiction.
  - eexists; reflexivity.
  - unfold indexD; simpl.
    destruct (p (i <+> measureDigit md pr)); [eexists; reflexivity|].
    destruct (p (i <+> measureDigit md pr <+> vm)); eexists; reflexivity.
Qed.

(** *** The approximation lemma: the demand is a genuine approximation
    of the input tree (Lemma 5.5 shape, by [MSeq_ind_poly]). *)
Theorem indexD_approx {M} `{Monoid M} :
  forall (A : Type) (t : MSeq M A),
  forall (B : Type) (LDB : LessDefined B)
         (RLDB : Reflexive (less_defined (a := B))) (EAB : Exact A B)
         (md : A -> M) (dflt : A) (p : M -> bool) (i : M) (xD : T B),
    xD `is_approx` snd (lookupTree md dflt p i t) ->
    Tick.val (indexD md dflt p i t xD) `is_approx` t.
Proof.
  apply (MSeq_ind_poly (M := M)
    (fun A t =>
       forall (B : Type) (LDB : LessDefined B)
              (RLDB : Reflexive (less_defined (a := B))) (EAB : Exact A B)
              (md : A -> M) (dflt : A) (p : M -> bool) (i : M) (xD : T B),
         xD `is_approx` snd (lookupTree md dflt p i t) ->
         Tick.val (indexD md dflt p i t xD) `is_approx` t)).
  - (* MNil *)
    intros; constructor.
  - (* MUnit *)
    intros A x B LDB RLDB EAB md dflt p i xD Happrox.
    cbn in *. repeat constructor. exact Happrox.
  - (* MMore *)
    intros A vm pr m sf IH B LDB RLDB EAB md dflt p i xD Happrox.
    unfold indexD in *. cbn.
    destruct (p (i <+> measureDigit md pr)) eqn:Hp1;
      [ | destruct (p (i <+> measureDigit md pr <+> vm)) eqn:Hp2 ].
    + (* pivot in the front digit *)
      cbn. repeat constructor; reflexivity.
    + (* descend into the middle *)
      cbn.
      unfold lookupTree in Happrox; fold (@lookupTree M) in Happrox.
      rewrite Hp1, Hp2 in Happrox.
      unfold pivotDmd.
      destruct (lookupTree measureMTuple (MPair mzero dflt dflt) p
                  (i <+> measureDigit md pr) m) as [b xs] eqn:Hlk.
      repeat constructor; try reflexivity.
      specialize (IH (MTupleA M B) _ _ _
                    measureMTuple (MPair mzero dflt dflt) p
                    (i <+> measureDigit md pr)
                    (Thunk (pivotNodeDmd md p b xs xD))).
      unfold indexD in IH. rewrite Hlk in IH. cbn in IH.
      apply IH.
      constructor. apply pivotNodeDmd_approx. exact Happrox.
    + (* pivot in the rear digit *)
      cbn. repeat constructor; try reflexivity.
      apply bottom_of_MSeqA_le.
Qed.

(** *** 8c. The pruned clairvoyant lookup

    The clairvoyant translation of [lookupTree].  It avoids
    [deepLA]/[deepRA]/[viewLA] entirely — the index path never
    reconstructs — and carries one [tick] per visited tree node,
    matching [splitTreeD]'s accounting (the digit/measure helpers are
    tick-free).  [Core.M] is the clairvoyance monad ([M] names the
    measure monoid throughout this file).  The re-import puts [Core]'s
    [>>] back on top of [tick_scope]'s (the [fconsA'] pattern). *)

From Clairvoyance Require Import Core.

Definition tupleToDigitA {M A} (t : MTupleA M A) : DigitA A :=
  match t with
  | MPairA _ x y    => TwoA x y
  | MTripleA _ x y z => ThreeA x y z
  end.

(** Monadic digit measure: computing [md] of an element forces it (the
    generic reading; a measure such as the size monoid's [fun _ => 1]
    may force less). *)
Definition measureDigitA {M A} `{Monoid M} (mdA : A -> M) (d : DigitA A)
    : Core.M M :=
  match d with
  | OneA x => let! xv := force x in ret (mdA xv)
  | TwoA x y =>
      let! xv := force x in let! yv := force y in ret (mdA xv <+> mdA yv)
  | ThreeA x y z =>
      let! xv := force x in let! yv := force y in let! zv := force z in
      ret (mdA xv <+> mdA yv <+> mdA zv)
  end.

Definition lookupDigitA {M A} `{Monoid M} (mdA : A -> M)
    (p : M -> bool) (i : M) (d : DigitA A) : Core.M (M * T A) :=
  match d with
  | OneA x => ret (i, x)
  | TwoA x y =>
      let! xv := force x in
      if p (i <+> mdA xv) then ret (i, x) else ret (i <+> mdA xv, y)
  | ThreeA x y z =>
      let! xv := force x in
      if p (i <+> mdA xv) then ret (i, x)
      else
        let! yv := force y in
        if p (i <+> mdA xv <+> mdA yv) then ret (i <+> mdA xv, y)
        else ret (i <+> mdA xv <+> mdA yv, z)
  end.

Fixpoint lookupTreeA {M B} `{Monoid M} (mdB : B -> M)
    (p : M -> bool) (i : M) (t : MSeqA M B) {struct t} : Core.M (M * T B) :=
  tick >>
  match t with
  | MNilA    => ret (i, Undefined)      (* unreachable under the contract *)
  | MUnitA x => ret (i, x)
  | MMoreA vm prT mT sfT =>
      forcing prT (fun pr =>
      let! vd := measureDigitA mdB pr in
      let vpr := i <+> vd in
      if p vpr then lookupDigitA mdB p i pr
      else if p (vpr <+> vm) then
        let! r := forcing mT (fun m =>
                    lookupTreeA (B := MTupleA M B) measureMTupleA p vpr m) in
        let '(b, xsT) := r in
        forcing xsT (fun xs => lookupDigitA mdB p b (tupleToDigitA xs))
      else
        forcing sfT (fun sf => lookupDigitA mdB p (vpr <+> vm) sf))
  end.
Arguments lookupTreeA : simpl nomatch.

(** The clairvoyant random access: force the root, descend, return the
    pivot approximation. *)
Definition indexA {M B} `{Monoid M} (mdB : B -> M)
    (p : M -> bool) (i : M) (tA : T (MSeqA M B)) : Core.M (T B) :=
  let! r := forcing tA (fun t => lookupTreeA mdB p i t) in
  ret (snd r).

(** *** 8d. Helper specifications (tick-free, cost 0)

    [Hcoh] is the measure-coherence sandwich: on any value pinned to
    [exact x] from both sides, the approximation-side measure agrees
    with the pure one.  At spine levels it is discharged by
    [measureMTupleA_coh]; at the leaves the user supplies it (trivial
    for the size monoid, whose measure is constant). *)

#[local] Existing Instance Reflexive_LessDefined_T.
#[local] Existing Instance Transitive_LessDefined_T.

Lemma measureDigitA_exact_spec {M} {A B : Type} `{Monoid M}
    `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (md : A -> M) (mdB : B -> M)
    (HcohE : forall x : A, mdB (exact x) = md x)
    (d : Digit A) :
  measureDigitA mdB (exact d) [[ fun out cost =>
    out = measureDigit md d /\ cost <= 0 ]].
Proof.
  destruct d as [x|x y|x y z]; cbn; mgo_; rewrite ?HcohE; intuition lia.
Qed.

Lemma lookupDigitA_exact_spec {M} {A B : Type} `{Monoid M}
    `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (md : A -> M) (mdB : B -> M)
    (HcohE : forall x : A, mdB (exact x) = md x)
    (p : M -> bool) (b : M) (d : Digit A) (xD : T B) :
  xD `is_approx` snd (lookupDigit md p b d) ->
  lookupDigitA mdB p b (exact d) [[ fun out cost =>
    fst out = fst (lookupDigit md p b d)
    /\ xD `less_defined` snd out
    /\ snd out `less_defined` Thunk (exact (snd (lookupDigit md p b d)))
    /\ cost <= 0 ]].
Proof.
  destruct d as [x|x y|x y z]; intro Hx; cbn in *.
  - (* One *)
    apply optimistic_ret; cbn; intuition (try reflexivity; lia).
  - (* Two *)
    eapply optimistic_bind; eapply optimistic_ret.
    rewrite HcohE. destruct (p (b <+> md x)) eqn:Hp; cbn in Hx;
      apply optimistic_ret; cbn; intuition (try reflexivity; lia).
  - (* Three *)
    eapply optimistic_bind; eapply optimistic_ret.
    rewrite HcohE. destruct (p (b <+> md x)) eqn:Hp1.
    + cbn in Hx.
      apply optimistic_ret; cbn; intuition (try reflexivity; lia).
    + eapply optimistic_bind; eapply optimistic_ret.
      rewrite HcohE. destruct (p (b <+> md x <+> md y)) eqn:Hp2; cbn in Hx;
        apply optimistic_ret; cbn; intuition (try reflexivity; lia).
Qed.

(** Tiny inversion helpers for [T]-level [less_defined] facts (more
    robust than inversion patterns under substituted equations). *)
Lemma TThunk_inv {a} `{LessDefined a} (x : a) (t : T a) :
  Thunk x `less_defined` t -> exists y, t = Thunk y /\ x `less_defined` y.
Proof. intro Hl; inversion Hl; subst; eauto. Qed.

Lemma TThunkThunk_inv {a} `{LessDefined a} (x y : a) :
  Thunk x `less_defined` Thunk y -> x `less_defined` y.
Proof. intro Hl; inversion Hl; subst; auto. Qed.

(** The sandwich version, for the borrowed pivot tuple coming back from
    the recursive call: the executed value [v] is pinned between the
    pivot demand and [exact xs]. *)
Lemma lookupNodeA_spec {M} {A B : Type} `{Monoid M}
    `{LDB : LessDefined B, !Reflexive LDB, !Transitive LDB, Exact A B}
    (md : A -> M) (mdB : B -> M)
    (Hcoh : forall (x : A) (v : B),
        exact x `less_defined` v -> v `less_defined` exact x -> mdB v = md x)
    (p : M -> bool) (b : M) (xs : MTuple M A) (v : MTupleA M B) (xD : T B) :
  pivotNodeDmd md p b xs xD `less_defined` v ->
  v `less_defined` exact xs ->
  xD `is_approx` snd (lookupDigit md p b (tupleToDigit xs)) ->
  lookupDigitA mdB p b (tupleToDigitA v) [[ fun out cost =>
    fst out = fst (lookupDigit md p b (tupleToDigit xs))
    /\ xD `less_defined` snd out
    /\ snd out `less_defined` Thunk (exact (snd (lookupDigit md p b (tupleToDigit xs))))
    /\ cost <= 0 ]].
Proof.
  destruct xs as [c x y | c x y z]; intros Hlo Hup Hx;
    unfold pivotNodeDmd in Hlo; cbn in Hup, Hx |- *.
  - (* Pair *)
    invert_clear Hup as [ m' x1 x2 y1 y2 Hx1 Hy1 | ].
    destruct (p (b <+> md x)) eqn:Hp; cbn in Hx;
      invert_clear Hlo as [ ? ? ? ? ? Hx0 Hy0 | ];
      destruct (TThunk_inv Hx0) as (xv & -> & Hxv);
      pose proof (TThunkThunk_inv Hx1) as Hxv';
      cbn;
      (eapply optimistic_bind; eapply optimistic_ret);
      rewrite (Hcoh x xv Hxv Hxv'), Hp;
      apply optimistic_ret; cbn; intuition (try reflexivity; try lia).
    + (* pivot = x: xD below the returned slot *)
      etransitivity; [exact Hx|]. constructor. exact Hxv.
  - (* Triple *)
    invert_clear Hup as [ | m' x1 x2 y1 y2 z1 z2 Hx1 Hy1 Hz1 ].
    destruct (p (b <+> md x)) eqn:Hp1.
    + (* pivot = x *)
      cbn in Hx.
      invert_clear Hlo as [ | ? ? ? ? ? ? ? Hx0 Hy0 Hz0 ].
      destruct (TThunk_inv Hx0) as (xv & -> & Hxv).
      pose proof (TThunkThunk_inv Hx1) as Hxv'.
      cbn. eapply optimistic_bind; eapply optimistic_ret.
      rewrite (Hcoh x xv Hxv Hxv'), Hp1.
      apply optimistic_ret; cbn; intuition (try reflexivity; try lia).
      etransitivity; [exact Hx|]. constructor. exact Hxv.
    + (* pivot = y or z: the first two slots are forced *)
      destruct (p (b <+> md x <+> md y)) eqn:Hp2; cbn in Hx;
        invert_clear Hlo as [ | ? ? ? ? ? ? ? Hx0 Hy0 Hz0 ];
        destruct (TThunk_inv Hx0) as (xv & -> & Hxv);
        pose proof (TThunkThunk_inv Hx1) as Hxv';
        destruct (TThunk_inv Hy0) as (yv & -> & Hyv);
        pose proof (TThunkThunk_inv Hy1) as Hyv';
        cbn;
        (eapply optimistic_bind; eapply optimistic_ret);
        rewrite (Hcoh x xv Hxv Hxv'), Hp1;
        (eapply optimistic_bind; eapply optimistic_ret);
        rewrite (Hcoh y yv Hyv Hyv'), Hp2;
        apply optimistic_ret; cbn; intuition (try reflexivity; try lia).
      (* pivot = y: xD below the returned slot *)
      etransitivity; [exact Hx|]. constructor. exact Hyv.
Qed.

(** Keep the helper calls folded in the workhorse proof below — their
    specs above are the only interface needed. *)
Arguments measureDigitA : simpl never.
Arguments lookupDigitA : simpl never.

(** *** 8e. The specification (Lemma 5.6 shape)

    Lockstep unfolding of [lookupTreeA] (on the demand returned by
    [indexD]) against the pure [lookupTree]: the strengthened payload
    carries (i) the accumulated prefix measure, exactly; (ii) the
    demanded pivot from below; (iii) [exact] of the pure pivot from
    above (the sandwich that pins cached measures); and (iv) the cost
    against [indexD]'s budget. *)
Lemma lookupTreeA_spec {M} `{Monoid M} :
  forall (A : Type) (t : MSeq M A),
  forall (B : Type) (LDB : LessDefined B)
         (RLDB : Reflexive (less_defined (a := B)))
         (TLDB : Transitive (less_defined (a := B)))
         (EAB : Exact A B)
         (md : A -> M) (mdB : B -> M) (dflt : A) (p : M -> bool)
         (i : M) (xD : T B),
    (forall (x : A) (v : B),
        exact x `less_defined` v -> v `less_defined` exact x -> mdB v = md x) ->
    mseq_valid t ->
    xD `is_approx` snd (lookupTree md dflt p i t) ->
    forall sD, Tick.val (indexD md dflt p i t xD) = Thunk sD ->
      lookupTreeA mdB p i sD [[ fun out cost =>
        fst out = fst (lookupTree md dflt p i t)
        /\ xD `less_defined` snd out
        /\ snd out `less_defined` Thunk (exact (snd (lookupTree md dflt p i t)))
        /\ cost <= Tick.cost (indexD md dflt p i t xD) ]].
Proof.
  apply (MSeq_ind_poly (M := M)
    (fun A t =>
       forall (B : Type) (LDB : LessDefined B)
              (RLDB : Reflexive (less_defined (a := B)))
              (TLDB : Transitive (less_defined (a := B)))
              (EAB : Exact A B)
              (md : A -> M) (mdB : B -> M) (dflt : A) (p : M -> bool)
              (i : M) (xD : T B),
         (forall (x : A) (v : B),
             exact x `less_defined` v -> v `less_defined` exact x -> mdB v = md x) ->
         mseq_valid t ->
         xD `is_approx` snd (lookupTree md dflt p i t) ->
         forall sD, Tick.val (indexD md dflt p i t xD) = Thunk sD ->
           lookupTreeA mdB p i sD [[ fun out cost =>
             fst out = fst (lookupTree md dflt p i t)
             /\ xD `less_defined` snd out
             /\ snd out `less_defined` Thunk (exact (snd (lookupTree md dflt p i t)))
             /\ cost <= Tick.cost (indexD md dflt p i t xD) ]])).
  - (* MNil: indexD demands nothing, no Thunk to run on *)
    intros A B LDB RLDB TLDB EAB md mdB dflt p i xD Hcoh Hval Hx sD HsD.
    cbn in HsD. discriminate.
  - (* MUnit *)
    intros A x B LDB RLDB TLDB EAB md mdB dflt p i xD Hcoh Hval Hx sD HsD.
    cbn in HsD, Hx. injection HsD as HsD. subst sD.
    cbn. eapply optimistic_bind. eapply optimistic_tick.
    apply optimistic_ret. cbn. intuition (try reflexivity; lia).
  - (* MMore *)
    intros A vm pr m sf IH B LDB RLDB TLDB EAB md mdB dflt p i xD Hcoh Hval Hx sD HsD.
    destruct Hval as [Hvm Hvalm].
    assert (HcohE : forall x : A, mdB (exact x) = md x)
      by (intros; apply Hcoh; reflexivity).
    unfold indexD in HsD. cbn in HsD, Hx |- *.
    destruct (p (i <+> measureDigit md pr)) eqn:Hp1;
      [ | destruct (p (i <+> measureDigit md pr <+> vm)) eqn:Hp2 ].
    + (* pivot in the front digit *)
      injection HsD as HsD. subst sD.
      cbn. eapply optimistic_bind. eapply optimistic_tick.
      eapply optimistic_bind.
      eapply optimistic_mon; [ eapply measureDigitA_exact_spec; exact HcohE | ].
      intros vd n [Hvd Hn]. subst vd.
      rewrite Hp1.
      eapply optimistic_mon; [ eapply lookupDigitA_exact_spec; eauto | ].
      intros out c (Hf & Hlo & Hup & Hc).
      repeat (split; try assumption). lia.
    + (* descend into the middle *)
      assert (Hm : m <> MNil).
      { intro Hmnil. subst m. cbn in Hvm. subst vm.
        rewrite madd_zero_r in Hp2. congruence. }
      destruct (indexD_val_thunk measureMTuple (MPair mzero dflt dflt) p
                  (i <+> measureDigit md pr)
                  (pivotDmd md dflt p (i <+> measureDigit md pr) m xD)
                  Hm) as [sD' HsD'].
      unfold indexD in HsD'.
      assert (HsD2 : Thunk sD = Thunk (MMoreA vm (exact pr) (Thunk sD') (exact sf))).
      { rewrite <- HsD. rewrite <- HsD'. reflexivity. }
      injection HsD2 as HsD2. subst sD.
      destruct (lookupTree measureMTuple (MPair mzero dflt dflt) p
                  (i <+> measureDigit md pr) m) as [b xs] eqn:Hlk.
      cbn in Hx.
      assert (Hcoh' : forall (x : MTuple M A) (v : MTupleA M B),
                 exact x `less_defined` v -> v `less_defined` exact x ->
                 measureMTupleA v = measureMTuple x)
        by (intros ? ? _ Hup'; eapply measureMTupleA_coh; eauto).
      assert (Hx' : pivotDmd md dflt p (i <+> measureDigit md pr) m xD
                      `is_approx`
                    snd (lookupTree measureMTuple (MPair mzero dflt dflt) p
                           (i <+> measureDigit md pr) m)).
      { unfold pivotDmd. rewrite Hlk. cbn.
        constructor. apply pivotNodeDmd_approx. exact Hx. }
      specialize (IH (MTupleA M B) _ _ _ _
                    measureMTuple measureMTupleA (MPair mzero dflt dflt) p
                    (i <+> measureDigit md pr)
                    (pivotDmd md dflt p (i <+> measureDigit md pr) m xD)
                    Hcoh' Hvalm Hx' sD' HsD').
      cbn. eapply optimistic_bind. eapply optimistic_tick.
      eapply optimistic_bind.
      eapply optimistic_mon; [ eapply measureDigitA_exact_spec; exact HcohE | ].
      intros vd n [Hvd Hn]. subst vd.
      rewrite Hp1, Hp2.
      eapply optimistic_bind.
      eapply optimistic_mon; [ exact IH | ].
      intros r n' (Hf' & Hlo' & Hup' & Hc').
      destruct r as [b' xsT].
      rewrite Hlk in Hf', Hup'. cbn in Hf', Hup'. subst b'.
      unfold pivotDmd in Hlo'. rewrite Hlk in Hlo'. cbn in Hlo'.
      destruct (TThunk_inv Hlo') as (v & -> & Hv).
      pose proof (TThunkThunk_inv Hup') as Hv'.
      cbn.
      eapply optimistic_mon;
        [ eapply lookupNodeA_spec; [ exact Hcoh | exact Hv | exact Hv' | exact Hx ] | ].
      intros out c (Hf'' & Hlo'' & Hup'' & Hc'').
      repeat (split; try assumption).
      unfold indexD in Hc'. lia.
    + (* pivot in the rear digit *)
      injection HsD as HsD. subst sD.
      cbn. eapply optimistic_bind. eapply optimistic_tick.
      eapply optimistic_bind.
      eapply optimistic_mon; [ eapply measureDigitA_exact_spec; exact HcohE | ].
      intros vd n [Hvd Hn]. subst vd.
      rewrite Hp1, Hp2.
      eapply optimistic_mon; [ eapply lookupDigitA_exact_spec; eauto | ].
      intros out c (Hf & Hlo & Hup & Hc).
      repeat (split; try assumption). lia.
Qed.

(** The headline specification: running the clairvoyant lookup on the
    demand [indexD] returns produces (at least) the demanded pivot,
    within [indexD]'s cost.  [t <> MNil] is implied by the split
    contract [p i = false /\ p (i <+> measureSeq md t) = true] (the
    measure of [MNil] is [mzero]). *)
Theorem indexD_spec {M} `{Monoid M} {A B : Type}
    `{LDB : LessDefined B, !Reflexive LDB, !Transitive LDB, Exact A B}
    (md : A -> M) (mdB : B -> M) (dflt : A) (p : M -> bool) (i : M)
    (t : MSeq M A) (xD : T B) :
  (forall (x : A) (v : B),
      exact x `less_defined` v -> v `less_defined` exact x -> mdB v = md x) ->
  mseq_valid t ->
  t <> MNil ->
  xD `is_approx` snd (lookupTree md dflt p i t) ->
  forall sD, sD = Tick.val (indexD md dflt p i t xD) ->
    indexA mdB p i sD [[ fun out cost =>
      xD `less_defined` out
      /\ cost <= Tick.cost (indexD md dflt p i t xD) ]].
Proof.
  intros Hcoh Hval Hne Hx sD HsD.
  destruct (indexD_val_thunk md dflt p i xD Hne) as [sD' HsD'].
  subst sD. rewrite HsD'.
  unfold indexA.
  eapply optimistic_bind.
  eapply optimistic_forcing; [ reflexivity | ].
  eapply optimistic_mon;
    [ eapply lookupTreeA_spec;
      [ assumption | assumption | exact Hcoh | exact Hval | exact Hx | exact HsD' ] | ].
  intros out c (Hf & Hlo & Hup & Hc).
  apply optimistic_ret. cbn. intuition lia.
Qed.

(** Random access at the size monoid: demand-correct AND O(log n) —
    the [index] counterpart of [index_O_log_n]. *)
Corollary index_spec {A : Type}
    `{LDA : LessDefined A, !Reflexive LDA, !Transitive LDA}
    (dflt : A) (i : nat) (t : MSeq nat A) (xD : T A) :
  mseq_valid t ->
  t <> MNil ->
  xD `is_approx` index dflt i t ->
  forall sD, sD = Tick.val (indexD (B := A) sz1 dflt (fun s => i <? s) 0 t xD) ->
    indexA (B := A) sz1 (fun s => i <? s) 0 sD [[ fun out cost =>
      xD `less_defined` out
      /\ cost <= split_c1 * Nat.log2 (size t) + split_c2 ]].
Proof.
  intros Hval Hne Hx sD HsD.
  eapply optimistic_mon.
  - eapply indexD_spec; [ | exact Hval | exact Hne | exact Hx | exact HsD ].
    intros; reflexivity.
  - intros out c [Hlo Hc]. split; [ exact Hlo | ].
    pose proof (index_O_log_n sz1 dflt (fun s => i <? s) 0 xD Hne) as Hlog.
    lia.
Qed.

(* ================================================================= *)
(** ** Section 9: The faithful split demand function (Item 4 / M9b)    *)
(* ================================================================= *)

(** The scaffold [splitTreeD] (Section 5) passes [(⊥, pivotDmd …, ⊥)] to
    its recursive call: reconstruction below the top level is never
    demanded, so its cost bound — while honest and [outD]-independent —
    bounds a demand function that does not model the pure [splitTree]'s
    per-level reconstruction (SPLIT_NOTE §7).  This section defines the
    *faithful* demand function [splitTreeD_f] ALONGSIDE the scaffold
    (coexist, don't replace — every Section 5–8 result is untouched):
    the caller's demands on the two result halves are unbundled through
    [deepLD_f]/[deepRD_f] (and, when a residual digit is empty, through
    the cascades [viewLD_f]/[viewRD_f]) into genuine demands on the
    recursive halves, threaded through the recursive call together with
    the pivot demand.

    Demand conventions (as established in Sections 5 and 8):
    - computing [md x] of a leaf element demands [x] in full
      ([Thunk (exact x)]); at spine levels the measure is the cached
      [measureMTuple], which demands only the tuple's root constructor
      (the measure field is strict) — the *skeleton* demands below;
    - digits at spine nodes visited by the descent are demanded at
      [exact] (the descent computes [vpr], measuring the front digit in
      full; the rear digit is over-demanded for uniformity with the
      scaffold);
    - building [mdeep pr m sf] computes the cache [‖m‖], which reads
      [m]'s root, its digit roots, and the cached measures of those
      digits' tuples: the skeleton [mseqSkel m]. *)

(** *** 9a. Skeleton demands (what a cache computation forces) *)

Definition mtupleSkel {M A B} (t : MTuple M A) : MTupleA M B :=
  match t with
  | MPair c _ _     => MPairA c Undefined Undefined
  | MTriple c _ _ _ => MTripleA c Undefined Undefined Undefined
  end.

Definition digitSkel {M A B} (d : Digit (MTuple M A)) : DigitA (MTupleA M B) :=
  match d with
  | One x       => OneA (Thunk (mtupleSkel x))
  | Two x y     => TwoA (Thunk (mtupleSkel x)) (Thunk (mtupleSkel y))
  | Three x y z =>
      ThreeA (Thunk (mtupleSkel x)) (Thunk (mtupleSkel y)) (Thunk (mtupleSkel z))
  end.

Definition mseqSkel {M A B} (m : MSeq M (MTuple M A)) : MSeqA M (MTupleA M B) :=
  match m with
  | MNil             => MNilA
  | MUnit x          => MUnitA (Thunk (mtupleSkel x))
  | MMore vm pr _ sf => MMoreA vm (Thunk (digitSkel pr)) Undefined (Thunk (digitSkel sf))
  end.

(** Merge a skeleton into a caller demand.  The merge is shallow (root,
    digit roots, tuple roots): a [Thunk] tuple demand already contains
    its strict cache field, so nothing deeper is ever needed — this is
    why no general [Lub] instance is required. *)

Definition addTupleSkel {M A B} (x : MTuple M A) (xD : T (MTupleA M B))
    : T (MTupleA M B) :=
  match xD with
  | Undefined => Thunk (mtupleSkel x)
  | Thunk v   => Thunk v
  end.

Definition addDigitSkel {M A B} (d : Digit (MTuple M A))
    (dD : T (DigitA (MTupleA M B))) : T (DigitA (MTupleA M B)) :=
  match dD with
  | Undefined => Thunk (digitSkel d)
  | Thunk dd  =>
      Thunk (match d, dd with
             | One x, OneA xD => OneA (addTupleSkel x xD)
             | Two x y, TwoA xD yD => TwoA (addTupleSkel x xD) (addTupleSkel y yD)
             | Three x y z, ThreeA xD yD zD =>
                 ThreeA (addTupleSkel x xD) (addTupleSkel y yD) (addTupleSkel z zD)
             | _, _ => dd                      (* shape mismatch: unreachable *)
             end)
  end.

Definition addSkel {M A B} (m : MSeq M (MTuple M A))
    (mD : T (MSeqA M (MTupleA M B))) : T (MSeqA M (MTupleA M B)) :=
  match mD with
  | Undefined => Thunk (mseqSkel m)
  | Thunk s   =>
      Thunk (match m, s with
             | MUnit x, MUnitA xD => MUnitA (addTupleSkel x xD)
             | MMore _ pr _ sf, MMoreA vm prD mD' sfD =>
                 MMoreA vm (addDigitSkel pr prD) mD' (addDigitSkel sf sfD)
             | _, _ => s                       (* shape mismatch: unreachable *)
             end)
  end.

(** *** 9b. Demand reassembly (output shapes back onto input shapes) *)

(** Demand on a borrowed tuple from the demand on the digit its contents
    became ([tupleToDigit t1] as the near digit of an [mdeep]-built
    node).  [tupleToDigit] forces the tuple's root, so the demand is at
    least the skeleton even when the digit demand is [⊥]. *)
Definition tupleDmdOfDigitDmd {M A B} (t1 : MTuple M A) (dD : T (DigitA B))
    : T (MTupleA M B) :=
  match t1, dD with
  | MPair c _ _,     Thunk (TwoA aD bD)      => Thunk (MPairA c aD bD)
  | MTriple c _ _ _, Thunk (ThreeA aD bD cD) => Thunk (MTripleA c aD bD cD)
  | _, _ => Thunk (mtupleSkel t1)
  end.

(** Demand on a digit [d] from the demand on [toTree md (digitToList d)]
    (the empty-middle rebuild of [deepL]/[deepR]).  [toTree]'s nodes
    have [MNil] middles, so their caches force nothing; only the element
    slots carry demand. *)
Definition toTreeDmd {M A B} (d : Digit A) (tD : T (MSeqA M B)) : T (DigitA B) :=
  match d, tD with
  | _, Undefined => Undefined
  | One _,   Thunk (MUnitA aD) => Thunk (OneA aD)
  | Two _ _, Thunk (MMoreA _ prD _ sfD) =>
      Thunk (TwoA (match prD with Thunk (OneA aD) => aD | _ => Undefined end)
                  (match sfD with Thunk (OneA bD) => bD | _ => Undefined end))
  | Three _ _ _, Thunk (MMoreA _ prD _ sfD) =>
      Thunk (ThreeA (match prD with Thunk (TwoA aD _) => aD | _ => Undefined end)
                    (match prD with Thunk (TwoA _ bD) => bD | _ => Undefined end)
                    (match sfD with Thunk (OneA cD) => cD | _ => Undefined end))
  | _, _ => Undefined                          (* shape mismatch: unreachable *)
  end.

(** Unbundle a demand on the borrow-built node
    [mdeep md (tupleToDigit t1) m' sf] (the empty-residual case of
    [deepL]) into demands on the borrowed tuple [t1], the remaining
    middle [m'] (which the node's cache forces to its skeleton), and the
    suffix [sf].  [borrowDmdR] is the mirrored unbundling for
    [mdeep md pr m' (tupleToDigit t1)]. *)
Definition borrowDmdL {M A B} (t1 : MTuple M A) (m' : MSeq M (MTuple M A))
    (outD : T (MSeqA M B))
    : T (MTupleA M B) * T (MSeqA M (MTupleA M B)) * T (DigitA B) :=
  match outD with
  | Thunk (MMoreA _ prD mD sfD) =>
      (tupleDmdOfDigitDmd t1 prD, addSkel m' mD, sfD)
  | Thunk _ =>                                 (* shape mismatch: unreachable *)
      (Thunk (mtupleSkel t1), Thunk (mseqSkel m'), Undefined)
  | Undefined => (Undefined, Undefined, Undefined)
  end.

Definition borrowDmdR {M A B} (m' : MSeq M (MTuple M A)) (t1 : MTuple M A)
    (outD : T (MSeqA M B))
    : T (DigitA B) * T (MSeqA M (MTupleA M B)) * T (MTupleA M B) :=
  match outD with
  | Thunk (MMoreA _ prD mD sfD) =>
      (prD, addSkel m' mD, tupleDmdOfDigitDmd t1 sfD)
  | Thunk _ =>                                 (* shape mismatch: unreachable *)
      (Undefined, Thunk (mseqSkel m'), Thunk (mtupleSkel t1))
  | Undefined => (Undefined, Undefined, Undefined)
  end.

(** *** 9c. The faithful view demands (the cascades)

    [viewLD_f dflt t xD tD]: demand of one [viewL] step — [xD] the
    demand on the uncons'd element, [tD] the demand on the remaining
    tree; returns the demand on the input tree.  One [Tick.tick] per
    visited node, recursing into the middle on a [One] front, so the
    cost is governed by [lvc] exactly as the scaffold [viewLD]'s.  The
    non-[One] fronts rebuild in place via [mdeep], whose cache forces
    the skeleton of the (unchanged) middle whenever the rebuilt node
    itself is demanded. *)
Fixpoint viewLD_f {M} {A B} `{Monoid M} (dflt : A)
    (t : MSeq M A) (xD : T B) (tD : T (MSeqA M B)) {struct t}
    : Tick (T (MSeqA M B)) :=
  let+ _ := Tick.tick in
  match t with
  | MNil    => Tick.ret (Thunk MNilA)
  | MUnit _ => Tick.ret (Thunk (MUnitA xD))
  | MMore vm pr m sf =>
      match pr with
      | Two _ _ =>
          match tD with
          | Thunk (MMoreA _ prD mD sfD) =>
              let yD := match prD with Thunk (OneA yD) => yD | _ => Undefined end in
              Tick.ret (Thunk (MMoreA vm (Thunk (TwoA xD yD)) (addSkel m mD) sfD))
          | _ =>
              Tick.ret (Thunk (MMoreA vm (Thunk (TwoA xD Undefined))
                                       Undefined Undefined))
          end
      | Three _ _ _ =>
          match tD with
          | Thunk (MMoreA _ prD mD sfD) =>
              let '(yD, zD) := match prD with
                               | Thunk (TwoA yD zD) => (yD, zD)
                               | _ => (Undefined, Undefined)
                               end in
              Tick.ret (Thunk (MMoreA vm (Thunk (ThreeA xD yD zD)) (addSkel m mD) sfD))
          | _ =>
              Tick.ret (Thunk (MMoreA vm (Thunk (ThreeA xD Undefined Undefined))
                                       Undefined Undefined))
          end
      | One _ =>
          match viewL measureMTuple (MPair mzero dflt dflt) m with
          | None =>
              (* m = MNil: the rest is [toTree md (digitToList sf)] *)
              let+ mD := viewLD_f (B := MTupleA M B)
                           (MPair mzero dflt dflt) m Undefined Undefined in
              Tick.ret (Thunk (MMoreA vm (Thunk (OneA xD)) mD (toTreeDmd sf tD)))
          | Some (t1, m') =>
              let '(t1D, m'D, sfD) := borrowDmdL t1 m' tD in
              let+ mD := viewLD_f (MPair mzero dflt dflt) m t1D m'D in
              Tick.ret (Thunk (MMoreA vm (Thunk (OneA xD)) mD sfD))
          end
      end
  end.

Fixpoint viewRD_f {M} {A B} `{Monoid M} (dflt : A)
    (t : MSeq M A) (xD : T B) (tD : T (MSeqA M B)) {struct t}
    : Tick (T (MSeqA M B)) :=
  let+ _ := Tick.tick in
  match t with
  | MNil    => Tick.ret (Thunk MNilA)
  | MUnit _ => Tick.ret (Thunk (MUnitA xD))
  | MMore vm pr m sf =>
      match sf with
      | Two _ _ =>
          (* viewR _ = Some (mdeep md pr m (One x), y) *)
          match tD with
          | Thunk (MMoreA _ prD mD sfD) =>
              let xD0 := match sfD with Thunk (OneA xD0) => xD0 | _ => Undefined end in
              Tick.ret (Thunk (MMoreA vm prD (addSkel m mD) (Thunk (TwoA xD0 xD))))
          | _ =>
              Tick.ret (Thunk (MMoreA vm Undefined Undefined
                                       (Thunk (TwoA Undefined xD))))
          end
      | Three _ _ _ =>
          (* viewR _ = Some (mdeep md pr m (Two x y), z) *)
          match tD with
          | Thunk (MMoreA _ prD mD sfD) =>
              let '(xD0, yD0) := match sfD with
                                 | Thunk (TwoA xD0 yD0) => (xD0, yD0)
                                 | _ => (Undefined, Undefined)
                                 end in
              Tick.ret (Thunk (MMoreA vm prD (addSkel m mD)
                                       (Thunk (ThreeA xD0 yD0 xD))))
          | _ =>
              Tick.ret (Thunk (MMoreA vm Undefined Undefined
                                       (Thunk (ThreeA Undefined Undefined xD))))
          end
      | One _ =>
          match viewR measureMTuple (MPair mzero dflt dflt) m with
          | None =>
              let+ mD := viewRD_f (B := MTupleA M B)
                           (MPair mzero dflt dflt) m Undefined Undefined in
              Tick.ret (Thunk (MMoreA vm (toTreeDmd pr tD) mD (Thunk (OneA xD))))
          | Some (m', t1) =>
              let '(prD, m'D, t1D) := borrowDmdR m' t1 tD in
              let+ mD := viewRD_f (MPair mzero dflt dflt) m t1D m'D in
              Tick.ret (Thunk (MMoreA vm prD mD (Thunk (OneA xD))))
          end
      end
  end.

(** *** 9d. The faithful reconstruction demands

    [deepLD_f dflt r m sf outD]: unbundle the demand on
    [deepL md dflt r m sf] into demands on the residual elements [r],
    the middle [m], and the suffix [sf].  Cost 0 when [outD = ⊥] (the
    half was not demanded) or when the residual refills the near digit
    directly; one [viewLD_f] cascade when the residual is empty. *)
Definition deepLD_f {M} {A B} `{Monoid M} (dflt : A)
    (r : list A) (m : MSeq M (MTuple M A)) (sf : Digit A) (outD : T (MSeqA M B))
    : Tick (list (T B) * T (MSeqA M (MTupleA M B)) * T (DigitA B)) :=
  match outD with
  | Undefined => Tick.ret ([], Undefined, Undefined)
  | Thunk out =>
      match r with
      | [x] =>
          match out with
          | MMoreA _ prD mD sfD =>
              let xD := match prD with Thunk (OneA xD) => xD | _ => Undefined end in
              Tick.ret ([xD], addSkel m mD, sfD)
          | _ => Tick.ret ([Undefined], Thunk (mseqSkel m), Undefined)
          end
      | [x; y] =>
          match out with
          | MMoreA _ prD mD sfD =>
              let '(xD, yD) := match prD with
                               | Thunk (TwoA xD yD) => (xD, yD)
                               | _ => (Undefined, Undefined)
                               end in
              Tick.ret ([xD; yD], addSkel m mD, sfD)
          | _ => Tick.ret ([Undefined; Undefined], Thunk (mseqSkel m), Undefined)
          end
      | [x; y; z] =>
          match out with
          | MMoreA _ prD mD sfD =>
              let '(xD, yD, zD) := match prD with
                                   | Thunk (ThreeA xD yD zD) => (xD, yD, zD)
                                   | _ => (Undefined, Undefined, Undefined)
                                   end in
              Tick.ret ([xD; yD; zD], addSkel m mD, sfD)
          | _ => Tick.ret ([Undefined; Undefined; Undefined],
                           Thunk (mseqSkel m), Undefined)
          end
      | [] =>
          match viewL measureMTuple (MPair mzero dflt dflt) m with
          | None =>
              let+ mD := viewLD_f (B := MTupleA M B)
                           (MPair mzero dflt dflt) m Undefined Undefined in
              Tick.ret ([], mD, toTreeDmd sf outD)
          | Some (t1, m') =>
              let '(t1D, m'D, sfD) := borrowDmdL t1 m' outD in
              let+ mD := viewLD_f (MPair mzero dflt dflt) m t1D m'D in
              Tick.ret ([], mD, sfD)
          end
      | _ => Tick.ret ([], Undefined, Undefined) (* |r| ≥ 4: deepL = MNil *)
      end
  end.

Definition deepRD_f {M} {A B} `{Monoid M} (dflt : A)
    (pr : Digit A) (m : MSeq M (MTuple M A)) (l : list A) (outD : T (MSeqA M B))
    : Tick (T (DigitA B) * T (MSeqA M (MTupleA M B)) * list (T B)) :=
  match outD with
  | Undefined => Tick.ret (Undefined, Undefined, [])
  | Thunk out =>
      match l with
      | [x] =>
          match out with
          | MMoreA _ prD mD sfD =>
              let xD := match sfD with Thunk (OneA xD) => xD | _ => Undefined end in
              Tick.ret (prD, addSkel m mD, [xD])
          | _ => Tick.ret (Undefined, Thunk (mseqSkel m), [Undefined])
          end
      | [x; y] =>
          match out with
          | MMoreA _ prD mD sfD =>
              let '(xD, yD) := match sfD with
                               | Thunk (TwoA xD yD) => (xD, yD)
                               | _ => (Undefined, Undefined)
                               end in
              Tick.ret (prD, addSkel m mD, [xD; yD])
          | _ => Tick.ret (Undefined, Thunk (mseqSkel m), [Undefined; Undefined])
          end
      | [x; y; z] =>
          match out with
          | MMoreA _ prD mD sfD =>
              let '(xD, yD, zD) := match sfD with
                                   | Thunk (ThreeA xD yD zD) => (xD, yD, zD)
                                   | _ => (Undefined, Undefined, Undefined)
                                   end in
              Tick.ret (prD, addSkel m mD, [xD; yD; zD])
          | _ => Tick.ret (Undefined, Thunk (mseqSkel m),
                           [Undefined; Undefined; Undefined])
          end
      | [] =>
          match viewR measureMTuple (MPair mzero dflt dflt) m with
          | None =>
              let+ mD := viewRD_f (B := MTupleA M B)
                           (MPair mzero dflt dflt) m Undefined Undefined in
              Tick.ret (toTreeDmd pr outD, mD, [])
          | Some (m', t1) =>
              let '(prD, m'D, t1D) := borrowDmdR m' t1 outD in
              let+ mD := viewRD_f (MPair mzero dflt dflt) m t1D m'D in
              Tick.ret (prD, mD, [])
          end
      | _ => Tick.ret (Undefined, Undefined, []) (* |l| ≥ 4: deepR = MNil *)
      end
  end.

(** *** 9e. The faithful pivot demand and [splitTreeD_f]

    [pivotNodeDmd_f] is [pivotNodeDmd] (Section 5) with the slots
    *beyond* the pivot — the elements that become the near digit of the
    right half — carrying the demands unbundled from the right half
    ([rEl], the first component of [deepLD_f]'s result) instead of [⊥].
    The slots before the pivot stay [exact]: the scan measured them. *)
Definition pivotNodeDmd_f {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M)
    (p : M -> bool) (b : M) (xs : MTuple M A) (xD : T B) (rEl : list (T B))
    : MTupleA M B :=
  let r0 := nth 0 rEl Undefined in
  let r1 := nth 1 rEl Undefined in
  match xs with
  | MPair c x y =>
      if p (b <+> md x)
      then MPairA c (Thunk (exact x)) r0
      else MPairA c (Thunk (exact x)) xD
  | MTriple c x y z =>
      if p (b <+> md x)
      then MTripleA c (Thunk (exact x)) r0 r1
      else if p (b <+> md x <+> md y)
      then MTripleA c (Thunk (exact x)) (Thunk (exact y)) r0
      else MTripleA c (Thunk (exact x)) (Thunk (exact y)) xD
  end.
Arguments pivotNodeDmd_f : simpl never.

(** The faithful demand function.  Branch structure and per-level tick
    follow the scaffold [splitTreeD]; the difference is entirely in the
    value demands: the recursive call receives the unbundled half-demands
    [(mlD, xsD, mrD)] instead of [(⊥, pivotDmd …, ⊥)], and the returned
    middle demand is the recursive result instead of a constant.  Note
    [mlD] always contains [mseqSkel ml]: locating the pivot inside the
    borrowed tuple computes [vpr <+> ‖ml‖] — the chain that makes the
    pivot-projection non-demand-isolated (Section 2b) — and here it is
    finally accounted for. *)
Fixpoint splitTreeD_f {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (p : M -> bool) (i : M) (t : MSeq M A) (outD : SplitDmd M B) {struct t}
    : Tick (T (MSeqA M B)) :=
  let+ _ := Tick.tick in
  match t with
  | MNil    => Tick.ret Undefined
  | MUnit x => let '(_, xD, _) := outD in Tick.ret (Thunk (MUnitA xD))
  | MMore vm pr m sf =>
      let '(lD, xD, rD) := outD in
      let vpr  := i <+> measureDigit md pr in
      let vm_t := vpr <+> vm in
      if p vpr then
        let '(_, _, r) := splitDigit md p i pr in
        let+ _  := toTreeD lD in
        let+ dl := deepLD_f dflt r m sf rD in
        let '(_, mD, _) := dl in
        Tick.ret (Thunk (MMoreA vm (exact pr) mD (exact sf)))
      else if p vm_t then
        let '(ml, xs, mr) :=
          splitTree measureMTuple (MPair mzero dflt dflt) p vpr m in
        let b := vpr <+> measureSeq measureMTuple ml in
        let '(l, _, r) := splitDigit md p b (tupleToDigit xs) in
        let+ dr := deepRD_f dflt pr ml l lD in
        let '(_, mlD0, _) := dr in
        let+ dl := deepLD_f dflt r mr sf rD in
        let '(rEl, mrD, _) := dl in
        let xsD := Thunk (pivotNodeDmd_f md p b xs xD rEl) in
        let mlD := addSkel ml mlD0 in
        let+ mD := splitTreeD_f (A := MTuple M A) (B := MTupleA M B)
                     measureMTuple (MPair mzero dflt dflt) p vpr m
                     (mlD, xsD, mrD) in
        Tick.ret (Thunk (MMoreA vm (exact pr) mD (exact sf)))
      else
        let '(l, _, _) := splitDigit md p vm_t sf in
        let+ dr := deepRD_f dflt pr m l lD in
        let '(_, mD, _) := dr in
        let+ _  := toTreeD rD in
        Tick.ret (Thunk (MMoreA vm (exact pr) mD (exact sf)))
  end.

(* ================================================================= *)
(** ** Section 10: Faithful split cost — the §C.2 telescoping (M7)      *)
(* ================================================================= *)

(** The naive per-level accounting gives O(depth²): each level may pay a
    [viewRD_f] cascade on its left half and a [viewLD_f] cascade on its
    right half, each up to [depth] ticks.  The pen-and-paper argument
    (thesis §C.2) telescopes: [deepL]/[deepR] always refill the near
    digit to size ≥ 2 unless the residual was a single element, so the
    view chains of successive levels are disjoint.  Mechanised the same
    way Theorem 5.7 absorbs the cascade: bake the chain potential
    [rvc l + lvc r] of the *result halves* into the induction
    hypothesis.  The per-level facts are [deepLD_f_cost_lvc] /
    [deepRD_f_cost_rvc]: reconstruction cost plus the result's chain
    potential is bounded by the input chain potential plus a constant —
    the credit the IH supplies at the recursive level is exactly what
    the cascade at this level spends. *)

Definition split_f_c1 : nat := 5.
Definition split_f_c2 : nat := 3.

(** *** Cascade cost (same statement as the scaffold's [viewLD_cost]). *)

Lemma viewLD_f_cost {M} `{Monoid M} :
  forall (A B : Type) (dflt : A) (t : MSeq M A) (xD : T B) (tD : T (MSeqA M B)),
    Tick.cost (viewLD_f dflt t xD tD) <= lvc t.
Proof.
  fix SELF 4.
  intros A B dflt t xD tD.
  destruct t as [|x|vm pr m sf].
  - simpl; lia.
  - simpl; lia.
  - destruct pr as [a|a b|a b c].
    + simpl.
      destruct (viewL measureMTuple (MPair mzero dflt dflt) m)
        as [ [t1 m']|] eqn:Hv.
      * destruct (borrowDmdL t1 m' tD) as [ [t1D m'D] sfD].
        specialize (SELF (MTuple M A) (MTupleA M B) (MPair mzero dflt dflt)
                      m t1D m'D).
        simpl Tick.cost; lia.
      * specialize (SELF (MTuple M A) (MTupleA M B) (MPair mzero dflt dflt)
                      m Undefined Undefined).
        simpl Tick.cost; lia.
    + destruct tD as [s|]; [destruct s as [|xT|vm' prD mD sfD]|]; simpl; lia.
    + destruct tD as [s|]; [destruct s as [|xT|vm' prD mD sfD]|]; simpl; try lia.
      destruct prD as [d|]; [destruct d|]; simpl; lia.
Qed.

Lemma viewRD_f_cost {M} `{Monoid M} :
  forall (A B : Type) (dflt : A) (t : MSeq M A) (xD : T B) (tD : T (MSeqA M B)),
    Tick.cost (viewRD_f dflt t xD tD) <= rvc t.
Proof.
  fix SELF 4.
  intros A B dflt t xD tD.
  destruct t as [|x|vm pr m sf].
  - simpl; lia.
  - simpl; lia.
  - destruct sf as [a|a b|a b c].
    + simpl.
      destruct (viewR measureMTuple (MPair mzero dflt dflt) m)
        as [ [m' t1]|] eqn:Hv.
      * destruct (borrowDmdR m' t1 tD) as [ [prD m'D] t1D].
        specialize (SELF (MTuple M A) (MTupleA M B) (MPair mzero dflt dflt)
                      m t1D m'D).
        simpl Tick.cost; lia.
      * specialize (SELF (MTuple M A) (MTupleA M B) (MPair mzero dflt dflt)
                      m Undefined Undefined).
        simpl Tick.cost; lia.
    + destruct tD as [s|]; [destruct s as [|xT|vm' prD mD sfD]|]; simpl; lia.
    + destruct tD as [s|]; [destruct s as [|xT|vm' prD mD sfD]|]; simpl; try lia.
      destruct sfD as [d|]; [destruct d|]; simpl; lia.
Qed.

(** *** Pure chain-potential facts. *)

Lemma lvc_pos {M A} (s : MSeq M A) : 1 <= lvc s.
Proof.
  destruct s as [|?|? pr ? ?]; [simpl;lia|simpl;lia|destruct pr; simpl; lia].
Qed.

Lemma rvc_pos {M A} (s : MSeq M A) : 1 <= rvc s.
Proof.
  destruct s as [|?|? ? ? sf]; [simpl;lia|simpl;lia|destruct sf; simpl; lia].
Qed.

Lemma lvc_toTree {M A} `{Monoid M} (md : A -> M) (xs : list A) :
  lvc (toTree md xs) <= 2.
Proof.
  destruct xs as [|x [|y [|z [|w ws] ] ] ]; simpl; lia.
Qed.

Lemma rvc_toTree {M A} `{Monoid M} (md : A -> M) (xs : list A) :
  rvc (toTree md xs) <= 2.
Proof.
  destruct xs as [|x [|y [|z [|w ws] ] ] ]; simpl; lia.
Qed.

(** [viewL]/[viewR] return [None] only on the empty tree. *)

Lemma viewL_None {M A} `{Monoid M} (md : A -> M) (dflt : A) (t : MSeq M A) :
  viewL md dflt t = None -> t = MNil.
Proof.
  destruct t as [|x|vm pr m sf]; simpl; intro Hv.
  - reflexivity.
  - discriminate Hv.
  - destruct pr as [a|a b|a b c];
      [ destruct (viewL measureMTuple (MPair mzero dflt dflt) m)
          as [ [t1 m']|] | | ]; discriminate Hv.
Qed.

Lemma viewR_None {M A} `{Monoid M} (md : A -> M) (dflt : A) (t : MSeq M A) :
  viewR md dflt t = None -> t = MNil.
Proof.
  destruct t as [|x|vm pr m sf]; simpl; intro Hv.
  - reflexivity.
  - discriminate Hv.
  - destruct sf as [a|a b|a b c];
      [ destruct (viewR measureMTuple (MPair mzero dflt dflt) m)
          as [ [m' t1]|] | | ]; discriminate Hv.
Qed.

(** *** The per-level telescoping facts: reconstruction cost plus the
    rebuilt half's chain potential is bounded by the original middle's
    chain potential plus 2.  The three residual shapes are §C.2's
    E/O/M types: empty (pay the cascade, the refilled digit has size
    ≥ 2 so the result chain resets); one element (pay nothing, the
    chain grows by 1 — the credit carries); two or three elements (pay
    nothing, the chain resets). *)

Lemma deepLD_f_cost_lvc {M} {A B} `{Monoid M} (md : A -> M) (dflt : A)
    (r : list A) (m : MSeq M (MTuple M A)) (sf : Digit A)
    (outD : T (MSeqA M B)) :
  Tick.cost (deepLD_f dflt r m sf outD) + lvc (deepL md dflt r m sf)
    <= lvc m + 2.
Proof.
  unfold deepLD_f, deepL.
  destruct outD as [out|].
  - destruct r as [|x [|y [|z [|w ws] ] ] ].
    + (* empty residual: the cascade *)
      destruct (viewL measureMTuple (MPair mzero dflt dflt) m)
        as [ [t1 m']|] eqn:Hv.
      * destruct (borrowDmdL t1 m' (Thunk out)) as [ [t1D m'D] sfD].
        pose proof (viewLD_f_cost (MPair mzero dflt dflt) m t1D m'D) as Hc.
        destruct t1; simpl Tick.cost; simpl lvc; lia.
      * (* viewL = None ⇒ m = MNil *)
        apply viewL_None in Hv. subst m.
        pose proof (lvc_toTree md (digitToList sf)) as Ht.
        simpl; lia.
    + destruct out; simpl; pose proof (lvc_pos m); lia.
    + destruct out as [|xT|vm' prD mD sfD]; simpl;
        try (pose proof (lvc_pos m); lia).
      destruct prD as [d|]; [destruct d|]; simpl;
        pose proof (lvc_pos m); lia.
    + destruct out as [|xT|vm' prD mD sfD]; simpl;
        try (pose proof (lvc_pos m); lia).
      destruct prD as [d|]; [destruct d|]; simpl;
        pose proof (lvc_pos m); lia.
    + simpl; pose proof (lvc_pos m); lia.
  - destruct r as [|x [|y [|z [|w ws] ] ] ].
    + destruct (viewL measureMTuple (MPair mzero dflt dflt) m)
        as [ [t1 m']|] eqn:Hv.
      * destruct t1; simpl; pose proof (lvc_pos m); lia.
      * apply viewL_None in Hv. subst m.
        pose proof (lvc_toTree md (digitToList sf)) as Ht. simpl; lia.
    + simpl; pose proof (lvc_pos m); lia.
    + simpl; pose proof (lvc_pos m); lia.
    + simpl; pose proof (lvc_pos m); lia.
    + simpl; pose proof (lvc_pos m); lia.
Qed.

Lemma deepRD_f_cost_rvc {M} {A B} `{Monoid M} (md : A -> M) (dflt : A)
    (pr : Digit A) (m : MSeq M (MTuple M A)) (l : list A)
    (outD : T (MSeqA M B)) :
  Tick.cost (deepRD_f dflt pr m l outD) + rvc (deepR md dflt pr m l)
    <= rvc m + 2.
Proof.
  unfold deepRD_f, deepR.
  destruct outD as [out|].
  - destruct l as [|x [|y [|z [|w ws] ] ] ].
    + destruct (viewR measureMTuple (MPair mzero dflt dflt) m)
        as [ [m' t1]|] eqn:Hv.
      * destruct (borrowDmdR m' t1 (Thunk out)) as [ [prD m'D] t1D].
        pose proof (viewRD_f_cost (MPair mzero dflt dflt) m t1D m'D) as Hc.
        destruct t1; simpl Tick.cost; simpl rvc; lia.
      * apply viewR_None in Hv. subst m.
        pose proof (rvc_toTree md (digitToList pr)) as Ht.
        simpl; lia.
    + destruct out; simpl; pose proof (rvc_pos m); lia.
    + destruct out as [|xT|vm' prD mD sfD]; simpl;
        try (pose proof (rvc_pos m); lia).
      destruct sfD as [d|]; [destruct d|]; simpl;
        pose proof (rvc_pos m); lia.
    + destruct out as [|xT|vm' prD mD sfD]; simpl;
        try (pose proof (rvc_pos m); lia).
      destruct sfD as [d|]; [destruct d|]; simpl;
        pose proof (rvc_pos m); lia.
    + simpl; pose proof (rvc_pos m); lia.
  - destruct l as [|x [|y [|z [|w ws] ] ] ].
    + destruct (viewR measureMTuple (MPair mzero dflt dflt) m)
        as [ [m' t1]|] eqn:Hv.
      * destruct t1; simpl; pose proof (rvc_pos m); lia.
      * apply viewR_None in Hv. subst m.
        pose proof (rvc_toTree md (digitToList pr)) as Ht. simpl; lia.
    + simpl; pose proof (rvc_pos m); lia.
    + simpl; pose proof (rvc_pos m); lia.
    + simpl; pose proof (rvc_pos m); lia.
    + simpl; pose proof (rvc_pos m); lia.
Qed.

(** *** Approximation facts for the faithful demand machinery (4c).
    Helper-level lemmas live here, BEFORE the [simpl never] directives
    below, so their proofs may still unfold the subjects; the main
    [splitTreeD_f_approx] (Section 11) sees everything folded and uses
    only these interfaces. *)

Lemma mtupleSkel_approx {M A B} `{LessDefined B} `{Exact A B}
    (t : MTuple M A) :
  mtupleSkel (B := B) t `less_defined` exact t.
Proof. destruct t; cbn; repeat constructor. Qed.

Lemma digitSkel_approx {M A B} `{LessDefined B} `{Exact A B}
    (d : Digit (MTuple M A)) :
  digitSkel (B := B) d `less_defined` exact d.
Proof.
  destruct d; cbn; repeat constructor; apply mtupleSkel_approx.
Qed.

Lemma mseqSkel_approx {M A B} `{LessDefined B} `{Exact A B}
    (m : MSeq M (MTuple M A)) :
  mseqSkel (B := B) m `less_defined` exact m.
Proof.
  destruct m; cbn; repeat constructor;
    first [ apply mtupleSkel_approx | apply digitSkel_approx ].
Qed.

Lemma addTupleSkel_approx {M A B} `{LessDefined B} `{Exact A B}
    (x : MTuple M A) (xD : T (MTupleA M B)) :
  xD `less_defined` exact x ->
  addTupleSkel x xD `less_defined` exact x.
Proof.
  intro Hx. destruct xD as [v|]; cbn.
  - exact Hx.
  - constructor. apply mtupleSkel_approx.
Qed.

Lemma addDigitSkel_approx {M A B} `{LessDefined B} `{Exact A B}
    (d : Digit (MTuple M A)) (dD : T (DigitA (MTupleA M B))) :
  dD `less_defined` exact d ->
  addDigitSkel d dD `less_defined` exact d.
Proof.
  intro Hd. destruct dD as [dd|]; cbn.
  - apply TThunkThunk_inv in Hd.
    destruct d as [x|x y|x y z]; invert_clear Hd; cbn;
      repeat constructor; apply addTupleSkel_approx; assumption.
  - constructor. apply digitSkel_approx.
Qed.

Lemma addSkel_approx {M A B} `{LessDefined B} `{Exact A B}
    (m : MSeq M (MTuple M A)) (mD : T (MSeqA M (MTupleA M B))) :
  mD `less_defined` exact m ->
  addSkel m mD `less_defined` exact m.
Proof.
  intro Hm. destruct mD as [sm|]; cbn.
  - apply TThunkThunk_inv in Hm.
    destruct m as [|x|vm pr mm sf]; invert_clear Hm; cbn;
      repeat constructor;
      first [ apply addTupleSkel_approx; assumption
            | apply addDigitSkel_approx; assumption
            | assumption ].
  - constructor. apply mseqSkel_approx.
Qed.

Lemma tupleDmdOfDigitDmd_approx {M A B} `{LessDefined B} `{Exact A B}
    (t1 : MTuple M A) (dD : T (DigitA B)) :
  dD `less_defined` exact (tupleToDigit t1) ->
  tupleDmdOfDigitDmd t1 dD `less_defined` exact t1.
Proof.
  intro Hd. destruct dD as [dd|].
  - apply TThunkThunk_inv in Hd.
    destruct t1 as [c x y|c x y z]; cbn in Hd |- *; invert_clear Hd;
      repeat constructor; assumption.
  - destruct t1; cbn; repeat constructor.
Qed.

Lemma toTreeDmd_approx {M A B} `{Monoid M} `{LessDefined B} `{Exact A B}
    (md : A -> M) (d : Digit A) (tD : T (MSeqA M B)) :
  tD `less_defined` exact (toTree md (digitToList d)) ->
  toTreeDmd d tD `less_defined` exact d.
Proof.
  intro Ht. destruct tD as [st|]; cbn; [|destruct d; constructor].
  apply TThunkThunk_inv in Ht.
  destruct d as [a|a b|a b c]; cbn in Ht |- *.
  - (* One: toTree = MUnit a *)
    invert_clear Ht as [ | aD aE HaD | ].
    repeat constructor; assumption.
  - (* Two: toTree = MMore _ (One a) MNil (One b) *)
    invert_clear Ht as [ | | vm0 prD f2 mD0 m2 sfD r2 Hpr Hsf' Hsf ].
    destruct prD as [dd1|];
      [ apply TThunkThunk_inv in Hpr; invert_clear Hpr | ];
      (destruct sfD as [dd2|];
        [ apply TThunkThunk_inv in Hsf; invert_clear Hsf | ]);
      cbn; repeat constructor; try assumption.
  - (* Three: toTree = MMore _ (Two a b) MNil (One c) *)
    invert_clear Ht as [ | | vm0 prD f2 mD0 m2 sfD r2 Hpr Hsf' Hsf ].
    destruct prD as [dd1|];
      [ apply TThunkThunk_inv in Hpr; invert_clear Hpr | ];
      (destruct sfD as [dd2|];
        [ apply TThunkThunk_inv in Hsf; invert_clear Hsf | ]);
      cbn; repeat constructor; try assumption.
Qed.

Lemma borrowDmdL_approx {M} {A B} `{Monoid M} `{LessDefined B} `{Exact A B}
    (md : A -> M) (t1 : MTuple M A) (m' : MSeq M (MTuple M A)) (sf : Digit A)
    (outD : T (MSeqA M B)) (t1D : T (MTupleA M B))
    (m'D : T (MSeqA M (MTupleA M B))) (sfD : T (DigitA B)) :
  borrowDmdL t1 m' outD = (t1D, m'D, sfD) ->
  outD `less_defined` exact (mdeep md (tupleToDigit t1) m' sf) ->
  t1D `less_defined` exact t1
  /\ m'D `less_defined` exact m'
  /\ sfD `less_defined` exact sf.
Proof.
  intros Hb Ho. destruct outD as [out|].
  - apply TThunkThunk_inv in Ho. unfold mdeep in Ho. cbn in Ho.
    invert_clear Ho. cbn in Hb.
    injection Hb as ? ? ?; subst.
    split; [|split].
    + apply tupleDmdOfDigitDmd_approx; assumption.
    + apply addSkel_approx; assumption.
    + assumption.
  - cbn in Hb. injection Hb as ? ? ?; subst.
    repeat constructor.
Qed.

Lemma borrowDmdR_approx {M} {A B} `{Monoid M} `{LessDefined B} `{Exact A B}
    (md : A -> M) (pr : Digit A) (m' : MSeq M (MTuple M A)) (t1 : MTuple M A)
    (outD : T (MSeqA M B)) (prD : T (DigitA B))
    (m'D : T (MSeqA M (MTupleA M B))) (t1D : T (MTupleA M B)) :
  borrowDmdR m' t1 outD = (prD, m'D, t1D) ->
  outD `less_defined` exact (mdeep md pr m' (tupleToDigit t1)) ->
  prD `less_defined` exact pr
  /\ m'D `less_defined` exact m'
  /\ t1D `less_defined` exact t1.
Proof.
  intros Hb Ho. destruct outD as [out|].
  - apply TThunkThunk_inv in Ho. unfold mdeep in Ho. cbn in Ho.
    invert_clear Ho. cbn in Hb.
    injection Hb as ? ? ?; subst.
    split; [|split].
    + assumption.
    + apply addSkel_approx; assumption.
    + apply tupleDmdOfDigitDmd_approx; assumption.
  - cbn in Hb. injection Hb as ? ? ?; subst.
    repeat constructor.
Qed.

(** The cascades return approximations of their input trees. *)
Lemma viewLD_f_approx {M} `{Monoid M} :
  forall (A : Type) (t : MSeq M A),
  forall (B : Type) (LDB : LessDefined B)
         (RLDB : Reflexive (less_defined (a := B))) (EAB : Exact A B)
         (md : A -> M) (dflt : A) (x0 : A) (t' : MSeq M A)
         (xD : T B) (tD : T (MSeqA M B)),
    viewL md dflt t = Some (x0, t') ->
    xD `is_approx` x0 ->
    tD `is_approx` t' ->
    Tick.val (viewLD_f dflt t xD tD) `is_approx` t.
Proof.
  apply (MSeq_ind_poly (M := M)
    (fun A t =>
       forall (B : Type) (LDB : LessDefined B)
              (RLDB : Reflexive (less_defined (a := B))) (EAB : Exact A B)
              (md : A -> M) (dflt : A) (x0 : A) (t' : MSeq M A)
              (xD : T B) (tD : T (MSeqA M B)),
         viewL md dflt t = Some (x0, t') ->
         xD `is_approx` x0 ->
         tD `is_approx` t' ->
         Tick.val (viewLD_f dflt t xD tD) `is_approx` t)).
  - (* MNil *)
    intros A B LDB RLDB EAB md dflt x0 t' xD tD Hv Hx Ht.
    discriminate Hv.
  - (* MUnit *)
    intros A x B LDB RLDB EAB md dflt x0 t' xD tD Hv Hx Ht.
    cbn in Hv. injection Hv as ? ?; subst.
    cbn. repeat constructor. exact Hx.
  - (* MMore *)
    intros A vm pr m sf IH B LDB RLDB EAB md dflt x0 t' xD tD Hv Hx Ht.
    destruct pr as [a|a b|a b c].
    + (* One: the cascade *)
      cbn in Hv. cbn.
      destruct (viewL measureMTuple (MPair mzero dflt dflt) m)
        as [ [t1 m'']|] eqn:Hv2.
      * injection Hv as ? ?; subst.
        destruct (borrowDmdL t1 m'' tD) as [ [t1D m'D] sfD] eqn:Hb.
        pose proof (borrowDmdL_approx Hb Ht)
          as (Ht1 & Hm' & Hsf).
        cbn. repeat constructor; [ exact Hx | | exact Hsf ].
        eapply (IH (MTupleA M B) _ _ _
                  measureMTuple (MPair mzero dflt dflt) t1 m'');
          eassumption.
      * (* viewL m = None: m = MNil *)
        apply viewL_None in Hv2. subst m.
        injection Hv as ? ?; subst.
        cbn. repeat constructor; [ exact Hx | ].
        apply toTreeDmd_approx with (md := md). exact Ht.
    + (* Two *)
      cbn in Hv. injection Hv as ? ?; subst.
      destruct tD as [st|].
      * apply TThunkThunk_inv in Ht.
        invert_clear Ht as [ | | vm0 prD prE mD0 mE sfD sfE Hpr Hm Hsf ].
        destruct prD as [dd|];
          [ apply TThunkThunk_inv in Hpr; invert_clear Hpr | ];
          cbn; repeat constructor;
          first [ exact Hx
                | apply addSkel_approx; assumption
                | assumption ].
      * cbn. repeat constructor. exact Hx.
    + (* Three *)
      cbn in Hv. injection Hv as ? ?; subst.
      destruct tD as [st|].
      * apply TThunkThunk_inv in Ht.
        invert_clear Ht as [ | | vm0 prD prE mD0 mE sfD sfE Hpr Hm Hsf ].
        destruct prD as [dd|];
          [ apply TThunkThunk_inv in Hpr; invert_clear Hpr | ];
          cbn; repeat constructor;
          first [ exact Hx
                | apply addSkel_approx; assumption
                | assumption ].
      * cbn. repeat constructor. exact Hx.
Qed.

Lemma viewRD_f_approx {M} `{Monoid M} :
  forall (A : Type) (t : MSeq M A),
  forall (B : Type) (LDB : LessDefined B)
         (RLDB : Reflexive (less_defined (a := B))) (EAB : Exact A B)
         (md : A -> M) (dflt : A) (x0 : A) (t' : MSeq M A)
         (xD : T B) (tD : T (MSeqA M B)),
    viewR md dflt t = Some (t', x0) ->
    xD `is_approx` x0 ->
    tD `is_approx` t' ->
    Tick.val (viewRD_f dflt t xD tD) `is_approx` t.
Proof.
  apply (MSeq_ind_poly (M := M)
    (fun A t =>
       forall (B : Type) (LDB : LessDefined B)
              (RLDB : Reflexive (less_defined (a := B))) (EAB : Exact A B)
              (md : A -> M) (dflt : A) (x0 : A) (t' : MSeq M A)
              (xD : T B) (tD : T (MSeqA M B)),
         viewR md dflt t = Some (t', x0) ->
         xD `is_approx` x0 ->
         tD `is_approx` t' ->
         Tick.val (viewRD_f dflt t xD tD) `is_approx` t)).
  - intros A B LDB RLDB EAB md dflt x0 t' xD tD Hv Hx Ht.
    discriminate Hv.
  - intros A x B LDB RLDB EAB md dflt x0 t' xD tD Hv Hx Ht.
    cbn in Hv. injection Hv as ? ?; subst.
    cbn. repeat constructor. exact Hx.
  - intros A vm pr m sf IH B LDB RLDB EAB md dflt x0 t' xD tD Hv Hx Ht.
    destruct sf as [a|a b|a b c].
    + (* One: the cascade *)
      cbn in Hv. cbn.
      destruct (viewR measureMTuple (MPair mzero dflt dflt) m)
        as [ [m'' t1]|] eqn:Hv2.
      * injection Hv as ? ?; subst.
        destruct (borrowDmdR m'' t1 tD) as [ [prD m'D] t1D] eqn:Hb.
        pose proof (borrowDmdR_approx Hb Ht)
          as (Hpr & Hm' & Ht1).
        cbn. repeat constructor; [ exact Hpr | | exact Hx ].
        eapply (IH (MTupleA M B) _ _ _
                  measureMTuple (MPair mzero dflt dflt) t1 m'');
          eassumption.
      * apply viewR_None in Hv2. subst m.
        injection Hv as ? ?; subst.
        cbn. repeat constructor; [ | exact Hx ].
        apply toTreeDmd_approx with (md := md). exact Ht.
    + (* Two *)
      cbn in Hv. injection Hv as ? ?; subst.
      destruct tD as [st|].
      * apply TThunkThunk_inv in Ht.
        invert_clear Ht as [ | | vm0 prD prE mD0 mE sfD sfE Hpr Hm Hsf ].
        destruct sfD as [dd|];
          [ apply TThunkThunk_inv in Hsf; invert_clear Hsf | ];
          cbn; repeat constructor;
          first [ exact Hx
                | apply addSkel_approx; assumption
                | assumption ].
      * cbn. repeat constructor. exact Hx.
    + (* Three *)
      cbn in Hv. injection Hv as ? ?; subst.
      destruct tD as [st|].
      * apply TThunkThunk_inv in Ht.
        invert_clear Ht as [ | | vm0 prD prE mD0 mE sfD sfE Hpr Hm Hsf ].
        destruct sfD as [dd|];
          [ apply TThunkThunk_inv in Hsf; invert_clear Hsf | ];
          cbn; repeat constructor;
          first [ exact Hx
                | apply addSkel_approx; assumption
                | assumption ].
      * cbn. repeat constructor. exact Hx.
Qed.

(** Unbundling lemmas for the reconstruction demands: only the facts the
    main induction consumes (the middle demand, and for [deepLD_f] the
    slot demands on the residual elements). *)
Lemma deepLD_f_approx {M} {A B} `{Monoid M}
    `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (md : A -> M) (dflt : A) (r : list A) (m : MSeq M (MTuple M A))
    (sf : Digit A) (outD : T (MSeqA M B))
    (rEl : list (T B)) (mD : T (MSeqA M (MTupleA M B))) (sfD : T (DigitA B)) :
  Tick.val (deepLD_f dflt r m sf outD) = (rEl, mD, sfD) ->
  outD `is_approx` deepL md dflt r m sf ->
  (forall k, nth k rEl Undefined `less_defined` exact (nth k r dflt))
  /\ mD `less_defined` exact m.
Proof.
  intros Hval Ho.
  destruct outD as [out|]; cbn in Hval.
  - destruct r as [|x [|y [|z [|w ws] ] ] ].
    + (* empty residual *)
      cbn in Ho.
      destruct (viewL measureMTuple (MPair mzero dflt dflt) m)
        as [ [t1 m']|] eqn:Hv.
      * apply TThunkThunk_inv in Ho.
        invert_clear Ho as [ | | vm0 prD prE mD0 mE sfD0 sfE Hpr Hm Hsf ].
        cbn in Hval. injection Hval as ? ? ?; subst.
        split; [ intro k; destruct k; cbn; constructor | ].
        eapply viewLD_f_approx;
          [ typeclasses eauto
          | exact Hv
          | apply tupleDmdOfDigitDmd_approx; exact Hpr
          | apply addSkel_approx; exact Hm ].
      * apply viewL_None in Hv. subst m.
        cbn in Hval. injection Hval as ? ? ?; subst.
        split; [ intro k; destruct k; cbn; constructor | ].
        cbn. repeat constructor.
    + (* [x] *)
      apply TThunkThunk_inv in Ho.
      invert_clear Ho as [ | | vm0 prD prE mD0 mE sfD0 sfE Hpr Hm Hsf ].
      cbn in Hval. injection Hval as ? ? ?; subst.
      split; [ | apply addSkel_approx; exact Hm ].
      intro k.
      destruct prD as [dd|];
        [ apply TThunkThunk_inv in Hpr; invert_clear Hpr | ];
        destruct k as [|k]; cbn; try constructor; try assumption;
        destruct k; cbn; constructor.
    + (* [x; y] *)
      apply TThunkThunk_inv in Ho.
      invert_clear Ho as [ | | vm0 prD prE mD0 mE sfD0 sfE Hpr Hm Hsf ].
      destruct prD as [dd|];
        [ apply TThunkThunk_inv in Hpr; invert_clear Hpr | ];
        cbn in Hval; injection Hval as ? ? ?; subst;
        (split; [ | apply addSkel_approx; exact Hm ]);
        intro k;
        destruct k as [|k]; cbn; try constructor; try assumption;
        destruct k as [|k]; cbn; try constructor; try assumption;
        destruct k; cbn; constructor.
    + (* [x; y; z] *)
      apply TThunkThunk_inv in Ho.
      invert_clear Ho as [ | | vm0 prD prE mD0 mE sfD0 sfE Hpr Hm Hsf ].
      destruct prD as [dd|];
        [ apply TThunkThunk_inv in Hpr; invert_clear Hpr | ];
        cbn in Hval; injection Hval as ? ? ?; subst;
        (split; [ | apply addSkel_approx; exact Hm ]);
        intro k;
        destruct k as [|k]; cbn; try constructor; try assumption;
        destruct k as [|k]; cbn; try constructor; try assumption;
        destruct k as [|k]; cbn; try constructor; try assumption;
        destruct k; cbn; constructor.
    + (* |r| >= 4 *)
      injection Hval as ? ? ?; subst.
      split; [ intro k; destruct k; cbn; constructor | constructor ].
  - injection Hval as ? ? ?; subst.
    split; [ intro k; destruct k; cbn; constructor | constructor ].
Qed.

Lemma deepRD_f_approx {M} {A B} `{Monoid M}
    `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (md : A -> M) (dflt : A) (pr : Digit A) (m : MSeq M (MTuple M A))
    (l : list A) (outD : T (MSeqA M B))
    (prD : T (DigitA B)) (mD : T (MSeqA M (MTupleA M B))) (lEl : list (T B)) :
  Tick.val (deepRD_f dflt pr m l outD) = (prD, mD, lEl) ->
  outD `is_approx` deepR md dflt pr m l ->
  mD `less_defined` exact m.
Proof.
  intros Hval Ho.
  destruct outD as [out|]; cbn in Hval.
  - destruct l as [|x [|y [|z [|w ws] ] ] ].
    + cbn in Ho.
      destruct (viewR measureMTuple (MPair mzero dflt dflt) m)
        as [ [m' t1]|] eqn:Hv.
      * apply TThunkThunk_inv in Ho.
        invert_clear Ho as [ | | vm0 prD0 prE mD0 mE sfD0 sfE Hpr Hm Hsf ].
        cbn in Hval. injection Hval as ? ? ?; subst.
        eapply viewRD_f_approx;
          [ typeclasses eauto
          | exact Hv
          | apply tupleDmdOfDigitDmd_approx; exact Hsf
          | apply addSkel_approx; exact Hm ].
      * apply viewR_None in Hv. subst m.
        cbn in Hval. injection Hval as ? ? ?; subst.
        cbn. repeat constructor.
    + apply TThunkThunk_inv in Ho.
      invert_clear Ho as [ | | vm0 prD0 prE mD0 mE sfD0 sfE Hpr Hm Hsf ].
      cbn in Hval. injection Hval as ? ? ?; subst.
      apply addSkel_approx; exact Hm.
    + apply TThunkThunk_inv in Ho.
      invert_clear Ho as [ | | vm0 prD0 prE mD0 mE sfD0 sfE Hpr Hm Hsf ].
      destruct sfD0 as [dd|];
        [ apply TThunkThunk_inv in Hsf; invert_clear Hsf | ];
        cbn in Hval; injection Hval as ? ? ?; subst;
        apply addSkel_approx; exact Hm.
    + apply TThunkThunk_inv in Ho.
      invert_clear Ho as [ | | vm0 prD0 prE mD0 mE sfD0 sfE Hpr Hm Hsf ].
      destruct sfD0 as [dd|];
        [ apply TThunkThunk_inv in Hsf; invert_clear Hsf | ];
        cbn in Hval; injection Hval as ? ? ?; subst;
        apply addSkel_approx; exact Hm.
    + injection Hval as ? ? ?; subst. constructor.
  - injection Hval as ? ? ?; subst. constructor.
Qed.

(** The faithful pivot demand approximates the pivot tuple. *)
Lemma pivotNodeDmd_f_approx {M} {A B} `{Monoid M}
    `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (md : A -> M) (p : M -> bool) (b : M) (xs : MTuple M A)
    (xD : T B) (rEl : list (T B)) (dflt : A)
    (l1 : list A) (x1 : A) (r1 : list A) :
  splitDigit md p b (tupleToDigit xs) = (l1, x1, r1) ->
  xD `is_approx` x1 ->
  (forall k, nth k rEl Undefined `less_defined` exact (nth k r1 dflt)) ->
  pivotNodeDmd_f md p b xs xD rEl `less_defined` exact xs.
Proof.
  destruct xs as [c x y | c x y z];
    unfold pivotNodeDmd_f, splitDigit, tupleToDigit;
    [ destruct (p (b <+> md x)) eqn:Hp1
    | destruct (p (b <+> md x)) eqn:Hp1;
      [ | destruct (p (b <+> md x <+> md y)) eqn:Hp2 ] ];
    intros Hsd Hx Hr; injection Hsd as ? ? ?; subst; cbn in Hx |- *.
  - (* Pair, pivot = x, r1 = [y] *)
    pose proof (Hr 0) as Hr0; cbn in Hr0.
    repeat constructor; [ reflexivity | exact Hr0 ].
  - (* Pair, pivot = y *)
    repeat constructor; [ reflexivity | exact Hx ].
  - (* Triple, pivot = x, r1 = [y; z] *)
    pose proof (Hr 0) as Hr0; pose proof (Hr 1) as Hr1; cbn in Hr0, Hr1.
    repeat constructor; [ reflexivity | exact Hr0 | exact Hr1 ].
  - (* Triple, pivot = y, r1 = [z] *)
    pose proof (Hr 0) as Hr0; cbn in Hr0.
    repeat constructor; [ reflexivity | reflexivity | exact Hr0 ].
  - (* Triple, pivot = z *)
    repeat constructor; [ reflexivity | reflexivity | exact Hx ].
Qed.

(** Keep the helper calls folded from here on: their cost lemmas above
    are the only interface the main induction needs. *)
Arguments viewLD_f : simpl never.
Arguments viewRD_f : simpl never.
Arguments deepLD_f : simpl never.
Arguments deepRD_f : simpl never.

(** Keep the pure helpers folded too: the main induction reasons about
    them only through the lemmas above and the [eqn:] equations. *)
Arguments splitDigit : simpl never.
Arguments deepL : simpl never.
Arguments deepR : simpl never.
Arguments toTree : simpl never.
Arguments viewL : simpl never.
Arguments viewR : simpl never.
Arguments measureDigit : simpl never.
Arguments measureSeq : simpl never.

(** *** M7+M9b — the telescoping bound.  The IH carries the chain
    potential of the pure result halves; at each level the
    [deepLD_f]/[deepRD_f] facts trade the credit supplied by the
    recursive call ([rvc ml + lvc mr]) for this level's cascade cost
    plus the credit owed upward ([rvc l + lvc r]). *)
Theorem splitTreeD_f_cost_pot {M} `{Monoid M} :
  forall (A B : Type) (EAB : Exact A B) (md : A -> M) (dflt : A)
         (p : M -> bool) (i : M) (t : MSeq M A) (outD : SplitDmd M B)
         (l : MSeq M A) (x : A) (r : MSeq M A),
    splitTree md dflt p i t = (l, x, r) ->
    Tick.cost (splitTreeD_f md dflt p i t outD) + rvc l + lvc r
    <= split_f_c1 * depth t + split_f_c2.
Proof.
  fix SELF 8.
  intros A B EAB md dflt p i t outD l x r Hsp.
  destruct t as [|x0|vm pr m sf].
  - simpl in Hsp. injection Hsp as ? ? ?; subst.
    destruct outD as [ [lD xD] rD]; simpl;
      unfold split_f_c1, split_f_c2; lia.
  - simpl in Hsp. injection Hsp as ? ? ?; subst.
    destruct outD as [ [lD xD] rD]; simpl;
      unfold split_f_c1, split_f_c2; lia.
  - destruct outD as [ [lD xD] rD].
    simpl in Hsp. simpl depth. simpl.
    destruct (p (i <+> measureDigit md pr)) eqn:Hp1.
    + (* branch 1: pivot in the front digit *)
      destruct (splitDigit md p i pr) as [ [l1 x1] r1] eqn:Hsd.
      injection Hsp as ? ? ?; subst.
      pose proof (toTreeD_cost lD) as Ht.
      pose proof (deepLD_f_cost_lvc (B := B) md dflt r1 m sf rD) as HdL.
      pose proof (rvc_toTree md l1) as Hrt.
      pose proof (lvc_le_depth m) as Hlm.
      simpl Tick.cost.
      destruct (Tick.val (deepLD_f (B := B) dflt r1 m sf rD))
        as [ [rEl mD1] sfD1].
      simpl Tick.cost.
      unfold split_f_c1, split_f_c2; lia.
    + destruct (p (i <+> measureDigit md pr <+> vm)) eqn:Hp2.
      * (* branch 2: descend into the middle *)
        destruct (splitTree measureMTuple (MPair mzero dflt dflt) p
                    (i <+> measureDigit md pr) m)
          as [ [ml xs] mr] eqn:Hst.
        destruct (splitDigit md p
                    (i <+> measureDigit md pr <+> measureSeq measureMTuple ml)
                    (tupleToDigit xs))
          as [ [l1 x1] r1] eqn:Hsd.
        injection Hsp as ? ? ?; subst.
        pose proof (deepRD_f_cost_rvc (B := B) md dflt pr ml l1 lD) as HdR.
        pose proof (deepLD_f_cost_lvc (B := B) md dflt r1 mr sf rD) as HdL.
        simpl Tick.cost.
        destruct (Tick.val (deepRD_f (B := B) dflt pr ml l1 lD))
          as [ [prD mlD0] lEl].
        simpl Tick.cost.
        destruct (Tick.val (deepLD_f (B := B) dflt r1 mr sf rD))
          as [ [rEl mrD] sfD1].
        simpl Tick.cost.
        specialize (SELF (MTuple M A) (MTupleA M B) _
                      measureMTuple (MPair mzero dflt dflt) p
                      (i <+> measureDigit md pr) m
                      (addSkel ml mlD0,
                       Thunk (pivotNodeDmd_f md p
                                (i <+> measureDigit md pr
                                   <+> measureSeq measureMTuple ml)
                                xs xD rEl),
                       mrD)
                      ml xs mr Hst).
        unfold split_f_c1, split_f_c2 in *; lia.
      * (* branch 3: pivot in the rear digit *)
        destruct (splitDigit md p (i <+> measureDigit md pr <+> vm) sf)
          as [ [l1 x1] r1] eqn:Hsd.
        injection Hsp as ? ? ?; subst.
        pose proof (deepRD_f_cost_rvc (B := B) md dflt pr m l1 lD) as HdR.
        pose proof (toTreeD_cost rD) as Ht.
        pose proof (lvc_toTree md r1) as Hlt.
        pose proof (rvc_le_depth m) as Hrm.
        simpl Tick.cost.
        destruct (Tick.val (deepRD_f (B := B) dflt pr m l1 lD))
          as [ [prD mD1] lEl].
        simpl Tick.cost.
        unfold split_f_c1, split_f_c2; lia.
Qed.

(** The headline cost bound: [outD]-independent (worst-case), now for
    the FAITHFUL demand function. *)
Theorem splitTreeD_f_cost {M} {A B} `{Monoid M} `{Exact A B}
    (md : A -> M) (dflt : A) (p : M -> bool) (i : M)
    (t : MSeq M A) (outD : SplitDmd M B) :
  Tick.cost (splitTreeD_f md dflt p i t outD)
    <= split_f_c1 * depth t + split_f_c2.
Proof.
  destruct (splitTree md dflt p i t) as [ [l x] r] eqn:Hsp.
  pose proof (splitTreeD_f_cost_pot _ md dflt p i t outD Hsp) as Hc.
  pose proof (rvc_pos l) as Hr.
  pose proof (lvc_pos r) as Hl.
  lia.
Qed.

Corollary split_f_O_log_n {M} {A B} `{Monoid M} `{Exact A B}
    (md : A -> M) (dflt : A) (p : M -> bool) (i : M)
    (t : MSeq M A) (outD : SplitDmd M B) :
  t <> MNil ->
  Tick.cost (splitTreeD_f md dflt p i t outD)
    <= split_f_c1 * Nat.log2 (size t) + split_f_c2.
Proof.
  intro Hne.
  pose proof (splitTreeD_f_cost md dflt p i t outD) as Hc.
  pose proof (@depth_log_size _ _ t Hne) as Hd.
  unfold split_f_c1, split_f_c2 in *. nia.
Qed.

(* ================================================================= *)
(** ** End of FingerSplit                                              *)
(* ================================================================= *)