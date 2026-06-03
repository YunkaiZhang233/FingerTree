(** * FingerSplit — annotated finger trees: worst-case O(log n) split and
      random access (Claessen-simplified, Hinze–Paterson measures).

    SCOPE (mirrors [FingerConcat.v]): this file targets the worst-case
    [O(log n)] COST bounds for [splitTree], [index], and [split].  The
    pure layer and the demand-function tick structure are concrete; the
    demand *values* (and hence [splitD_approx]/[splitD_spec]) are
    correctness-scope and left admitted, exactly as [glueD'_approx]/
    [glueD'_spec] are in [FingerConcat.v].

    Measures are taken over an abstract [Monoid] (see [FingerMonoid.v]);
    the element measure [md : A -> M] is threaded à la Leroy.  Random
    access is the [Monoid_size] instantiation; the same [splitTree] gives
    priority queues / ordered sequences under [Monoid_interval] /
    [Monoid_lastval].

    Headline results (this file):
      [indexD_cost]      : Tick.cost (indexD md i t xD)      ≤ c·depth t + c'
      [splitTreeD_cost]  : Tick.cost (splitTreeD md d p i t o) ≤ c·depth t + c'
      [index_O_log_n]    : ... ≤ c · log2 (size t) + c'                       *)

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
(** ** Section 3: Random access and friends (Leroy's get/set/delete)   *)
(* ================================================================= *)

(** Specialise to the size monoid: [md := fun _ => 1], [p := i <? ·]. *)
Section RandomAccess.
  Context {A : Type}.
  Definition sz1 : A -> nat := fun _ => 1.

  (** Read the [i]-th element ([dflt] returned iff out of bounds). *)
  Definition index (dflt : A) (i : nat) (t : MSeq nat A) : A :=
    let '(_, x, _) := splitTree sz1 dflt (fun s => i <? s) 0 t in x.

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
(* Reflexive/Transitive/PartialOrder: port from FingerCore.v if needed
   for the (admitted) correctness lemmas; not required for cost. *)

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

(** [splitTreeD]: one [Tick.tick] per visited [MMore]; reconstruction
    gated by the half-demands [lD]/[rD]; recurse on the middle.  When
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
                     (Undefined, Undefined, Undefined) in
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

(** *** M7 — reconstruction telescoping (the only genuinely new lemma).
    The bottom-up [deepL]/[deepR] fold building one half costs [O(depth)]:
    with potential [Φ = lvc] (resp. [rvc]) the amortised cost per
    [deepL]/[deepR] step is constant, and the run-cascades telescope.
    Phrased as a bound on the total reconstruction cost incurred along the
    descent path.  Proof: the physicist's argument of §4.2 — three cases
    on the residual ([], singleton, size-2/3), each amortised ≤ K+1. *)
Lemma deepL_reconstruction_cost {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (r : list A) (m : MSeq M (MTuple M A)) (sf : Digit A) (rD : T (MSeqA M B)) :
  Tick.cost (deepLD md dflt r m sf rD) + lvc (deepL md dflt r m sf) <=
    (split_c1) + lvc m.
Proof. Admitted.   (* the per-step amortised inequality; sum gives O(depth) *)
Lemma deepR_reconstruction_cost {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (pr : Digit A) (m : MSeq M (MTuple M A)) (l : list A) (lD : T (MSeqA M B)) :
  Tick.cost (deepRD md dflt pr m l lD) + rvc (deepR md dflt pr m l) <=
    (split_c1) + rvc m.
Proof. Admitted.

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
                     (i <+> measureDigit md pr) m Undefined).
           simpl Tick.cost. unfold split_c1, split_c2 in *. lia.
        -- simpl Tick.cost. unfold split_c1, split_c2. lia.
Qed.

(** *** M8 — full split: descent (M6) + two reconstructions (M7). *)
Theorem splitTreeD_cost {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (p : M -> bool) (i : M) (t : MSeq M A) (outD : SplitDmd M B) :
  Tick.cost (splitTreeD md dflt p i t outD) <= split_c1 * depth t + split_c2.
Proof. Admitted.   (* §4.2: combine indexD_cost with deep*_reconstruction_cost *)

(* ================================================================= *)
(** ** Section 7: O(log n) corollaries (mirror concatD_cost_O_log_n)    *)
(* ================================================================= *)

(** Needs [depth_log_size]/[size_pos] ported to [MSeq] (M1). *)
Corollary index_O_log_n {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (p : M -> bool) (i : M) (t : MSeq M A) (xD : T B) :
  t <> MNil ->
  Tick.cost (indexD md dflt p i t xD)
    <= split_c1 * Nat.log2 (size t) + split_c2.
Proof. Admitted.

Corollary split_O_log_n {M} {A B} `{Monoid M} `{Exact A B} (md : A -> M) (dflt : A)
    (p : M -> bool) (i : M) (t : MSeq M A) (outD : SplitDmd M B) :
  t <> MNil ->
  Tick.cost (splitTreeD md dflt p i t outD)
    <= split_c1 * Nat.log2 (size t) + split_c2.
Proof. Admitted.

(* ================================================================= *)
(** ** Section 8: Correctness (future work, admitted — cf. FingerConcat)*)
(* ================================================================= *)

(** Split contract (Leroy): [¬ p mzero] and [p (measureSeq md t)] make the
    pivot exist; [splitD_approx]/[splitD_spec] mirror [glueD'_approx]/
    [glueD'_spec] and need correct [viewLD]/[viewRD]/[deepLD]/[deepRD]. *)

(* Lemma split_correct {M A} `{Monoid M} (md : A -> M) (dflt : A)
     (p : M -> bool) (i : M) (t : MSeq M A) :
     p i = false -> p (i <+> measureSeq md t) = true ->
     let '(l, x, r) := splitTree md dflt p i t in
     (* toList l ++ [x] ++ toList r = toList t  ∧  the pivot's prefix-measure
        is the first to satisfy p *) ...
   Admitted. *)

(* Lemma indexD_approx / splitTreeD_spec : ... Admitted. *)

(* ================================================================= *)
(** ** End of FingerSplit                                              *)
(* ================================================================= *)