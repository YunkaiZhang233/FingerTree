(** * Finger Trees (Claessen 2020, simplified)
 
    Based on: "Finger trees explained anew, and slightly simplified"
    by Koen Claessen (Haskell Symposium 2020).
 
    We verify amortized constant-time deque operations (cons, snoc,
    uncons, unsnoc) using the bidirectional demand semantics and the
    reverse physicist's method from Xia et al. (ICFP 2024).
 
    The key data structure is:
 
      Seq A = Nil | Unit A | More (Digit A) (Seq (A * A)) (Digit A)
 
    where Digit A holds 1--3 elements. The recursive spine stores
    pairs, doubling the element type at each level — the same
    polymorphic recursion pattern as the implicit queue.
 
    Compared to ImplicitQueue.v:
      - Digit range widens from {1,2} to {1,2,3}
      - Both ends support insertion and deletion (deque, not queue)
      - The amortised argument uses min(|f|-1, |r|-1) for the
        debit invariant instead of the asymmetric (|f|-1)+(1-|r|)
*)
 
From Coq Require Import Arith Psatz Relations RelationClasses.
From Clairvoyance Require Import Core Approx ApproxM Tick Prod Option.
 
Import Tick.Notations.
Open Scope tick_scope.
 
Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.
 
#[local] Existing Instance Exact_id | 1.