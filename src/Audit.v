(** ===== Audit ===== *)
(** Mechanical realisation of the thesis contribution audit.

    Prints the assumption set of every headline theorem via
    [Print Assumptions]. Each theorem is preceded by [Locate], whose
    output ("Constant Clairvoyance.<File>.<name>") labels the block
    that follows in the build log.

    Expected output per theorem: either
      "Closed under the global context"
    or an axiom set containing only [Classical_Prop.classic], which is
    inherited from the vendored Clairvoyance library (its trace
    metatheory uses classical logic), not introduced by this
    development.

    This file is intentionally NOT listed in [_CoqProject]: a plain
    [make] does not run it. Run it via [make audit], whose wrapper
    script ([scripts/audit.sh]) re-checks the output and fails on any
    assumption outside the allowlist, and additionally sweeps the
    thesis sources for [Admitted]/[admit]/[Axiom] outside comments. *)

From Clairvoyance Require Import
  FingerCons FingerSnoc FingerHead FingerTail
  FingerConcat FingerSplit FingerPhysicist.

(** ===== Main theorem: O(1) amortised deque, persistent ===== *)

Locate amortized_cost.
Print Assumptions FingerPhysicist.amortized_cost.

(** ===== Deque operations: demand-correctness + cost ===== *)

Locate fconsD'_approx.
Print Assumptions FingerCons.fconsD'_approx.
Locate fconsD'_spec.
Print Assumptions FingerCons.fconsD'_spec.
Locate fconsD'_cost.
Print Assumptions FingerCons.fconsD'_cost.

Locate fsnocD'_approx.
Print Assumptions FingerSnoc.fsnocD'_approx.
Locate fsnocD'_spec.
Print Assumptions FingerSnoc.fsnocD'_spec.
Locate fsnocD'_cost.
Print Assumptions FingerSnoc.fsnocD'_cost.

Locate headD'_approx.
Print Assumptions FingerHead.headD'_approx.
Locate headD'_spec.
Print Assumptions FingerHead.headD'_spec.
Locate headD'_cost.
Print Assumptions FingerHead.headD'_cost.

Locate ftailD'_approx.
Print Assumptions FingerTail.ftailD'_approx.
Locate ftailD'_spec.
Print Assumptions FingerTail.ftailD'_spec.
Locate ftailD'_cost.
Print Assumptions FingerTail.ftailD'_cost.

(** ===== Concatenation: demand-correctness + worst-case O(log n) ===== *)

Locate glueD'_approx.
Print Assumptions FingerConcat.glueD'_approx.
Locate glueD'_spec.
Print Assumptions FingerConcat.glueD'_spec.
Locate glueD'_cost.
Print Assumptions FingerConcat.glueD'_cost.

Locate concatD_approx.
Print Assumptions FingerConcat.concatD_approx.
Locate concatD_spec.
Print Assumptions FingerConcat.concatD_spec.
Locate concatD_cost.
Print Assumptions FingerConcat.concatD_cost.
Locate concatD_cost_O_log_n.
Print Assumptions FingerConcat.concatD_cost_O_log_n.

(** ===== Random access: demand-correctness + worst-case O(log n) ===== *)

Locate indexD_approx.
Print Assumptions FingerSplit.indexD_approx.
Locate indexD_spec.
Print Assumptions FingerSplit.indexD_spec.
Locate index_spec.
Print Assumptions FingerSplit.index_spec.
Locate indexD_cost.
Print Assumptions FingerSplit.indexD_cost.
Locate index_O_log_n.
Print Assumptions FingerSplit.index_O_log_n.

(** ===== Split: worst-case O(log n) cost ===== *)

Locate splitTreeD_cost.
Print Assumptions FingerSplit.splitTreeD_cost.
Locate split_O_log_n.
Print Assumptions FingerSplit.split_O_log_n.

(** ===== Faithful split: telescoping worst-case O(log n) cost ===== *)

Locate splitTreeD_f_cost_pot.
Print Assumptions FingerSplit.splitTreeD_f_cost_pot.
Locate splitTreeD_f_cost.
Print Assumptions FingerSplit.splitTreeD_f_cost.
Locate split_f_O_log_n.
Print Assumptions FingerSplit.split_f_O_log_n.
