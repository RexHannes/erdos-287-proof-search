import RequestProject.Erdos287.ResearchBankV13.UpdatedSplice

/-!
# Erdős #287 — Research Bank V13 §27–28: the current effective frontier

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `current_M_an = none` (re-used from V11; no numerical constants are instantiated).
* The global splice is **BLOCKED**; the *reason* is updated:
  - historical V11 reasons (preserved): explicit analytic threshold unavailable **and** finite
    architecture absent (`v11BlockReasons`);
  - current V13 reason: explicit analytic threshold unavailable (`v13BlockReasons`).
* Finite-side status is split, never blurred (`finiteSideStatus`):
  - formal finite theorem architecture = **AVAILABLE** (generic certificate soundness, prime
    layer, two-hole theorem, both families, Proth/Pocklington soundness);
  - actual 10^500 payload = **EXTERNALLY AUDITED BUT NOT LEAN-REPLAYED**.
* `effectiveOverlap U M_an :⟺ M_an ≤ U + 1` — **the decisive splice condition**.
* `splice_closes_of_future_constants`: if a *future* `NumericalExternalConstants` instance yields
  `M_an` (via the V11 `analyticActivation`), the analytic chain gives eventual exclusion from
  `M_an`, and `effectiveOverlap U M_an` holds with `NoCounterexampleUpTo U`, then the splice
  closes.  No such instance is created.
-/

namespace Erdos287
namespace ResearchBankV13
namespace EffectiveFrontier

open FiniteRepresentationModel IntervalCertificate UpdatedSplice
  ResearchBankV11.EffectiveConstants ResearchBankV11.AnalyticActivation

/-- **The current explicit analytic threshold: none.** -/
theorem current_M_an_none (A : ℝ) : current_M_an A = none := current_M_an_eq_none A

/-- `effectiveOverlap U M_an :⟺ M_an ≤ U + 1`. -/
def effectiveOverlap (U M_an : ℕ) : Prop := M_an ≤ U + 1

instance (U M_an : ℕ) : Decidable (effectiveOverlap U M_an) := by
  unfold effectiveOverlap; infer_instance

/-- **The splice closes once a future constant bundle produces an overlapping `M_an`.**  All
three analytic/finite inputs are visible hypotheses. -/
theorem splice_closes_of_future_constants (c : NumericalExternalConstants) {A : ℝ} {M_an U : ℕ}
    (hM : analyticActivation c A = some M_an)
    (hchain : ∀ M', analyticActivation c A = some M' → ∀ M, M' ≤ M → NoCounterexampleAt M)
    (hfin : NoCounterexampleUpTo U) (hov : effectiveOverlap U M_an) :
    ∀ S : Finset ℕ, ¬ Erdos287Counterexample S :=
  erdos287_of_splice hfin (hchain M_an hM) hov

/-- Without overlap the same data do not suffice (the `U + 2` fixture). -/
theorem overlap_needed (U : ℕ) : ¬ effectiveOverlap U (U + 2) := by
  unfold effectiveOverlap; omega

/-- Reasons for the splice being blocked. -/
inductive BlockReason
  | explicitAnalyticThresholdUnavailable
  | finiteArchitectureAbsent
  deriving DecidableEq, Repr

/-- Historical V11 reasons (preserved, not rewritten). -/
def v11BlockReasons : List BlockReason :=
  [.explicitAnalyticThresholdUnavailable, .finiteArchitectureAbsent]

/-- Current V13 reason. -/
def v13BlockReasons : List BlockReason := [.explicitAnalyticThresholdUnavailable]

theorem v11_reasons_preserved :
    BlockReason.finiteArchitectureAbsent ∈ v11BlockReasons ∧
      ResearchBankV11.FiniteArchitectureFrontier.currentArchitecture = none := ⟨by decide, rfl⟩

theorem v13_reason_updated :
    v13BlockReasons = [.explicitAnalyticThresholdUnavailable] ∧
      BlockReason.finiteArchitectureAbsent ∉ v13BlockReasons := ⟨rfl, by decide⟩

/-- The V13 reason is justified: the analytic threshold is unavailable. -/
theorem v13_reason_justified (A : ℝ) :
    current_M_an A = none ∧ IsEmpty (SpliceInputV13 A) :=
  ⟨current_M_an_eq_none A, missing_M_an_blocks_splice A⟩

/-- **The current global splice is BLOCKED.** -/
theorem current_global_splice_blocked (A : ℝ) : IsEmpty (SpliceInputV13 A) :=
  missing_M_an_blocks_splice A

/-- Finite-side status values. -/
inductive FiniteStatus
  | available
  | availableThrough (U : ℕ)
  | externallyAuditedNotLeanReplayed
  deriving DecidableEq, Repr

/-- **The finite-side status, split into its two components.** -/
structure FiniteSideStatus where
  formalFiniteTheoremArchitecture : FiniteStatus
  actual10pow500Payload : FiniteStatus
  leanReplayedEndpoint : ℕ

/-- The current finite-side status. -/
def finiteSideStatus : FiniteSideStatus where
  formalFiniteTheoremArchitecture := .available
  actual10pow500Payload := .externallyAuditedNotLeanReplayed
  leanReplayedEndpoint := AuditedEndpoint.bankLeanReplayedEndpoint

/-- The two components are distinct statuses and are never blurred. -/
theorem finiteSide_not_blurred :
    finiteSideStatus.formalFiniteTheoremArchitecture = .available ∧
      finiteSideStatus.actual10pow500Payload = .externallyAuditedNotLeanReplayed ∧
      finiteSideStatus.formalFiniteTheoremArchitecture ≠ finiteSideStatus.actual10pow500Payload ∧
      NoCounterexampleUpTo finiteSideStatus.leanReplayedEndpoint :=
  ⟨rfl, rfl, by decide, AuditedEndpoint.bankLeanReplayedEndpoint_sound⟩

/-- **Firewall (b), V13 form**: the bank's constants are `none`, so no `M_an` and no overlap test
can currently be performed. -/
theorem overlap_test_pending (A : ℝ) :
    currentConstants = none ∧ current_M_an A = none ∧ ¬ ∃ M, current_M_an A = some M := by
  refine ⟨rfl, current_M_an_eq_none A, ?_⟩
  rintro ⟨M, h⟩; rw [current_M_an_eq_none] at h; cases h

end EffectiveFrontier
end ResearchBankV13
end Erdos287
