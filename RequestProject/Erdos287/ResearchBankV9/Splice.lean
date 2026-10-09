import RequestProject.Erdos287.ResearchBankV9.GraphLocalization
import RequestProject.Erdos287.ResearchBankV9.AsraInterfaces

/-!
# Erdős #287 — Research Bank V9 §5: eventual exclusion and the finite splice

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `eventual_exclusion_conditional` — the implication chain, **only conditionally**:
  ASRA + (graph-selective occupancy + prescribed-shape/localization data + Maynard-type prime
  supply, packaged as the explicit chain hypothesis producing useful localized edges at every
  scale `≥ M_an`) ⟹ `EventualNoCounterexampleFrom M_an`.  No `M_an` is created.
* `splice` — finite verification through `U` + `U ≥ M₀ − 1` + eventual exclusion from `M₀`
  ⟹ full exclusion (no Erdős #287 counterexample at all).
* `SpliceThresholds`, `M₀` — `M₀ = max(M_an, M_geom, M_int, M_rig)`, defined only when the analytic
  threshold is present (`Option`).  The **current** state has `M_an = none`, hence
  `M₀ = none` (`current_M0_unavailable`); `EffectiveFiniteSplice` is an uninhabited proposition
  (it is equivalent to the full Erdős #287 statement, `effectiveSplice_iff_no_counterexample`).
* Historical metadata: the earlier finite endpoint `≈ 6.125 × 10^120` is recorded as a string only
  and is not reverified; `asymptotic_without_threshold_does_not_splice` shows that an eventual
  statement plus a finite check below its (unknown) threshold does not give full exclusion.
-/

namespace Erdos287
namespace ResearchBankV9
namespace Splice

open GraphLocalization AsraInterfaces

/-- No Erdős #287 counterexample has maximum `≥ M₀`. -/
def EventualNoCounterexampleFrom (M₀ : ℕ) : Prop :=
  ∀ A : Finset ℕ, ∀ h : Erdos287Counterexample A, A.max' h.nonempty < M₀

/-- Finite verification: no Erdős #287 counterexample has maximum `≤ U`. -/
def FiniteVerifiedThrough (U : ℕ) : Prop :=
  ∀ A : Finset ℕ, ∀ h : Erdos287Counterexample A, U < A.max' h.nonempty

/-- **The splice.** -/
theorem splice {U M₀ : ℕ} (hfin : FiniteVerifiedThrough U) (hU : M₀ ≤ U + 1)
    (hev : EventualNoCounterexampleFrom M₀) : ∀ A : Finset ℕ, ¬ Erdos287Counterexample A := by
  intro A h
  have h1 := hfin A h
  have h2 := hev A h
  omega

/-- **Conditional eventual exclusion.**  The chain hypothesis `hchain` is where graph-selective
occupancy, the prescribed-shape/localization data and the prime supply enter; it is a premise,
never inhabited here. -/
theorem eventual_exclusion_conditional (D : ASRAData) (PrimeSupply : Prop) {c : ℝ}
    (hc : 1 / Real.exp 1 < c) (M_an : ℕ) (hASRA : ASRA D) (hsupply : PrimeSupply)
    (hchain : ASRA D → PrimeSupply → ∀ M ≥ M_an, Nonempty (UsefulEdgeData M c)) :
    EventualNoCounterexampleFrom M_an := by
  intro A h
  by_contra hge
  push_neg at hge
  exact no_counterexample_above_of_edge_supply hc (hchain hASRA hsupply) h hge

/-- The explicit splice thresholds; the analytic threshold is optional. -/
structure SpliceThresholds where
  /-- Analytic threshold (absent in the current state). -/
  M_an : Option ℕ
  /-- Geometric threshold. -/
  M_geom : ℕ
  /-- Integrality threshold. -/
  M_int : ℕ
  /-- Rigidity threshold. -/
  M_rig : ℕ

/-- `M₀ = max(M_an, M_geom, M_int, M_rig)`, available only when `M_an` is. -/
def SpliceThresholds.M₀ (t : SpliceThresholds) : Option ℕ :=
  t.M_an.map fun a => max a (max t.M_geom (max t.M_int t.M_rig))

/-- The **current** thresholds: the analytic threshold is absent.  The finite thresholds are
recorded as `0` placeholders because no value is banked for them in this layer. -/
def currentThresholds : SpliceThresholds := ⟨none, 0, 0, 0⟩

/-- **`M₀` is unavailable in the current state.** -/
theorem current_M0_unavailable : currentThresholds.M₀ = none := rfl

theorem M0_ge {t : SpliceThresholds} {a m : ℕ} (ha : t.M_an = some a) (hm : t.M₀ = some m) :
    a ≤ m ∧ t.M_geom ≤ m ∧ t.M_int ≤ m ∧ t.M_rig ≤ m := by
  simp only [SpliceThresholds.M₀, ha, Option.map_some, Option.some.injEq] at hm
  subst hm
  omega

/-- The effective finite splice: an explicit threshold, a matching finite verification and the
eventual exclusion.  **OPEN / BLOCKED** — never inhabited. -/
def EffectiveFiniteSplice : Prop :=
  ∃ M₀ U : ℕ, FiniteVerifiedThrough U ∧ M₀ ≤ U + 1 ∧ EventualNoCounterexampleFrom M₀

/-- The effective splice is exactly the full statement "no Erdős #287 counterexample"; it is
therefore not claimed. -/
theorem effectiveSplice_iff_no_counterexample :
    EffectiveFiniteSplice ↔ ∀ A : Finset ℕ, ¬ Erdos287Counterexample A := by
  constructor
  · rintro ⟨M₀, U, hfin, hU, hev⟩
    exact splice hfin hU hev
  · intro h
    exact ⟨0, 0, fun A hA => (h A hA).elim, by omega, fun A hA => (h A hA).elim⟩

/-- Historical metadata only (not reverified, not used in any proof). -/
def historicalFiniteEndpoint : String :=
  "≈ 6.125 × 10^120 (historical metadata; the finite chain is not imported or reverified)"

/-- **Firewall: an asymptotic statement without an effective threshold does not splice.**  An
eventual exclusion from some unknown threshold plus a finite check through `U` does not give
full exclusion. -/
theorem asymptotic_without_threshold_does_not_splice (U : ℕ) :
    ¬ ∀ bad : ℕ → Prop, (∃ M₀, ∀ M ≥ M₀, ¬ bad M) → (∀ M ≤ U, ¬ bad M) → ∀ M, ¬ bad M := by
  intro h
  exact h (fun M => M = U + 1) ⟨U + 2, fun M hM hb => by omega⟩ (fun M hM hb => by omega)
    (U + 1) rfl

/-- **Firewall: a finite obstruction does not imply an asymptotic one.** -/
theorem finite_obstruction_not_asymptotic :
    ¬ ∀ bad : ℕ → Prop, (∃ M, bad M) → ∀ M₀, ∃ M ≥ M₀, bad M := by
  intro h
  obtain ⟨M, hM, hb⟩ := h (fun M => M = 0) ⟨0, rfl⟩ 1
  omega

/-- **Firewall: a conditional implication does not inhabit its premise.** -/
theorem conditional_does_not_inhabit_premise : ¬ ∀ P Q : Prop, (P → Q) → P := by
  intro h; exact h False True (fun _ => trivial)

end Splice
end ResearchBankV9
end Erdos287
