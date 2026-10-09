import RequestProject.Erdos287.SourceChain.FourierPoisson

/-!
# Erdős #287 — physical source: an explicit admissible smooth plateau `Ψ` (§24)

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**  `sources/physical_spec.md` §24 allows a
new explicit witness for the Ordering-B profile:

`η(t) = e^{-1/t} (t > 0)`, `θ(t) = η(t)/(η(t) + η(1-t))`, `Ψ(u) = θ(4u-2) θ(10-4u)`.

Mathlib's `Real.smoothTransition` is exactly `θ`.  Kernel-proved:

* `physPsi_contDiff` — `Ψ` is `C^∞`;
* `physPsi_nonneg`, `physPsi_le_one` — `0 ≤ Ψ ≤ 1`;
* `physPsi_eq_one` — `Ψ = 1` on `[3/4, 9/4]`, hence the plateau `physPsi_plateau`:
  `Ψ(u) ≥ 1` for `1 ≤ u ≤ 2`;
* `physPsi_support`, `physPsi_hasCompactSupport` — `supp Ψ ⊆ [1/2, 5/2]`.

No normalisation `∫Ψ = 1` is asserted.  `physPsiHat ξ = ∫ Ψ(u) e(-ξu) du` is the Fourier
transform in the convention of §26, and `physPF = PF physPsiHat` is the literal nonzero-mode
Poisson remainder `𝒫_M(q,ρ)` of the existing `FourierPoisson` layer, now with an actual profile.
The Poisson summation identity for this profile is NOT proved here.
-/

open Real

namespace Erdos287.Physical

/-- **The explicit Ordering-B profile** `Ψ(u) = θ(4u-2) θ(10-4u)`. -/
noncomputable def physPsi (u : ℝ) : ℝ :=
  smoothTransition (4 * u - 2) * smoothTransition (10 - 4 * u)

theorem physPsi_contDiff : ContDiff ℝ (⊤ : ℕ∞) physPsi := by
  unfold physPsi
  apply ContDiff.mul
  · exact smoothTransition.contDiff.comp (by fun_prop)
  · exact smoothTransition.contDiff.comp (by fun_prop)

theorem physPsi_nonneg (u : ℝ) : 0 ≤ physPsi u :=
  mul_nonneg (smoothTransition.nonneg _) (smoothTransition.nonneg _)

theorem physPsi_le_one (u : ℝ) : physPsi u ≤ 1 :=
  mul_le_one₀ (smoothTransition.le_one _) (smoothTransition.nonneg _)
    (smoothTransition.le_one _)

theorem physPsi_eq_one {u : ℝ} (h1 : 3 / 4 ≤ u) (h2 : u ≤ 9 / 4) : physPsi u = 1 := by
  unfold physPsi
  rw [smoothTransition.one_of_one_le (by linarith), smoothTransition.one_of_one_le (by linarith),
    mul_one]

/-- **The required plateau** `Ψ(u) ≥ 1` on `[1, 2]`. -/
theorem physPsi_plateau {u : ℝ} (h1 : 1 ≤ u) (h2 : u ≤ 2) : 1 ≤ physPsi u :=
  (physPsi_eq_one (by linarith) (by linarith)).ge

theorem physPsi_eq_zero {u : ℝ} (h : u ≤ 1 / 2 ∨ 5 / 2 ≤ u) : physPsi u = 0 := by
  unfold physPsi
  rcases h with h | h
  · rw [smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  · rw [smoothTransition.zero_of_nonpos (show 10 - 4 * u ≤ 0 by linarith), mul_zero]

theorem physPsi_support : Function.support physPsi ⊆ Set.Icc (1 / 2) (5 / 2) := by
  intro u hu
  by_contra h
  simp only [Set.mem_Icc, not_and_or, not_le] at h
  exact hu (physPsi_eq_zero (h.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le)))

theorem physPsi_hasCompactSupport : HasCompactSupport physPsi :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc physPsi_support

/-- `Ψ̂(ξ) = ∫ Ψ(u) e(-ξu) du` (§26 convention). -/
noncomputable def physPsiHat (ξ : ℝ) : ℂ :=
  ∫ u : ℝ, (physPsi u : ℂ) * Erdos287.SourceChain.eR (-(ξ * u))

/-- The literal nonzero-mode Poisson remainder `𝒫_M(q,ρ)` with the explicit profile. -/
noncomputable def physPF (M q : ℝ) (ρ : ℤ) : ℂ :=
  Erdos287.SourceChain.PF physPsiHat M q ρ

end Erdos287.Physical
