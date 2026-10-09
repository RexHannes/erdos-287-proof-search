import RequestProject.Erdos287.ResearchBankV15.FixedAffineSource
import RequestProject.Erdos287.ResearchBankV15.MobiusCoefficients

/-!
# Erdős #287 — Research Bank V15 §B9: source data, physical weight and normalization

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `SourceData` — the fixed-source data at scale `M`: integrated cutoff `G`, scale `X(M)`,
  `W0`, the residue `b0 (mod W0)`, the divisor-tuple support `D(M)`, and the three normalization
  factors `C_X`, `S_W0(a)`, `I`;
* `sieveSum`, `weight` — the **physical weight**
  `w(M, t) = 1[t ≡ b0 (W0)] · (∑_{d ∈ D(M), d_i ∣ L_i(t) ∀ i} λ_d)^2 ≥ 0` built from the actual
  Möbius coefficients; `weightSystem` — it as a V14 `WeightSystem` of the fixed tuple;
* `NX = C_X · S_W0(a) · I` — **the normalization; the factor `I` is mandatory**;
* `weight_scale`, `S0_scale` — under `G ↦ c G` the weight and `S0` scale by `c²`;
* `normalization_scale_invariant` — with `I` (quadratic in the kernel) `S0/N_X` is invariant;
* `omitting_I_breaks_invariance` — **regression**: dropping `I` breaks scale invariance (`c = 2`).
-/

namespace Erdos287
namespace ResearchBankV15
namespace Normalization

open ResearchBankV14 ResearchBankV14.BalancedKernelParameters
open ResearchBankV14.ConditionalAsymptoticImplication FixedAffineSource MobiusCoefficients
open DerivativeKernel

/-- The fixed-source data. -/
structure SourceData where
  /-- The integrated cutoff `G` (not the kernel `F`). -/
  G : Kernel K
  /-- The scale `X(M)`. -/
  Xs : ℕ → ℝ
  /-- The `W`-trick modulus. -/
  W0 : ℕ
  W0_pos : 0 < W0
  /-- The residue class `t ≡ b0 (mod W0)`. -/
  b0 : ℕ
  /-- The divisor-tuple support at scale `M`. -/
  D : ℕ → Finset (Fin K → ℕ)
  /-- `C_X` at scale `X(M)`. -/
  CX : ℕ → ℝ
  /-- The singular series `S_W0(a)`. -/
  SW0 : ℝ
  /-- The functional factor `I` (quadratic in the kernel). -/
  I : ℝ

variable (src : SourceData)

open Classical in
/-- The sieve sum `∑_{d ∈ D(M), d_i ∣ L_i(t)} λ_d`. -/
noncomputable def sieveSum (M t : ℕ) : ℝ :=
  ∑ d ∈ src.D M, if ∀ i, d i ∣ L i t then lam src.G (src.Xs M) src.W0 d else 0

/-- **The physical weight.** -/
noncomputable def weight (M t : ℕ) : ℝ :=
  (if t % src.W0 = src.b0 then 1 else 0) * sieveSum src M t ^ 2

theorem weight_nonneg (M t : ℕ) : 0 ≤ weight src M t := by
  unfold weight; split_ifs <;> positivity

/-- The physical weight as a V14 weight system of the fixed tuple. -/
noncomputable def weightSystem : WeightSystem tuple := ⟨weight src, weight_nonneg src⟩

/-- **`N_X = C_X · S_W0(a) · I`.** -/
noncomputable def NX (M : ℕ) : ℝ := src.CX M * src.SW0 * src.I

/-- The (incorrect) normalization without `I`. -/
noncomputable def NXwithoutI (M : ℕ) : ℝ := src.CX M * src.SW0

/-- Rescaling the kernel by `c` (the functional `I` is quadratic in the kernel). -/
noncomputable def SourceData.scale (c : ℝ) : SourceData :=
  { src with G := fun x => c * src.G x, I := c ^ 2 * src.I }

theorem sieveSum_scale (c : ℝ) (M t : ℕ) :
    sieveSum (src.scale c) M t = c * sieveSum src M t := by
  classical
  unfold sieveSum SourceData.scale
  simp only
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs
  · exact lam_smul _ _ _ _ _
  · ring

theorem weight_scale (c : ℝ) (M t : ℕ) :
    weight (src.scale c) M t = c ^ 2 * weight src M t := by
  unfold weight
  rw [sieveSum_scale]
  have : (src.scale c).W0 = src.W0 := rfl
  have h2 : (src.scale c).b0 = src.b0 := rfl
  rw [this, h2]; ring

theorem S0_scale (c : ℝ) (M : ℕ) :
    S0 tuple (weightSystem (src.scale c)) M = c ^ 2 * S0 tuple (weightSystem src) M := by
  unfold S0 weightSystem
  simp only
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => weight_scale src c M t

theorem NX_scale (c : ℝ) (M : ℕ) : NX (src.scale c) M = c ^ 2 * NX src M := by
  unfold NX SourceData.scale; ring

/-- **With `I`, `S0/N_X` is scale invariant.** -/
theorem normalization_scale_invariant {c : ℝ} (hc : c ≠ 0) (M : ℕ) :
    S0 tuple (weightSystem (src.scale c)) M / NX (src.scale c) M =
      S0 tuple (weightSystem src) M / NX src M := by
  rw [S0_scale, NX_scale]
  have : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  rw [mul_div_mul_left _ _ this]

/-- **Regression: omitting `I` breaks scale invariance** (rescaling by `c = 2`). -/
theorem omitting_I_breaks_invariance (M : ℕ) (hS : S0 tuple (weightSystem src) M ≠ 0)
    (hN : NXwithoutI src M ≠ 0) :
    S0 tuple (weightSystem (src.scale 2)) M / NXwithoutI (src.scale 2) M ≠
      S0 tuple (weightSystem src) M / NXwithoutI src M := by
  rw [S0_scale]
  have hN' : NXwithoutI (src.scale 2) M = NXwithoutI src M := rfl
  rw [hN']
  intro h
  rw [mul_div_assoc] at h
  have hq : S0 tuple (weightSystem src) M / NXwithoutI src M ≠ 0 := div_ne_zero hS hN
  have : (2 : ℝ) ^ 2 = 1 := by
    have := mul_right_cancel₀ hq (h.trans (one_mul _).symm)
    exact this
  norm_num at this

end Normalization
end ResearchBankV15
end Erdos287
