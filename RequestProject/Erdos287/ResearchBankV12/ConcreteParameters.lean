import RequestProject.Erdos287.ResearchBankV11

/-!
# Erdős #287 — Research Bank V12 §3: the concrete repaired parameters (exact rationals)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Exact rational arithmetic only (no floating point):

* `theta0 = 1/25000 + 1/625000000`, `epsilon0 = 1/100000`, `zeta = epsilon0/100`,
  `lam = 7/13 − 3·theta0 − epsilon0` (`= vartheta`).
* Kernel-checked facts: `theta0 < 1/1000`, `epsilon0 ≤ 1/1000`,
  `3·theta0 + epsilon0 = 81253/625000000 < 1/1885`, `vartheta > 78/145`,
  `145/39 − 2/vartheta = 52426455/18953756081 > 0`.
* `concreteParams` — the V10 `CoverageParams` record at these values; it coincides with the V10
  `repairedParams` (`concreteParams_eq_repaired`), so every V10 theorem stated for a general
  `CoverageParams` specializes to the concrete values.
-/

namespace Erdos287
namespace ResearchBankV12
namespace ConcreteParameters

open ResearchBankV10.HBSupportCoverage

/-- `θ₀ = 1/25000 + 1/625000000`. -/
def theta0 : ℚ := 1 / 25000 + 1 / 625000000

/-- `ε₀ = 1/100000`. -/
def epsilon0 : ℚ := 1 / 100000

/-- `ζ = ε₀ / 100`. -/
def zeta : ℚ := epsilon0 / 100

/-- `λ = 7/13 − 3θ₀ − ε₀`. -/
def lam : ℚ := 7 / 13 - 3 * theta0 - epsilon0

/-- `ϑ = 7/13 − 3θ₀ − ε₀` (the same number as `lam`). -/
def vartheta : ℚ := 7 / 13 - 3 * theta0 - epsilon0

theorem theta0_eq : theta0 = 25001 / 625000000 := by norm_num [theta0]

theorem theta0_pos : 0 < theta0 := by norm_num [theta0]

/-- `θ₀ < 1/1000`. -/
theorem theta0_lt : theta0 < 1 / 1000 := by norm_num [theta0]

theorem epsilon0_pos : 0 < epsilon0 := by norm_num [epsilon0]

/-- `ε₀ ≤ 1/1000`. -/
theorem epsilon0_le : epsilon0 ≤ 1 / 1000 := by norm_num [epsilon0]

theorem zeta_eq : zeta = 1 / 10000000 := by norm_num [zeta, epsilon0]

theorem zeta_pos : 0 < zeta := by norm_num [zeta, epsilon0]

/-- `3θ₀ + ε₀ = 81253 / 625000000`. -/
theorem loss_eq : 3 * theta0 + epsilon0 = 81253 / 625000000 := by
  norm_num [theta0, epsilon0]

/-- `3θ₀ + ε₀ < 1/1885`. -/
theorem loss_lt : 3 * theta0 + epsilon0 < 1 / 1885 := by
  rw [loss_eq]; norm_num

theorem lam_eq_vartheta : lam = vartheta := rfl

theorem vartheta_eq : vartheta = 4373943711 / 8125000000 := by
  norm_num [vartheta, theta0, epsilon0]

theorem lam_eq : lam = 4373943711 / 8125000000 := vartheta_eq

/-- **`ϑ > 78/145`.** -/
theorem vartheta_gt : 78 / 145 < vartheta := by rw [vartheta_eq]; norm_num

/-- **`145/39 − 2/ϑ = 52426455/18953756081 > 0`.** -/
theorem pair_gap : 145 / 39 - 2 / vartheta = 52426455 / 18953756081 ∧
    (0 : ℚ) < 52426455 / 18953756081 := by
  rw [vartheta_eq]; constructor <;> norm_num

/-- `λ` in terms of `ζ`: `λ = 7/13 − 3θ₀ − 100ζ`. -/
theorem lam_zeta : lam = 7 / 13 - 3 * theta0 - 100 * zeta := by
  unfold lam zeta; ring

/-- The concrete `CoverageParams`. -/
def concreteParams : CoverageParams where
  θ₀ := theta0
  ε₀ := epsilon0
  θ₀_nonneg := theta0_pos.le
  θ₀_le := theta0_lt.le
  ε₀_pos := epsilon0_pos
  ε₀_le := epsilon0_le

theorem concreteParams_ζ : concreteParams.ζ = zeta := rfl

theorem concreteParams_lam : concreteParams.lam = lam := rfl

theorem concreteParams_θ₀ : concreteParams.θ₀ = theta0 := rfl

/-- The V12 concrete values agree with the V10 `repairedParams`. -/
theorem concreteParams_eq_repaired :
    concreteParams = ResearchBankV10.AsymptoticComposition.repairedParams := rfl

/-- The V12 values agree with the V10 exponent-gate constants. -/
theorem agrees_with_v10 :
    theta0 = ResearchBankV10.ExponentGate.theta0 ∧ epsilon0 = ResearchBankV10.ExponentGate.eps0 ∧
      vartheta = ResearchBankV10.ExponentGate.vartheta := ⟨rfl, rfl, rfl⟩

/-! ## §9 The small-total-modulus BV region (frozen analytic input; routing only) -/

/-- `smallBV(θ, r, s) :⟺ θ + r + s ≤ 1/2 − 10ζ`.  Bombieri–Vinogradov itself is **not** proved
here: Lean only routes support boxes into this region. -/
def smallBV (θ r s : ℚ) : Prop := θ + r + s ≤ 1 / 2 - 10 * zeta

instance (θ r s : ℚ) : Decidable (smallBV θ r s) := by unfold smallBV; infer_instance

/-- `smallBV` agrees with the V10 `InBV` predicate at the concrete parameters. -/
theorem smallBV_iff_InBV (b : SupportBox) : smallBV b.θ b.r b.s ↔ InBV concreteParams b :=
  Iff.rfl

/-! ## §10 Case-II box parameters -/

/-- `s* = ν − ζ`. -/
def sStar (ν : ℚ) : ℚ := ν - zeta

/-- `r* = λ − ν + ζ`. -/
def rStar (ν : ℚ) : ℚ := lam - ν + zeta

theorem rStar_add_sStar (ν : ℚ) : rStar ν + sStar ν = lam := by unfold rStar sStar; ring

theorem sStar_eq_v10 (ν : ℚ) :
    sStar ν = ResearchBankV10.HBSupportCoverage.sStar concreteParams ν := rfl

theorem rStar_eq_v10 (ν : ℚ) :
    rStar ν = ResearchBankV10.HBSupportCoverage.rStar concreteParams ν := rfl

end ConcreteParameters
end ResearchBankV12
end Erdos287
