import RequestProject.Erdos287.ResearchBankV12.ConcreteParameters

/-!
# Erdős #287 — Research Bank V12 §15: rough-seed identities (concrete re-statement)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

In the repository's Dirichlet-convolution notation (`ArithmeticFunction ℤ`, `*` = Dirichlet
convolution, `pmul` = pointwise product, `ζ` = the constant-one function):

* `rho_z_identity`:   `ρ_z = 1 ⋆ (μ · 1_{P⁺ ≤ z})`;
* `mu_rho_z_identity`: `μ · ρ_z = μ ⋆ 1_{P⁺ ≤ z}`;

both proved (re-using V10 `rough_eq_zeta_mul`, `moebius_rough_eq`), with pointwise evaluations
(`rho_z_apply`, `mu_rho_z_apply`).

The rough-seed Siegel–Walfisz estimate remains **external** (`RoughSeedSWProvider`): the only
inhabitant is the zero-error model, and it is not automatic (`X²` violates it).
-/

namespace Erdos287
namespace ResearchBankV12
namespace RoughSeedConcrete

open ArithmeticFunction ResearchBankV10.RoughSeedIdentities

/-- **`ρ_z = 1 ⋆ (μ · 1_{P⁺ ≤ z})`.** -/
theorem rho_z_identity (z : ℕ) :
    roughInd z = (zeta : ArithmeticFunction ℤ) * (moebius : ArithmeticFunction ℤ).pmul (smoothInd z) :=
  rough_eq_zeta_mul z

/-- **`μ ρ_z = μ ⋆ 1_{P⁺ ≤ z}`.** -/
theorem mu_rho_z_identity (z : ℕ) :
    (moebius : ArithmeticFunction ℤ).pmul (roughInd z) =
      (moebius : ArithmeticFunction ℤ) * smoothInd z :=
  moebius_rough_eq z

/-- Pointwise: `ρ_z(n) = ∑_{d ∣ n} μ(d) 1_{P⁺(d) ≤ z}`. -/
theorem rho_z_apply (z n : ℕ) :
    roughInd z n = ∑ d ∈ n.divisors, (moebius : ArithmeticFunction ℤ) d * smoothInd z d := by
  rw [rho_z_identity, coe_zeta_mul_apply]
  rfl

/-- Pointwise: `μ(n) ρ_z(n) = ∑_{ab = n} μ(a) 1_{P⁺(b) ≤ z}`. -/
theorem mu_rho_z_apply (z n : ℕ) :
    (moebius : ArithmeticFunction ℤ) n * roughInd z n =
      ∑ x ∈ n.divisorsAntidiagonal, (moebius : ArithmeticFunction ℤ) x.1 * smoothInd z x.2 := by
  have := congrArg (fun f : ArithmeticFunction ℤ => f n) (mu_rho_z_identity z)
  simpa [pmul_apply, mul_apply] using this

/-- The rough-seed SW estimate is an external provider: satisfiable (zero model) but not
automatic. -/
theorem roughSeedSW_external :
    RoughSeedSWProvider (fun _ _ _ => 0) ∧ ¬ RoughSeedSWProvider (fun _ _ X => X ^ 2) :=
  ⟨roughSeedSW_zero, roughSeedSW_not_automatic⟩

end RoughSeedConcrete
end ResearchBankV12
end Erdos287
