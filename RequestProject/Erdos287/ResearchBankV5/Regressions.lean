import RequestProject.Erdos287.AnchoredV4
import RequestProject.Erdos287.ResearchBankV5.ContactCore.PathTransfer
import RequestProject.Erdos287.ResearchBankV5.ContactCore.StrictHeight
import RequestProject.Erdos287.ResearchBankV5.ContactCore.PadicSaturation
import RequestProject.Erdos287.ResearchBankV5.KilledRoutes

/-!
# Research Bank V5 — regression suite

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Every statement in this file is an **exact finite** statement.  A regression certifies a fixture,
never an asymptotic theorem.

Contents (re-exports keep the original V2/V3/V4 theorems untouched):

1. factor-two denominator fixture (`regression_factor_two`, from Anchored V4);
2. doubled-denominator lattice fixture `1/1056 + 1/1080 = 89/47520` (`regression_doubled_lattice`);
3. the `53 — 317 — 79` depth-two splice (`regression_depth_two_splice`);
4. proper-power forced-zero fixture `[34,100]`, `q = 16`, `d = 4`
   (`regression_properPower_forced_zero`, `regression_valuation_lift_34_100`);
5. `p`-adic saturation finite examples (`regression_padic_saturation`);
6. raw-port `4ℓ` bound finite example (`regression_raw_port_cap`);
7. strict-height exhaustive finite checks (`regression_strict_height`);
8. the `20 → 19` no-fixed-ratio-drop fixture (`regression_no_fixed_ratio`);
9. primorial local-factor cancellation (`regression_primorial_cancellation`).
-/

namespace Erdos287
namespace ResearchBankV5
namespace Regressions

open ContactCore

/-! ## 1–2.  Anchored V4 denominator fixtures (re-exported unchanged) -/

/-- **Factor-two fixture.**  `32 ∣ 2·L(16)` but `32 ∤ L(16)`: the factor `2` in `den(2Δ)` is
load-bearing. -/
theorem regression_factor_two : (32 : ℕ) ∣ 2 * Erdos287.AnchoredV4.L 16 ∧
    ¬ ((32 : ℕ) ∣ Erdos287.AnchoredV4.L 16) :=
  Erdos287.AnchoredV4.two_factor_essential

/-- **Doubled-denominator lattice fixture.**  `1/1056 + 1/1080 = 89/47520`, with
`den(2Δ) ∣ L(30)` and `den(Δ) ∤ L(30)`. -/
theorem regression_doubled_lattice :
    Erdos287.AnchoredV4.deltaCert = 89 / 47520 ∧
      (2 * Erdos287.AnchoredV4.deltaCert).den ∣ Erdos287.AnchoredV4.L 30 ∧
      ¬ (Erdos287.AnchoredV4.deltaCert.den ∣ Erdos287.AnchoredV4.L 30) :=
  Erdos287.AnchoredV4.doubled_lattice_regression

/-! ## 3.  Depth-two splice -/

/-- **`53 — 317 — 79`.**  Two unit edges whose direct splice is not a unit. -/
theorem regression_depth_two_splice :
    ((6 : ℤ) * 53 - 1 * 317 = 1) ∧ ((1 : ℤ) * 317 - 4 * 79 = 1) ∧
      ((6 : ℤ) * 53 - 4 * 79 ≠ 1 ∧ (6 : ℤ) * 53 - 4 * 79 ≠ -1) :=
  direct_splice_not_unit

/-- PATH reproduces the fixture exactly. -/
theorem regression_path_transfer_fixture :
    Dseq fixtureD 2 * fixtureP 2
      = Cseq fixtureC 2 * fixtureP 0 - Rseq fixtureC fixtureD fixtureSigma 2 :=
  fixture_path_transfer

/-! ## 4.  Proper-power forced-zero fixture `[34,100]`, `q = 16`, `d = 4` -/

/-- Cofactor interval of the owner `q = 16` inside the window `[34,100]` is `[3,6]`. -/
theorem regression_cofactor_interval_34_100 : (34 + 16 - 1) / 16 = 3 ∧ 100 / 16 = 6 := by
  norm_num

/-- The base-`2` valuation layers of the cofactor interval `[3,6]`:
`n₀ = 2` (`{3,5}`), `n₁ = 1` (`{6}`), `n₂ = 1` (`{4}`); the first deficient layer is `v✱ = 1`. -/
theorem regression_properPower_forced_zero :
    exactLayerCount 3 6 2 0 = 2 ∧ exactLayerCount 3 6 2 1 = 1 ∧ exactLayerCount 3 6 2 2 = 1 ∧
      DeficientLayer 3 6 2 1 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  unfold DeficientLayer
  decide

/-- The forced-zero terminal `d = 4` indeed has `v₂(d) = 2 ≥ v✱ = 1`. -/
theorem regression_forced_zero_valuation : (2 : ℕ) ^ 1 ∣ 4 ∧ (2 : ℕ) ^ 2 ∣ 4 := by decide

/-- **Valuation lift on the fixture.**  `q = 16 = 2⁴`, `d = 4 = 2²·1`, `h = 2⁶ = 64`:
`q·d = h·d₀` and `⌊⌊100/16⌋/2²⌋ = ⌊100/64⌋`. -/
theorem regression_valuation_lift_34_100 :
    2 ^ 4 * (2 ^ 2 * 1) = 2 ^ (4 + 2) * 1 ∧ 100 / 2 ^ 4 / 2 ^ 2 = 100 / 2 ^ (4 + 2) := by
  refine ⟨valuationLift_mul 2 4 2 1, valuationLift_floor 100 2 4 2⟩

/-! ## 5.  `p`-adic saturation finite examples -/

/-- Subset sums of `ℓ - 1 = 4` nonzero residues cover `𝔽₅`; three do not. -/
theorem regression_padic_saturation :
    subsetSums 5 [1, 1, 1, 1] = Finset.univ ∧ subsetSums 3 [2, 1] = Finset.univ ∧
      subsetSums 5 [1, 1, 1] ≠ Finset.univ :=
  ⟨subsetSums_regression_five, subsetSums_regression_three, subsetSums_regression_sharp⟩

/-! ## 6.  Raw-port `4ℓ` bound -/

/-- On the fixture the deficient layer `v✱ = 1` carries `D₁ = 2 ≤ 4·2 = 8` multiples of `2¹`, in
accordance with `rawPort_cap`. -/
theorem regression_raw_port_cap :
    layerCount 3 6 2 1 = 2 ∧ layerCount 3 6 2 1 ≤ 4 * 2 := by
  refine ⟨by decide, ?_⟩
  exact rawPort_cap 3 6 2 1 (by norm_num) (by unfold DeficientLayer; decide)

/-! ## 7.  Strict height -/

/-- Strict-height exhaustive checks at two scales, plus the `M = 100`, `p = 41`, `q = 43`
fixture. -/
theorem regression_strict_height :
    (100 / 41 = 2 ∧ 100 / 43 = 2 ∧
        ∀ c ∈ Finset.Icc 1 2, ∀ d ∈ Finset.Icc 1 2,
          41 * c ≠ 43 * d + 1 ∧ 43 * d ≠ 41 * c + 1) ∧
      (∀ p ∈ Finset.Icc 20 60, ∀ q ∈ Finset.Icc 20 60,
        p < q → Odd p → Odd q → 300 / p = 300 / q →
          ∀ c ∈ Finset.Icc 1 (300 / p), ∀ d ∈ Finset.Icc 1 (300 / p),
            p * c ≠ q * d + 1 ∧ q * d ≠ p * c + 1) :=
  ⟨strictHeight_regression_fixture, strictHeight_regression_sweep300⟩

/-! ## 8–9.  Killed-architecture fixtures -/

/-- The `20 → 19` fixture and its consequence: no universal multiplicative drop. -/
theorem regression_no_fixed_ratio :
    (19 : ℚ) = (1 - 1 / 20) * 20 ∧ ∀ eta : ℚ, 1 / 20 < eta → ¬ ((19 : ℚ) ≤ (1 - eta) * 20) :=
  ⟨height_drop_20_19, no_universal_height_ratio⟩

/-- Primorial local-factor cancellation at `λ = 3`. -/
theorem regression_primorial_cancellation :
    (1 - 1 / (3 : ℚ)) * ((3 : ℚ) / ((3 : ℚ) - 1)) = 1 :=
  primorial_cancellation_fixture

end Regressions
end ResearchBankV5
end Erdos287
