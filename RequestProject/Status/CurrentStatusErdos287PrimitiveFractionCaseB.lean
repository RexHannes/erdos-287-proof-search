import Mathlib
import RequestProject.Status.CurrentStatusErdos287OneLevelMobius
import RequestProject.CurrentProgramme.OneLevelPrimitiveFractionSpacing
import RequestProject.CurrentProgramme.OneLevelCoefficientEnergy
import RequestProject.CurrentProgramme.OneLevelProjectorS1S2
import RequestProject.CurrentProgramme.OneLevelWeightedLargeSieve
import RequestProject.CurrentProgramme.OneLevelPrimitiveFractionGlobal

/-!
# Append-only status layer — Erdős #287, CASE-B ONE-LEVEL PRIMITIVE-FRACTION Δ

This module is **append-only**: `CurrentStatusErdos287OneLevelMobius` (and through it the
SHARED-`g₀`, PRIMITIVE-LOCALPROFILE and BLOCK20 ledgers) is imported and left untouched.

## What this delta certifies

The audit of §§2–10 of the CASE-B one-level primitive-fraction large sieve.  Each row of the
ledger is backed below by the literal kernel-checked statement it claims.

* `spacing45` — Section 2 is **unconditional**: `formalPassExact`.
* `dRestrictedLS45`, `coeffEnergy45`, `projectorS1S2_45`, `globalPrimitiveFraction45` — the
  reductions of Sections 3–8 are kernel-checked, but each carries its analytic or normalisation
  input as an *explicit hypothesis*: `formalPassConditional`.  Nothing here proves the classical
  separated-frequency large sieve, the reciprocal energy bound `E_g ≪ (gB+B²)L^{C_E}`, or the
  `Ω_H` normalisation.
* `omegaNormalisationPin`, `bPolynomialPin`, `gPolynomialPin` — **`sourcePinUnresolved`**.  The
  statements `supp Ω_H ⊆ {e ~ H}`, `|Ω_H| ≪ 1`, `∑|Ω_H(e)|/e ≪ 1`, `∑|Ω_H(e)|/e² ≪ 1/H`,
  `A ≥ X^{η_A}`, `B ≥ X^{η_B}`, `G > X^{1/2-η₀}` do **not** occur as theorems anywhere in this
  repository.  They are therefore not promoted; they enter only as hypotheses.
* `smallBObstruction`, `smallGObstruction` — `conditionalOnPin`, *not* closed: the closure
  mechanism (a fixed power of `L` is beaten by any positive power of `X`) is proved
  (`logPow_div_le_of_polynomial_lower`), but its input is an unresolved source pin.
* `primitiveFractionCritical45` — the unique first exact main-line residual, `hCriticalOpen`.
* `erdos287` — `open_`.  Nothing in this delta closes Erdős #287, and there is no `closed` row.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open ArithmeticFunction Filter

namespace Erdos287
namespace PrimitiveFractionCaseBStatus

open Erdos287.OneLevelSpacing
open Erdos287.OneLevelEnergy
open Erdos287.OneLevelProjector
open Erdos287.OneLevelWeightedLS
open Erdos287.OneLevelGlobal
open Erdos287.SharedGcdGram

/-! ## §11.1  The ledger -/

/-- The nodes of the CASE-B one-level primitive-fraction audit. -/
inductive Node
  | spacing45
  | dRestrictedLS45
  | coeffEnergy45
  | projectorS1S2_45
  | globalPrimitiveFraction45
  | normalisedRatio45
  | omegaNormalisationPin
  | bPolynomialPin
  | gPolynomialPin
  | smallBObstruction
  | smallGObstruction
  | primitiveFractionCritical45
  | uniformK0
  | fcl
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-- The status labels.  `closed` exists only so that "no closed row" is a statement about this
ledger; it is never used. -/
inductive Label
  | closed
  | formalPassExact
  | formalPassConditional
  | sourcePinUnresolved
  | conditionalOnPin
  | hCriticalOpen
  | notReached
  | open_
  deriving DecidableEq, Fintype, Repr

open Node Label

/-- The CASE-B one-level primitive-fraction ledger. -/
def ledger : Node → Label
  | spacing45 => formalPassExact
  | dRestrictedLS45 => formalPassConditional
  | coeffEnergy45 => formalPassConditional
  | projectorS1S2_45 => formalPassConditional
  | globalPrimitiveFraction45 => formalPassConditional
  | normalisedRatio45 => formalPassExact
  | omegaNormalisationPin => sourcePinUnresolved
  | bPolynomialPin => sourcePinUnresolved
  | gPolynomialPin => sourcePinUnresolved
  | smallBObstruction => conditionalOnPin
  | smallGObstruction => conditionalOnPin
  | primitiveFractionCritical45 => hCriticalOpen
  | uniformK0 => open_
  | fcl => notReached
  | erdos287 => open_

/-- The exact main-line residual order after this delta. -/
def residualRank : Node → ℕ
  | primitiveFractionCritical45 => 1
  | omegaNormalisationPin => 2
  | bPolynomialPin => 3
  | gPolynomialPin => 4
  | _ => 0

/-! ## §11.2  Ledger integrity -/

/-- **`no_closed_rows`.**  `LEAN_PROVED`. -/
theorem no_closed_rows : ∀ n : Node, ledger n ≠ closed := by decide +kernel

/-- **`erdos287_open`.**  `LEAN_PROVED`. -/
theorem erdos287_open : ledger erdos287 = open_ := by decide +kernel

/-- **`uniform_k0_open_fcl_not_reached`.**  `LEAN_PROVED`. -/
theorem uniform_k0_open_fcl_not_reached :
    ledger uniformK0 = open_ ∧ ledger fcl = notReached := by decide +kernel

/-- **`source_pins_unresolved`.**  `LEAN_PROVED`.

The three source pins are unresolved, and the two "small parameter" obstructions are therefore
*not* closed: they are conditional on the pins. -/
theorem source_pins_unresolved :
    ledger omegaNormalisationPin = sourcePinUnresolved ∧
      ledger bPolynomialPin = sourcePinUnresolved ∧
      ledger gPolynomialPin = sourcePinUnresolved ∧
      ledger smallBObstruction = conditionalOnPin ∧
      ledger smallGObstruction = conditionalOnPin ∧
      sourcePinUnresolved ≠ closed ∧ conditionalOnPin ≠ closed := by decide +kernel

/-- **`primitiveFractionCritical_is_first_exact_residual`.**  `LEAN_PROVED`. -/
theorem primitiveFractionCritical_is_first_exact_residual :
    ledger primitiveFractionCritical45 = hCriticalOpen ∧
      residualRank primitiveFractionCritical45 = 1 ∧
      (∀ n : Node, residualRank n = 1 → n = primitiveFractionCritical45) ∧
      hCriticalOpen ≠ closed := by decide +kernel

/-! ## §11.3  The `PASS` rows are backed by theorems -/

/-- **`spacing_row_is_a_theorem`.**  `LEAN_PROVED`.

Section 2, unconditional: injectivity of the primitive fractions with standard representatives,
and the `d/(4G²)` separation modulo one. -/
theorem spacing_row_is_a_theorem :
    ledger spacing45 = formalPassExact ∧
      (∀ d m1 m2 t1 t2 : ℕ, 0 < d → 0 < m1 → 0 < m2 → Nat.Coprime t1 m1 → Nat.Coprime t2 m2 →
        t1 < d * m1 → t2 < d * m2 → ∀ n : ℤ,
        (t1 : ℚ) / ((d * m1 : ℕ) : ℚ) - (t2 : ℚ) / ((d * m2 : ℕ) : ℚ) = (n : ℚ) →
        m1 = m2 ∧ t1 = t2) ∧
      (∀ d M m1 m2 : ℕ, 0 < d → 0 < M → 0 < m1 → 0 < m2 → m1 < 2 * M → m2 < 2 * M →
        ∀ t1 t2 n : ℤ,
        t1 * (m2 : ℤ) - t2 * (m1 : ℤ) - n * ((d * m1 * m2 : ℕ) : ℤ) ≠ 0 →
        (d : ℚ) / (4 * ((d * M : ℕ) : ℚ) ^ 2)
          ≤ |(t1 : ℚ) / ((d * m1 : ℕ) : ℚ) - (t2 : ℚ) / ((d * m2 : ℕ) : ℚ) - (n : ℚ)|) :=
  ⟨by decide +kernel,
    fun _ _ _ _ _ hd hm1 hm2 h1 h2 hlt1 hlt2 n heq =>
      primitiveFraction_inj hd hm1 hm2 h1 h2 hlt1 hlt2 n heq,
    fun _ _ _ _ hd hM hm1 hm2 h1 h2 t1 t2 n hne =>
      primitiveFraction_separation hd hM hm1 hm2 h1 h2 t1 t2 n hne⟩

/-- **`largeSieve_row_is_a_theorem`.**  `LEAN_PROVED`.

Section 3: the source weight is bounded (`0 ≤ ρ ≤ ‖V‖_∞`, no friability estimate needed), the
weighted sum is dominated by the unweighted one, and the Section 2 spacing gives the factor
`A + 4G²/d` with no logarithm. -/
theorem largeSieve_row_is_a_theorem :
    ledger dRestrictedLS45 = formalPassConditional ∧
      (∀ (Y : ℕ) (V : ℝ → ℝ) (Alen : ℝ) (a : ℕ), 0 ≤ rho Y V Alen a) ∧
      (∀ (Cv : ℝ), 0 ≤ Cv → ∀ (Y : ℕ) (V : ℝ → ℝ), (∀ x, |V x| ≤ Cv) →
        ∀ (Alen : ℝ) (a : ℕ), rho Y V Alen a ≤ Cv) ∧
      (∀ (Apts : Finset ℕ) (w : ℕ → ℝ) (S : ℕ → ℂ) (Cv : ℝ), (∀ a ∈ Apts, w a ≤ Cv) →
        ∑ a ∈ Apts, w a * ‖S a‖ ^ 2 ≤ Cv * ∑ a ∈ Apts, ‖S a‖ ^ 2) ∧
      (∀ Alen G d : ℝ, Alen + ((d / (4 * G ^ 2))⁻¹) = Alen + 4 * G ^ 2 / d) :=
  ⟨by decide +kernel,
    fun Y V Alen a => rho_nonneg Y V Alen a,
    fun _ hCv Y _ hV Alen a => rho_le hCv Y hV Alen a,
    fun Apts w S Cv h1 => weighted_sum_le_sup_mul Apts w S Cv h1,
    fun Alen G d => largeSieve_separation_factor Alen G d⟩

/-- **`coefficientEnergy_row_is_a_theorem`.**  `LEAN_PROVED`.

Section 4, with implied constant `1`: `∑_{M ≤ m < 2M} E_{dm}/m² ≤ dB(1+B/G)L`, `G = dM`, and the
two dyadic reciprocal sums that produce it. -/
theorem coefficientEnergy_row_is_a_theorem :
    ledger coeffEnergy45 = formalPassConditional ∧
      (∀ M : ℕ, 0 < M → ∑ m ∈ Finset.Ico M (2 * M), (1 : ℝ) / (m : ℝ) ≤ 1) ∧
      (∀ M : ℕ, 0 < M → ∑ m ∈ Finset.Ico M (2 * M), (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / (M : ℝ)) ∧
      (∀ (d M : ℕ), 0 < d → 0 < M → ∀ B L : ℝ, 0 ≤ B → 0 ≤ L → ∀ E : ℕ → ℝ,
        (∀ g, E g ≤ ((g : ℝ) * B + B ^ 2) * L) →
        ∑ m ∈ Finset.Ico M (2 * M), E (d * m) / (m : ℝ) ^ 2
          ≤ (d : ℝ) * B * (1 + B / ((d * M : ℕ) : ℝ)) * L) :=
  ⟨by decide +kernel,
    fun M hM => sum_inv_dyadic_le_one M hM,
    fun M hM => sum_inv_sq_dyadic_le M hM,
    fun _ _ hd hM B L hB hL E hE => coefficient_energy_bound hd hM B L hB hL E hE⟩

/-- **`projector_row_is_a_theorem`.**  `LEAN_PROVED`.

Section 6: `S1 ≤ c₁(1 + log⌊X/H⌋)` and `S2 ≤ 2c₁/H`, both for the *full* range `d ≤ X` — no
`d ~ H` assumption is used anywhere.  Both are conditional on the `Ω_H` support and mass
hypotheses, which are the unresolved source pin. -/
theorem projector_row_is_a_theorem :
    ledger projectorS1S2_45 = formalPassConditional ∧
      (∀ (Om : ℕ → ℝ) (H : ℕ), 0 < H → (∀ e, e < H → Om e = 0) → ∀ (X : ℕ) (c1 : ℝ),
        (∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ)) ≤ c1 →
        ∑ d ∈ Finset.Icc 1 X, |lambdaH Om d| / (d : ℝ)
          ≤ c1 * (1 + Real.log ((X / H : ℕ) : ℝ))) ∧
      (∀ (Om : ℕ → ℝ) (H X : ℕ), 0 < H → H ≤ X → (∀ e, e < H → Om e = 0) → ∀ c1 : ℝ,
        (∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ)) ≤ c1 →
        ∑ d ∈ Finset.Icc 1 X, |lambdaH Om d| / (d : ℝ)
          ≤ c1 * (1 + Real.log ((X : ℝ) / (H : ℝ)))) ∧
      (∀ (Om : ℕ → ℝ) (H : ℕ), 0 < H → (∀ e, e < H → Om e = 0) → ∀ (X : ℕ) (c1 : ℝ),
        (∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ)) ≤ c1 →
        ∑ d ∈ Finset.Icc 1 X, |lambdaH Om d| / (d : ℝ) ^ 2 ≤ 2 * c1 / (H : ℝ)) :=
  ⟨by decide +kernel,
    fun Om _ hH hsupp X c1 hmass => projector_S1_bound Om hH hsupp X c1 hmass,
    fun Om _ _ hH hHX hsupp c1 hmass => projector_S1_bound_real Om hH hHX hsupp c1 hmass,
    fun Om _ hH hsupp X c1 hmass => projector_S2_bound Om hH hsupp X c1 hmass⟩

/-- **`global_row_is_a_theorem`.**  `LEAN_PROVED`.

Sections 5 and 7: the fixed-`d` bound with all powers of `d` cancelling, and the global sharp
form together with its common-log envelope. -/
theorem global_row_is_a_theorem :
    ledger globalPrimitiveFraction45 = formalPassConditional ∧
      (∀ Alen G d K : ℝ, 0 < d →
        (Alen + 4 * G ^ 2 / d) * (d * K) = (Alen * d + 4 * G ^ 2) * K) ∧
      (∀ Gsum Alen G d Esum K : ℝ, 0 < d → 0 ≤ Alen →
        Gsum ≤ (Alen + 4 * G ^ 2 / d) * Esum → Esum ≤ d * K →
        Gsum ≤ (Alen * d + 4 * G ^ 2) * K) ∧
      (∀ (X H : ℕ), 0 < H → ∀ (Om : ℕ → ℝ), (∀ e, e < H → Om e = 0) →
        ∀ (Gd : ℕ → ℝ) (Q Alen Gfreq K c1 : ℝ),
        |Q| ≤ ∑ d ∈ Finset.Icc 1 X, |lambdaH Om d| / (d : ℝ) ^ 2 * Gd d →
        (∀ d ∈ Finset.Icc 1 X, Gd d ≤ (Alen * (d : ℝ) + 4 * Gfreq ^ 2) * K) →
        0 ≤ K → 0 ≤ Alen →
        (∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ)) ≤ c1 →
        |Q| ≤ K * (Alen * (c1 * (1 + Real.log ((X / H : ℕ) : ℝ)))
              + 4 * Gfreq ^ 2 * (2 * c1 / H))) :=
  ⟨by decide +kernel,
    fun Alen G d K hd => fixedD_factor_identity Alen G d K hd,
    fun Gsum Alen G d Esum K hd hAlen hLS hE => fixedD_bound Gsum Alen G d Esum K hd hAlen hLS hE,
    fun _ _ hH Om hsupp Gd Q Alen Gfreq K c1 hQ hGd hK hAlen hmass =>
      global_QH_bound hH Om hsupp Gd Q Alen Gfreq K c1 hQ hGd hK hAlen hmass⟩

/-- **`normalisedRatio_row_is_a_theorem`.**  `LEAN_PROVED`.

Section 8: the exact four-term decomposition of `|Q_H|/(AB²)` with `X = AB`, and the two
Section 10 branch closures. -/
theorem normalisedRatio_row_is_a_theorem :
    ledger normalisedRatio45 = formalPassExact ∧
      (∀ Alen B Gfreq H X L1 L0 : ℝ, Alen ≠ 0 → B ≠ 0 → Gfreq ≠ 0 → H ≠ 0 → X = Alen * B →
        (B * (1 + B / Gfreq) * (Alen * L1 + Gfreq ^ 2 / H * L0)) / (Alen * B ^ 2)
          = L1 / B + L1 / Gfreq + L0 * Gfreq ^ 2 / (H * X) + L0 * Gfreq / (H * Alen)) ∧
      (∀ (Gfreq X H Lg : ℝ) (Ce K : ℕ), 1 ≤ Lg → 0 < X → 0 < Gfreq →
        (Gfreq ^ 2 / X) * Lg ^ (Ce + K) ≤ H →
        Lg ^ Ce * Gfreq ^ 2 / (H * X) ≤ 1 / Lg ^ K) ∧
      (∀ (Gfreq Alen H Lg : ℝ) (Ce K : ℕ), 1 ≤ Lg → 0 < Alen → 0 < Gfreq →
        (Gfreq / Alen) * Lg ^ (Ce + K) ≤ H →
        Lg ^ Ce * Gfreq / (H * Alen) ≤ 1 / Lg ^ K) :=
  ⟨by decide +kernel,
    fun Alen B Gfreq H X L1 L0 hA hB hG hH hX =>
      normalised_ratio_identity Alen B Gfreq H X L1 L0 hA hB hG hH hX,
    fun _ _ _ _ Ce K hLg hX hG hbig => branch_G2_over_HX_closes Ce K hLg hX hG hbig,
    fun _ _ _ _ Ce K hLg hA hG hbig => branch_G_over_HA_closes Ce K hLg hA hG hbig⟩

/-- **`small_parameter_rows_are_conditional`.**  `LEAN_PROVED`.

The mechanism behind "a polynomial lower bound beats every fixed power of `L`" is proved.  It
is *not* promoted to a closure: the polynomial lower bounds `B ≥ X^{η_B}` and `G > X^{1/2-η₀}`
are unresolved source pins, so both rows stay `conditionalOnPin`. -/
theorem small_parameter_rows_are_conditional :
    ledger smallBObstruction = conditionalOnPin ∧
      ledger smallGObstruction = conditionalOnPin ∧
      conditionalOnPin ≠ closed ∧
      (∀ (K : ℕ) (eta eps : ℝ), 0 < eta → 0 < eps →
        ∀ᶠ X : ℝ in atTop, ∀ B : ℝ, X ^ eta ≤ B → (Real.log X) ^ K / B ≤ eps) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    fun K _ _ heta heps => logPow_div_le_of_polynomial_lower K heta heps⟩

/-! ## §11.4  Historical ledgers preserved -/

/-- **`historical_status_preserved`.**  `LEAN_PROVED`.

The imported ONE-LEVEL MÖBIUS ledger — and, through it, the SHARED-`g₀`,
PRIMITIVE-LOCALPROFILE and BLOCK20 ledgers — is unmodified and still records no closed row. -/
theorem historical_status_preserved :
    Erdos287.OneLevelMobiusStatus.ledger Erdos287.OneLevelMobiusStatus.Node.erdos287
        = Erdos287.OneLevelMobiusStatus.Label.open_ ∧
      Erdos287.OneLevelMobiusStatus.ledger Erdos287.OneLevelMobiusStatus.Node.fcl
        = Erdos287.OneLevelMobiusStatus.Label.notReached ∧
      (∀ n : Erdos287.OneLevelMobiusStatus.Node,
        Erdos287.OneLevelMobiusStatus.ledger n ≠ Erdos287.OneLevelMobiusStatus.Label.closed) ∧
      (∀ n : Erdos287.SharedG0RepairStatus.Node,
        Erdos287.SharedG0RepairStatus.ledger n
          ≠ Erdos287.SharedG0RepairStatus.Label.closed) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_⟩
  · exact Erdos287.OneLevelMobiusStatus.no_closed_rows
  · exact Erdos287.SharedG0RepairStatus.no_closed_rows

end PrimitiveFractionCaseBStatus
end Erdos287
