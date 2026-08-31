import Mathlib
import RequestProject.CurrentProgramme.OneLevelPrimitiveFractionSpacing
import RequestProject.CurrentProgramme.OneLevelCoefficientEnergy
import RequestProject.CurrentProgramme.OneLevelProjectorS1S2
import RequestProject.CurrentProgramme.OneLevelWeightedLargeSieve
import RequestProject.CurrentProgramme.OneLevelPrimitiveFractionGlobal

/-!
# CASE-B primitive-fraction reproof bank — the additional exact statements

This module is an append-only *strengthening* layer over the banked CASE-B one-level
primitive-fraction package (`OneLevelPrimitiveFractionSpacing`, `OneLevelCoefficientEnergy`,
`OneLevelProjectorS1S2`, `OneLevelWeightedLargeSieve`, `OneLevelPrimitiveFractionGlobal`).
Nothing already banked is edited; the statements below are the four items of the reproof
report that were *not* previously available as literal Lean theorems.

* §A′ `separation_of_distinct_pairs` — the spacing statement in the form actually used by a
  large sieve: the hypothesis is that the two *pairs* `(m,t)` are distinct, not that a certain
  integral numerator is nonzero.  Injectivity of the standard representatives (which needs only
  `(t,m) = 1`, never `(t,dm) = 1`) is what converts one into the other.

* §B′ `caseB_pipeline_QH_bound` — the end-to-end composition
  `energy input → fixed-d bound → projector S1/S2 → global Q_H`, with the coefficient-energy
  bound inserted verbatim rather than as an abstract hypothesis `hGd`.  The only extra
  hypothesis is the (explicit) comparability `G ≤ M`, which is what lets the `d`-dependent
  energy denominator `dM` be replaced by the fixed frequency scale `G`.

* §D′ `normalised_ratio_le_of_comparable` — the source firewall `AB ≍ X` (rather than the
  normalisation `AB = X`) made explicit: with `c₀X ≤ AB` the four-term decomposition survives
  with the comparability constant restored on the `G²/(HX)` term only.

* §E′ `kappa_le_of_critical_range`, `kappa_le_eventually` — the exponential form of the CASE-B
  critical range.  From `X^κ ≤ L^K max(X^{2θ-1}, X^{θ-α})` one gets the *exact* inequality
  `κ ≤ max(2θ-1, θ-α) + K·log log X / log X`, and the correction term tends to `0`; this is the
  precise content of `κ ≤ max(0, 2θ-1, θ-α) + o(1)`.

No new analytic input is introduced: `hLS`, the energy bound `E_g ≤ (gB+B²)L^{C_E}` and the
`Ω_H` support/mass normalisation remain explicit hypotheses, exactly as in the banked layer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Filter

namespace Erdos287
namespace CaseBReproof

open Erdos287.OneLevelSpacing
open Erdos287.OneLevelProjector
open Erdos287.OneLevelWeightedLS
open Erdos287.OneLevelGlobal
open Erdos287.SharedGcdGram

/-! ## §A′  Spacing for distinct primitive pairs -/

/-- **`DET1-ONELEVEL-PRIMITIVEFRACTION-SPACING45`, pair form.**  `LEAN_PROVED` (unconditional).

If `(m₁,t₁) ≠ (m₂,t₂)` are two standard primitive representatives, `0 ≤ tᵢ < dmᵢ`,
`(tᵢ,mᵢ) = 1`, `mᵢ ∈ [M,2M)`, then modulo one

```
‖t₁/(dm₁) − t₂/(dm₂)‖ ≥ 1/(d m₁ m₂) ≥ d/(4G²),   G = dM.
```

Only `(t,m) = 1` is used; the stronger `(t,dm) = 1` is not needed. -/
theorem separation_of_distinct_pairs {d M m1 m2 t1 t2 : ℕ} (hd : 0 < d) (hM : 0 < M)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (h1 : m1 < 2 * M) (h2 : m2 < 2 * M)
    (hc1 : Nat.Coprime t1 m1) (hc2 : Nat.Coprime t2 m2)
    (hlt1 : t1 < d * m1) (hlt2 : t2 < d * m2) (hne : (m1, t1) ≠ (m2, t2)) (n : ℤ) :
    (d : ℚ) / (4 * ((d * M : ℕ) : ℚ) ^ 2)
      ≤ |(t1 : ℚ) / ((d * m1 : ℕ) : ℚ) - (t2 : ℚ) / ((d * m2 : ℕ) : ℚ) - (n : ℚ)| := by
  refine primitiveFraction_separation hd hM hm1 hm2 h1 h2 (t1 : ℤ) (t2 : ℤ) n ?_
  intro hzero
  have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hm1q : (0 : ℚ) < (m1 : ℚ) := by exact_mod_cast hm1
  have hm2q : (0 : ℚ) < (m2 : ℚ) := by exact_mod_cast hm2
  have hrepr : (t1 : ℚ) / ((d * m1 : ℕ) : ℚ) - (t2 : ℚ) / ((d * m2 : ℕ) : ℚ) - (n : ℚ)
      = ((((t1 : ℤ) * (m2 : ℤ) - (t2 : ℤ) * (m1 : ℤ)
            - n * ((d * m1 * m2 : ℕ) : ℤ) : ℤ)) : ℚ) / ((d * m1 * m2 : ℕ) : ℚ) := by
    push_cast
    field_simp
  rw [hzero] at hrepr
  simp only [Int.cast_zero, zero_div] at hrepr
  have hdiff : (t1 : ℚ) / ((d * m1 : ℕ) : ℚ) - (t2 : ℚ) / ((d * m2 : ℕ) : ℚ) = (n : ℚ) := by
    linarith
  obtain ⟨hme, hte⟩ := primitiveFraction_inj hd hm1 hm2 hc1 hc2 hlt1 hlt2 n hdiff
  exact hne (by rw [hme, hte])

/-! ## §B′  The end-to-end pipeline -/

/-- **CASE-B pipeline.**  `LEAN_PROVED` (conditional on the same explicit inputs as the banked
layer: the separated-frequency large sieve `hLS`, the energy input `hE`, and the `Ω_H`
support/mass normalisation `hsupp`, `hmass`).

Composing §4 (coefficient energy), §5 (fixed `d`) and §6 (`S1`, `S2`) gives the global bound

```
|Q_H| ≤ B(1+B/G)L · ( A c₁(1 + log⌊X/H⌋) + 8c₁G²/H ).
```

The hypothesis `G ≤ M` records that the fixed frequency scale is at most the dyadic scale, so
that the `d`-dependent energy denominator `dM` may be replaced by `G`. -/
theorem caseB_pipeline_QH_bound {X H M : ℕ} (hH : 0 < H) (hM : 0 < M)
    (Om E Gd : ℕ → ℝ) (hsupp : ∀ e, e < H → Om e = 0)
    (Q Alen Gfreq B L c1 : ℝ)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hAlen : 0 ≤ Alen) (hG : 0 < Gfreq) (hGM : Gfreq ≤ (M : ℝ))
    (hE : ∀ g, E g ≤ ((g : ℝ) * B + B ^ 2) * L)
    (hLS : ∀ d ∈ Finset.Icc 1 X, Gd d ≤ (Alen + 4 * Gfreq ^ 2 / (d : ℝ)) *
      ∑ m ∈ Finset.Ico M (2 * M), E (d * m) / (m : ℝ) ^ 2)
    (hQ : |Q| ≤ ∑ d ∈ Finset.Icc 1 X, |lambdaH Om d| / (d : ℝ) ^ 2 * Gd d)
    (hmass : ∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ) ≤ c1) :
    |Q| ≤ (B * (1 + B / Gfreq) * L) *
      (Alen * (c1 * (1 + Real.log ((X / H : ℕ) : ℝ))) + 4 * Gfreq ^ 2 * (2 * c1 / (H : ℝ))) := by
  have hfac : (0 : ℝ) ≤ 1 + B / Gfreq := by positivity
  have hK : (0 : ℝ) ≤ B * (1 + B / Gfreq) * L := by positivity
  refine global_QH_bound hH Om hsupp Gd Q Alen Gfreq (B * (1 + B / Gfreq) * L) c1 hQ ?_ hK hAlen
    hmass
  intro d hd
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hd0 : 0 < d := hd1
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have henergy := Erdos287.OneLevelEnergy.coefficient_energy_bound hd0 hM B L hB hL E hE
  have hGdM : Gfreq ≤ ((d * M : ℕ) : ℝ) := by
    have hdM : (M : ℝ) ≤ ((d * M : ℕ) : ℝ) := by
      have : M ≤ d * M := Nat.le_mul_of_pos_left M hd0
      exact_mod_cast this
    linarith
  have hdiv : B / ((d * M : ℕ) : ℝ) ≤ B / Gfreq := by
    apply div_le_div_of_nonneg_left hB hG hGdM
  have hcmp : (d : ℝ) * B * (1 + B / ((d * M : ℕ) : ℝ)) * L
      ≤ (d : ℝ) * (B * (1 + B / Gfreq) * L) := by
    have hstep : (d : ℝ) * B * (1 + B / ((d * M : ℕ) : ℝ)) * L
        ≤ (d : ℝ) * B * (1 + B / Gfreq) * L := by
      have hnn : (0 : ℝ) ≤ (d : ℝ) * B := by positivity
      nlinarith [mul_nonneg hnn hL]
    nlinarith [hstep]
  exact fixedD_bound (Gd d) Alen Gfreq (d : ℝ)
    (∑ m ∈ Finset.Ico M (2 * M), E (d * m) / (m : ℝ) ^ 2)
    (B * (1 + B / Gfreq) * L) hdR hAlen (hLS d hd) (le_trans henergy hcmp)

/-! ## §D′  The `AB ≍ X` source firewall -/

/-- **Normalised ratio under comparability.**  `LEAN_PROVED`.

The banked identity assumes the dyadic normalisation `X = AB`.  The programme bank only supplies
`AB ≍ X`; with the explicit lower comparability `c₀X ≤ AB` the four-term decomposition survives,
the constant appearing on the `G²/(HX)` term only:

```
|Q_H|/(AB²) ≤ L₁/B + L₁/G + L₀G²/(c₀HX) + L₀G/(HA).
``` -/
theorem normalised_ratio_le_of_comparable {Alen B Gfreq H X c0 L1 L0 : ℝ}
    (hA : 0 < Alen) (hB : 0 < B) (hG : 0 < Gfreq) (hH : 0 < H) (hX : 0 < X) (hc0 : 0 < c0)
    (hL0 : 0 ≤ L0) (hcomp : c0 * X ≤ Alen * B) :
    (B * (1 + B / Gfreq) * (Alen * L1 + Gfreq ^ 2 / H * L0)) / (Alen * B ^ 2)
      ≤ L1 / B + L1 / Gfreq + L0 * Gfreq ^ 2 / (H * (c0 * X)) + L0 * Gfreq / (H * Alen) := by
  have hid := normalised_ratio_identity Alen B Gfreq H (Alen * B) L1 L0 hA.ne' hB.ne' hG.ne'
    hH.ne' rfl
  rw [hid]
  have hterm : L0 * Gfreq ^ 2 / (H * (Alen * B)) ≤ L0 * Gfreq ^ 2 / (H * (c0 * X)) := by
    have hpos : (0 : ℝ) < H * (c0 * X) := by positivity
    have hnum : (0 : ℝ) ≤ L0 * Gfreq ^ 2 := by positivity
    apply div_le_div_of_nonneg_left hnum hpos
    exact mul_le_mul_of_nonneg_left hcomp hH.le
  linarith

/-! ## §E′  The exponential form of the critical range -/

/-- `max (X^a) (X^b) = X^{max a b}` for `X > 1`.  `LEAN_PROVED`. -/
theorem rpow_max_eq {X : ℝ} (hX : 1 < X) (a b : ℝ) :
    max (X ^ a) (X ^ b) = X ^ (max a b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right ((Real.rpow_le_rpow_left_iff hX).mpr h)]
  · rw [max_eq_left h, max_eq_left ((Real.rpow_le_rpow_left_iff hX).mpr h)]

/-- **CASE-B critical range, exponential form, exact.**  `LEAN_PROVED`.

If `H = X^κ`, `G = X^θ`, `A = X^α` and `H ≤ L^K·max(G²/X, G/A)`, then

```
κ ≤ max(2θ − 1, θ − α) + K·log log X / log X.
``` -/
theorem kappa_le_of_critical_range {theta alpha kappa X : ℝ} (K : ℕ) (hX : 1 < X)
    (h : X ^ kappa ≤ (Real.log X) ^ K * max (X ^ (2 * theta - 1)) (X ^ (theta - alpha))) :
    kappa ≤ max (2 * theta - 1) (theta - alpha)
      + (K : ℝ) * Real.log (Real.log X) / Real.log X := by
  have hX0 : (0 : ℝ) < X := lt_trans zero_lt_one hX
  have hlog : (0 : ℝ) < Real.log X := Real.log_pos hX
  rw [rpow_max_eq hX] at h
  have hlogle : Real.log (X ^ kappa)
      ≤ Real.log ((Real.log X) ^ K * X ^ (max (2 * theta - 1) (theta - alpha))) :=
    Real.log_le_log (Real.rpow_pos_of_pos hX0 _) h
  rw [Real.log_rpow hX0, Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_rpow hX0] at hlogle
  have hstep : kappa - max (2 * theta - 1) (theta - alpha)
      ≤ (K : ℝ) * Real.log (Real.log X) / Real.log X := by
    rw [le_div_iff₀ hlog]
    nlinarith [hlogle]
  linarith

/-- `log log X / log X → 0`.  `LEAN_PROVED`. -/
theorem loglog_div_log_tendsto_zero :
    Tendsto (fun X : ℝ => Real.log (Real.log X) / Real.log X) atTop (nhds 0) :=
  (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp Real.tendsto_log_atTop

/-- **CASE-B critical range, exponential form, `o(1)` version.**  `LEAN_PROVED`.

For every fixed logarithmic power `K` and every `ε > 0`, eventually in `X`:
`X^κ ≤ L^K·max(X^{2θ−1}, X^{θ−α})` forces `κ ≤ max(2θ−1, θ−α) + ε`.  Hence
`κ ≤ max(0, 2θ−1, θ−α) + o(1)`. -/
theorem kappa_le_eventually (K : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ X : ℝ in atTop, ∀ theta alpha kappa : ℝ,
      X ^ kappa ≤ (Real.log X) ^ K * max (X ^ (2 * theta - 1)) (X ^ (theta - alpha)) →
      kappa ≤ max (2 * theta - 1) (theta - alpha) + eps := by
  have hlim : Tendsto (fun X : ℝ => (K : ℝ) * (Real.log (Real.log X) / Real.log X)) atTop
      (nhds 0) := by
    simpa using loglog_div_log_tendsto_zero.const_mul (K : ℝ)
  have hev : ∀ᶠ X : ℝ in atTop,
      (K : ℝ) * (Real.log (Real.log X) / Real.log X) < eps :=
    hlim.eventually (eventually_lt_nhds heps)
  filter_upwards [hev, eventually_gt_atTop (1 : ℝ)] with X hXsmall hX1 theta alpha kappa hle
  have hmain := kappa_le_of_critical_range K hX1 hle
  rw [mul_div_assoc] at hmain
  linarith

/-- **The `max(0, ·)` form.**  `LEAN_PROVED`.  Weakening `max(2θ−1, θ−α)` to
`max(0, max(2θ−1, θ−α))` as in the banked statement of the critical exponent. -/
theorem kappa_le_max_zero (K : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ X : ℝ in atTop, ∀ theta alpha kappa : ℝ,
      X ^ kappa ≤ (Real.log X) ^ K * max (X ^ (2 * theta - 1)) (X ^ (theta - alpha)) →
      kappa ≤ max 0 (max (2 * theta - 1) (theta - alpha)) + eps := by
  filter_upwards [kappa_le_eventually K heps] with X hX theta alpha kappa hle
  have := hX theta alpha kappa hle
  have hmax : max (2 * theta - 1) (theta - alpha)
      ≤ max 0 (max (2 * theta - 1) (theta - alpha)) := le_max_right _ _
  linarith

/-! ## §A″  `S1` at the audited truncation `X = 2G` -/

/-- **`S1` at `X = 2G`.**  `LEAN_PROVED` (conditional on the `Ω_H` mass pin).

The banked form of the report's `S1 ≤ c₁(1 + log(2G/H))`. -/
theorem projector_S1_at_two_G (Om : ℕ → ℝ) {H Gnat : ℕ} (hH : 0 < H) (hHX : H ≤ 2 * Gnat)
    (hsupp : ∀ e, e < H → Om e = 0) (c1 : ℝ)
    (hmass : ∑ e ∈ Finset.Icc 1 (2 * Gnat), |Om e| / (e : ℝ) ≤ c1) :
    ∑ d ∈ Finset.Icc 1 (2 * Gnat), |lambdaH Om d| / (d : ℝ)
      ≤ c1 * (1 + Real.log (((2 * Gnat : ℕ) : ℝ) / (H : ℝ))) :=
  projector_S1_bound_real Om hH hHX hsupp c1 hmass

end CaseBReproof
end Erdos287
