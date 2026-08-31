import Mathlib
import RequestProject.CurrentProgramme.OneLevelPrimitiveFractionSpacing
import RequestProject.CurrentProgramme.OneLevelCoefficientEnergy

/-!
# §§3, 5 — The weighted `d`-restricted large sieve and the fixed-`d` bound

`CASE-B ONE-LEVEL PRIMITIVE-FRACTION LARGE SIEVE`, Sections 3 and 5.

## What is proved

* `rho_nonneg`, `rho_le` — the source weight `ρ(a) = 1_{P⁺(a) ≤ Y}·|V(a/A)|` satisfies
  `0 ≤ ρ(a) ≤ ‖V‖_∞`.  Only boundedness of `V` is used; **no friability estimate is needed**,
  and the friability indicator may be replaced by any `{0,1}`-valued function.
* `weighted_sum_le_sup_mul` — hence `∑_a ρ(a)|S(a)|² ≤ ‖ρ‖_∞ ∑_a |S(a)|²`: the weighted sieve
  reduces to the unweighted one over the containing interval.
* `largeSieve_separation_factor` — the arithmetic of the large-sieve factor: with the Section 2
  separation `δ = d/(4G²)` one has `1/δ = 4G²/d`, so the Montgomery–Vaughan factor is
  `(length) + 4G²/d`.  No logarithm and no `X^ε` enters this step.
* `weighted_dRestricted_largeSieve` — the weighted `d`-restricted bound, deduced from the
  unweighted separated-frequency inequality, which is carried as an explicit hypothesis
  (`hLS`).
* `fixedD_bound` — Section 5: feeding the Section 4 energy `∑_m E_{dm}/m² ≤ dB(1+B/G)L` into
  the sieve factor `A + 4G²/d` gives `(Ad + 4G²)·B(1+B/G)L`; **all powers of `d` cancel
  exactly**.

## Source firewall

The unweighted separated-frequency large sieve inequality itself is a classical analytic input
(Montgomery–Vaughan).  It is *not* formalised in this repository and is *not* asserted here: it
appears only as the hypothesis `hLS` of `weighted_dRestricted_largeSieve` and of `fixedD_bound`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace Erdos287
namespace OneLevelWeightedLS

/-! ## §3.1  The source weight is bounded -/

/-- The source weight `ρ(a) = 1_{P⁺(a) ≤ Y}·|V(a/A)|`. -/
noncomputable def rho (Y : ℕ) (V : ℝ → ℝ) (Alen : ℝ) (a : ℕ) : ℝ :=
  if (∀ p ∈ a.primeFactors, p ≤ Y) then |V ((a : ℝ) / Alen)| else 0

/-- `0 ≤ ρ(a)`.  `LEAN_PROVED`. -/
theorem rho_nonneg (Y : ℕ) (V : ℝ → ℝ) (Alen : ℝ) (a : ℕ) : 0 ≤ rho Y V Alen a := by
  unfold rho
  split <;> positivity

/-- `ρ(a) ≤ ‖V‖_∞`.  `LEAN_PROVED`.  Only the bound on `V` is used: the friability cut is a
`{0,1}` factor and costs nothing. -/
theorem rho_le {Cv : ℝ} (hCv : 0 ≤ Cv) (Y : ℕ) {V : ℝ → ℝ} (hV : ∀ x, |V x| ≤ Cv)
    (Alen : ℝ) (a : ℕ) : rho Y V Alen a ≤ Cv := by
  unfold rho
  split
  · exact hV _
  · exact hCv

/-! ## §3.2  Weight domination -/

/-- **`DET1-ONELEVEL-dRESTRICTED-LS45`, weight domination.**  `LEAN_PROVED`.

`∑_a ρ(a)|S(a)|² ≤ ‖ρ‖_∞ ∑_a |S(a)|²`. -/
theorem weighted_sum_le_sup_mul {ι : Type*} (Apts : Finset ι) (w : ι → ℝ) (S : ι → ℂ)
    (Cv : ℝ) (h1 : ∀ a ∈ Apts, w a ≤ Cv) :
    ∑ a ∈ Apts, w a * ‖S a‖ ^ 2 ≤ Cv * ∑ a ∈ Apts, ‖S a‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun a ha => ?_)
  exact mul_le_mul_of_nonneg_right (h1 a ha) (by positivity)

/-! ## §3.3  The separation factor -/

/-- **The Montgomery–Vaughan factor for the Section 2 spacing.**  `LEAN_PROVED`.

With `δ = d/(4G²)` (Section 2) the large-sieve factor `(length) + δ⁻¹` is exactly
`(length) + 4G²/d`.  No logarithm and no `X^ε` appears. -/
theorem largeSieve_separation_factor (Alen G d : ℝ) :
    Alen + ((d / (4 * G ^ 2))⁻¹) = Alen + 4 * G ^ 2 / d := by
  rw [inv_div]

/-! ## §3.4  The weighted `d`-restricted large sieve -/

/-- **`DET1-ONELEVEL-dRESTRICTED-LS45`.**  `LEAN_PROVED` (conditional on the classical
separated-frequency large sieve, carried as `hLS`).

If the unweighted sieve over the containing interval obeys

```
∑_{a ∈ I} |S(a)|² ≤ (A + 4G²/d)·∑ |c|²,
```

then the `ρ`-weighted sum over any subfamily obeys the same bound with the extra factor
`‖ρ‖_∞`. -/
theorem weighted_dRestricted_largeSieve {ι : Type*} (Apts : Finset ι) (w : ι → ℝ) (S : ι → ℂ)
    (Cv Alen G d Esum : ℝ) (hCv : 0 ≤ Cv) (h1 : ∀ a ∈ Apts, w a ≤ Cv)
    (hLS : ∑ a ∈ Apts, ‖S a‖ ^ 2 ≤ (Alen + 4 * G ^ 2 / d) * Esum) :
    ∑ a ∈ Apts, w a * ‖S a‖ ^ 2 ≤ Cv * ((Alen + 4 * G ^ 2 / d) * Esum) := by
  refine le_trans (weighted_sum_le_sup_mul Apts w S Cv h1) ?_
  exact mul_le_mul_of_nonneg_left hLS hCv

/-! ## §5  The fixed-`d` bound -/

/-- **Fixed-`d` bound, Section 5.**  `LEAN_PROVED`.

`(A + 4G²/d)·(dB(1+B/G)L) = (Ad + 4G²)·B(1+B/G)L`: the powers of `d` cancel exactly. -/
theorem fixedD_factor_identity (Alen G d K : ℝ) (hd : 0 < d) :
    (Alen + 4 * G ^ 2 / d) * (d * K) = (Alen * d + 4 * G ^ 2) * K := by
  field_simp

/-- **`DET1-ONELEVEL-dRESTRICTED-LS45`, fixed-`d` form.**  `LEAN_PROVED`.

```
G_{H,d} ≤ (A + 4G²/d)·∑_m E_{dm}/m² ≤ (Ad + 4G²)·B(1+B/G)L.
```

`hLS` is the sieve step, `hE` the Section 4 energy bound. -/
theorem fixedD_bound (Gsum Alen G d Esum K : ℝ) (hd : 0 < d) (hAlen : 0 ≤ Alen)
    (hLS : Gsum ≤ (Alen + 4 * G ^ 2 / d) * Esum) (hE : Esum ≤ d * K) :
    Gsum ≤ (Alen * d + 4 * G ^ 2) * K := by
  have hfac : 0 ≤ Alen + 4 * G ^ 2 / d := by positivity
  calc Gsum ≤ (Alen + 4 * G ^ 2 / d) * Esum := hLS
    _ ≤ (Alen + 4 * G ^ 2 / d) * (d * K) := mul_le_mul_of_nonneg_left hE hfac
    _ = (Alen * d + 4 * G ^ 2) * K := fixedD_factor_identity Alen G d K hd

/-- **Fixed-`d` bound with the Section 4 energy inserted verbatim.**  `LEAN_PROVED`.

The composite statement `G_{H,d} ≤ (Ad + 4G²)·B(1+B/G)·L` with the energy sum taken literally
as `∑_{M ≤ m < 2M} E_{dm}/m²` and `G = dM`. -/
theorem fixedD_bound_with_energy {d M : ℕ} (hd : 0 < d) (hM : 0 < M) (B L Alen Gsum : ℝ)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hAlen : 0 ≤ Alen) (E : ℕ → ℝ)
    (hE : ∀ g, E g ≤ ((g : ℝ) * B + B ^ 2) * L)
    (hLS : Gsum ≤ (Alen + 4 * ((d * M : ℕ) : ℝ) ^ 2 / (d : ℝ)) *
      ∑ m ∈ Finset.Ico M (2 * M), E (d * m) / (m : ℝ) ^ 2) :
    Gsum ≤ (Alen * (d : ℝ) + 4 * ((d * M : ℕ) : ℝ) ^ 2) * (B * (1 + B / ((d * M : ℕ) : ℝ)) * L) :=
  fixedD_bound Gsum Alen ((d * M : ℕ) : ℝ) (d : ℝ)
    (∑ m ∈ Finset.Ico M (2 * M), E (d * m) / (m : ℝ) ^ 2)
    (B * (1 + B / ((d * M : ℕ) : ℝ)) * L)
    (by exact_mod_cast hd) hAlen
    hLS
    (by
      have := Erdos287.OneLevelEnergy.coefficient_energy_bound hd hM B L hB hL E hE
      calc ∑ m ∈ Finset.Ico M (2 * M), E (d * m) / (m : ℝ) ^ 2
          ≤ (d : ℝ) * B * (1 + B / ((d * M : ℕ) : ℝ)) * L := this
        _ = (d : ℝ) * (B * (1 + B / ((d * M : ℕ) : ℝ)) * L) := by ring)

end OneLevelWeightedLS
end Erdos287
