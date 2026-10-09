import Mathlib

/-!
# Erdős #287 — Research Bank V10 §D: Type-I `e`-rescaling (exact reproof)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The repaired Type-I change of variables, kernel-proved in its exact finite form:

* `rescale_product` — `M_e · N_e = M · N` for `M_e = M/e`, `N_e = e·N` (rational scale model);
* `betaE` — the transformed coefficient `β_e(v) = 1_{e ∣ v} β(v/e)`;
* `betaE_support` — support preservation: `β_e(v) ≠ 0 ⟺ v = e·w` with `β(w) ≠ 0`;
* `betaE_divisor_bound` — divisor-bound inheritance `|β| ≤ τ^k ⟹ |β_e| ≤ τ^k`;
* `betaE_sum` — the exact change-of-variable bijection `v = e·w` on `[1, eV] ↔ [1, V]`;
* `physical_product_preserved` — `(u/e)·(e·v) = u·v` together with the scale bounds;
* `reference_term_preserved` — the bilinear reference sum is unchanged by the rescaling;
* `lattice_card` / `lattice_density` — the `e`-lattice has exactly `X` points in `[1, eX]`;
* `lattice_congruence_iff`, `lattice_set_iff`, `lattice_sum` — the Poisson/lattice identity in its
  exact congruence form: `e ∣ ρ, ρ ≡ r (mod L)` ⟺ `ρ = e·u`, `u ≡ ē·r (mod L)` (`ē e ≡ 1 mod L`),
  with spacing `eL` (`lattice_spacing`, `lattice_translate`);
* `density_diagnostic_2_5_1` — the hostile fixture `e = 2, L = 5, r = 1`: forgetting `e ∣ ρ`
  doubles the density from `1/10` to `1/5`; `old_transform_rejected` fails if the old incorrect
  transformation is reintroduced.

No analytic Fourier transform is claimed: only the lattice and congruence statements are proved.
-/

namespace Erdos287
namespace ResearchBankV10
namespace TypeIRescaling

open Finset

/-! ## Scales -/

/-- **Scale invariant**: `M_e · N_e = M · N` for `M_e = M/e`, `N_e = e·N`, `e > 0`. -/
theorem rescale_product (M N : ℚ) {e : ℕ} (he : 0 < e) : (M / e) * (e * N) = M * N := by
  have : (e : ℚ) ≠ 0 := by exact_mod_cast he.ne'
  field_simp

/-! ## The transformed coefficient -/

/-- `β_e(v) = 1_{e ∣ v} β(v/e)`. -/
def betaE {R : Type*} [Zero R] (e : ℕ) (β : ℕ → R) (v : ℕ) : R :=
  if e ∣ v then β (v / e) else 0

theorem betaE_mul {R : Type*} [Zero R] {e : ℕ} (he : 0 < e) (β : ℕ → R) (w : ℕ) :
    betaE e β (e * w) = β w := by
  simp [betaE, Nat.mul_div_cancel_left w he]

theorem betaE_of_not_dvd {R : Type*} [Zero R] {e v : ℕ} (β : ℕ → R) (h : ¬ e ∣ v) :
    betaE e β v = 0 := by
  simp [betaE, h]

/-- **Support preservation.** -/
theorem betaE_support {R : Type*} [Zero R] {e : ℕ} (he : 0 < e) (β : ℕ → R) (v : ℕ) :
    betaE e β v ≠ 0 ↔ ∃ w, v = e * w ∧ β w ≠ 0 := by
  constructor
  · intro h
    unfold betaE at h
    split_ifs at h with hd
    · obtain ⟨w, rfl⟩ := hd
      exact ⟨w, rfl, by rwa [Nat.mul_div_cancel_left w he] at h⟩
    · exact absurd rfl h
  · rintro ⟨w, rfl, hw⟩
    rwa [betaE_mul he]

/-- **Divisor-bound inheritance**: `‖β(w)‖ ≤ τ(w)^k` for all `w ≥ 1` implies the same bound for
`β_e`. -/
theorem betaE_divisor_bound {e : ℕ} (he : 0 < e) (β : ℕ → ℂ) (k : ℕ)
    (hβ : ∀ w, 0 < w → ‖β w‖ ≤ ((Nat.divisors w).card : ℝ) ^ k) (v : ℕ) (hv : 0 < v) :
    ‖betaE e β v‖ ≤ ((Nat.divisors v).card : ℝ) ^ k := by
  unfold betaE
  split_ifs with hd
  · obtain ⟨w, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left w he]
    have hw : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h | h
      · simp [h] at hv
      · exact h
    refine (hβ w hw).trans ?_
    have hc : ((Nat.divisors w).card : ℝ) ≤ (Nat.divisors (e * w)).card := by
      exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hv.ne' (dvd_mul_left w e))
    exact pow_le_pow_left₀ (by positivity) hc k
  · simp only [norm_zero]; positivity

/-- **Exact change of variables** `v = e·w`: the `β_e`-weighted sum over `[1, eV]` equals the
`β`-weighted sum over `[1, V]` with the argument rescaled. -/
theorem betaE_sum {R : Type*} [CommSemiring R] {e : ℕ} (he : 0 < e) (β f : ℕ → R) (V : ℕ) :
    ∑ v ∈ Icc 1 (e * V), betaE e β v * f v = ∑ w ∈ Icc 1 V, β w * f (e * w) := by
  have h1 : ∑ v ∈ Icc 1 (e * V), betaE e β v * f v =
      ∑ v ∈ (Icc 1 (e * V)).filter (fun v => e ∣ v), β (v / e) * f v := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    unfold betaE; split_ifs <;> simp
  rw [h1]
  symm
  refine Finset.sum_nbij' (fun w => e * w) (fun v => v / e) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter, mem_Icc] at *
    exact ⟨⟨by nlinarith, by nlinarith⟩, dvd_mul_right _ _⟩
  · intro v hv
    simp only [mem_filter, mem_Icc] at *
    obtain ⟨⟨h1, h2⟩, w, rfl⟩ := hv
    rw [Nat.mul_div_cancel_left w he]
    constructor <;> nlinarith
  · intro w _; simp [Nat.mul_div_cancel_left w he]
  · intro v hv
    simp only [mem_filter] at hv
    exact Nat.mul_div_cancel' hv.2
  · intro w _; simp [Nat.mul_div_cancel_left w he]

/-! ## The physical product and the reference term -/

/-- **Physical product preservation**: for `e ∣ u`, the rescaled pair `(u/e, e·v)` has the same
product `u·v`, and it lies in the rescaled box `[0, M/e] × [0, eN]` whenever `(u, v)` lies in
`[0, M] × [0, N]`. -/
theorem physical_product_preserved {e u v : ℕ} (he : 0 < e) (hu : e ∣ u) {M N : ℚ}
    (huM : (u : ℚ) ≤ M) (hvN : (v : ℚ) ≤ N) :
    (u / e) * (e * v) = u * v ∧ ((u / e : ℕ) : ℚ) ≤ M / e ∧ ((e * v : ℕ) : ℚ) ≤ e * N := by
  obtain ⟨w, rfl⟩ := hu
  have he' : (0 : ℚ) < e := by exact_mod_cast he
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.mul_div_cancel_left w he]; ring
  · rw [Nat.mul_div_cancel_left w he, le_div_iff₀ he']
    push_cast at huM ⊢; linarith
  · push_cast; exact mul_le_mul_of_nonneg_left hvN he'.le

/-- **Reference-term preservation.**  The bilinear reference sum
`∑_{u ≤ U} ∑_{v ≤ eV} α(e u) β_e(v) Φ(u v)` of the rescaled problem equals the original
`∑_{u ≤ U} ∑_{w ≤ V} α(e u) β(w) Φ((e u) w)`, i.e. the physical products are unchanged. -/
theorem reference_term_preserved {R : Type*} [CommSemiring R] {e : ℕ} (he : 0 < e)
    (α β Φ : ℕ → R) (U V : ℕ) :
    ∑ u ∈ Icc 1 U, ∑ v ∈ Icc 1 (e * V), α (e * u) * (betaE e β v * Φ (u * v)) =
      ∑ u ∈ Icc 1 U, ∑ w ∈ Icc 1 V, α (e * u) * (β w * Φ ((e * u) * w)) := by
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  rw [betaE_sum he β (fun v => Φ (u * v)) V]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 2; ring

/-! ## The `e`-lattice density -/

/-- The `e`-lattice has exactly `X` points in `[1, eX]`. -/
theorem lattice_card {e : ℕ} (he : 0 < e) (X : ℕ) :
    ((Icc 1 (e * X)).filter (fun v => e ∣ v)).card = X := by
  have h := betaE_sum (R := ℕ) he (fun _ => 1) (fun _ => 1) X
  simp only [mul_one, sum_const, Nat.card_Icc, add_tsub_cancel_right, smul_eq_mul] at h
  calc ((Icc 1 (e * X)).filter (fun v => e ∣ v)).card
      = ∑ v ∈ Icc 1 (e * X), betaE e (fun _ => 1) v := by
        rw [card_eq_sum_ones, sum_filter]
        exact sum_congr rfl fun v _ => by unfold betaE; split_ifs <;> simp
    _ = X := h

/-- Density `1/e` of the `e`-lattice. -/
theorem lattice_density {e X : ℕ} (he : 0 < e) (hX : 0 < X) :
    (((Icc 1 (e * X)).filter (fun v => e ∣ v)).card : ℚ) / ((e * X : ℕ) : ℚ) = 1 / e := by
  rw [lattice_card he]
  have : (X : ℚ) ≠ 0 := by exact_mod_cast hX.ne'
  have : (e : ℚ) ≠ 0 := by exact_mod_cast he.ne'
  push_cast; field_simp

/-! ## The lattice / congruence identity -/

/-- **Congruence transfer**: if `e·ē ≡ 1 (mod L)`, then `e·u ≡ r (mod L) ⟺ u ≡ ē·r (mod L)`. -/
theorem lattice_congruence_iff {e ebar L : ℤ} (hinv : e * ebar ≡ 1 [ZMOD L]) (u r : ℤ) :
    e * u ≡ r [ZMOD L] ↔ u ≡ ebar * r [ZMOD L] := by
  constructor
  · intro h
    have h1 : ebar * (e * u) ≡ ebar * r [ZMOD L] := h.mul_left ebar
    have h2 : ebar * (e * u) ≡ u [ZMOD L] := by
      have := hinv.mul_right u
      rw [one_mul] at this
      calc ebar * (e * u) = e * ebar * u := by ring
        _ ≡ u [ZMOD L] := this
    exact h2.symm.trans h1
  · intro h
    have h1 : e * u ≡ e * (ebar * r) [ZMOD L] := h.mul_left e
    have h2 : e * (ebar * r) ≡ r [ZMOD L] := by
      have := hinv.mul_right r
      rw [one_mul] at this
      calc e * (ebar * r) = e * ebar * r := by ring
        _ ≡ r [ZMOD L] := this
    exact h1.trans h2

/-- The set description: `e ∣ ρ ∧ ρ ≡ r (mod L)` ⟺ `ρ = e·u` with `u ≡ ē·r (mod L)`. -/
theorem lattice_set_iff {e ebar L : ℤ} (hinv : e * ebar ≡ 1 [ZMOD L]) (ρ r : ℤ) :
    (e ∣ ρ ∧ ρ ≡ r [ZMOD L]) ↔ ∃ u, ρ = e * u ∧ u ≡ ebar * r [ZMOD L] := by
  constructor
  · rintro ⟨⟨u, rfl⟩, h⟩
    exact ⟨u, rfl, (lattice_congruence_iff hinv u r).1 h⟩
  · rintro ⟨u, rfl, h⟩
    exact ⟨dvd_mul_right _ _, (lattice_congruence_iff hinv u r).2 h⟩

/-- **Spacing `eL`**: two points of the lattice progression differ by a multiple of `eL`. -/
theorem lattice_spacing {e ebar L : ℤ} (hinv : e * ebar ≡ 1 [ZMOD L]) {ρ₁ ρ₂ r : ℤ}
    (h₁ : e ∣ ρ₁ ∧ ρ₁ ≡ r [ZMOD L]) (h₂ : e ∣ ρ₂ ∧ ρ₂ ≡ r [ZMOD L]) : e * L ∣ ρ₁ - ρ₂ := by
  obtain ⟨u₁, rfl, hu₁⟩ := (lattice_set_iff hinv ρ₁ r).1 h₁
  obtain ⟨u₂, rfl, hu₂⟩ := (lattice_set_iff hinv ρ₂ r).1 h₂
  have : L ∣ u₁ - u₂ := Int.ModEq.dvd (hu₂.trans hu₁.symm)
  rw [← mul_sub]
  exact mul_dvd_mul_left e this

/-- Conversely the progression is closed under translation by `eL`. -/
theorem lattice_translate {e L ρ r : ℤ} (h : e ∣ ρ ∧ ρ ≡ r [ZMOD L]) :
    e ∣ ρ + e * L ∧ ρ + e * L ≡ r [ZMOD L] := by
  refine ⟨dvd_add h.1 (dvd_mul_right _ _), ?_⟩
  have : ρ + e * L ≡ ρ [ZMOD L] := by
    rw [Int.modEq_iff_dvd]; exact ⟨-e, by ring⟩
  exact this.trans h.2

/-- **The lattice sum identity**: a sum over `ρ ∈ [0, e·U)` with `e ∣ ρ` and `ρ ≡ r (mod L)`
becomes a sum over `u ∈ [0, U)` with `u ≡ ē·r (mod L)` of `f(e·u)`. -/
theorem lattice_sum {R : Type*} [AddCommMonoid R] {e : ℕ} (he : 0 < e) {ebar L : ℤ}
    (hinv : (e : ℤ) * ebar ≡ 1 [ZMOD L]) (r : ℤ) (U : ℕ) (f : ℕ → R) :
    ∑ ρ ∈ (range (e * U)).filter (fun ρ : ℕ => e ∣ ρ ∧ (ρ : ℤ) ≡ r [ZMOD L]), f ρ =
      ∑ u ∈ (range U).filter (fun u : ℕ => (u : ℤ) ≡ ebar * r [ZMOD L]), f (e * u) := by
  symm
  refine Finset.sum_nbij' (fun u => e * u) (fun ρ => ρ / e) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [mem_filter, mem_range] at *
    refine ⟨by nlinarith [hu.1], dvd_mul_right _ _, ?_⟩
    push_cast
    exact (lattice_congruence_iff hinv u r).2 hu.2
  · intro ρ hρ
    simp only [mem_filter, mem_range] at *
    obtain ⟨h1, ⟨w, rfl⟩, h3⟩ := hρ
    rw [Nat.mul_div_cancel_left w he]
    refine ⟨by nlinarith, ?_⟩
    push_cast at h3
    exact (lattice_congruence_iff hinv w r).1 h3
  · intro u _; simp [Nat.mul_div_cancel_left u he]
  · intro ρ hρ
    simp only [mem_filter] at hρ
    exact Nat.mul_div_cancel' hρ.2.1
  · intro u _; rfl

/-! ## Hostile regression fixture: `e = 2, L = 5, r = 1` -/

/-- The correct rescaled progression `2 ∣ ρ, ρ ≡ 1 (mod 5)`: `1` point in `[0, 10)`. -/
theorem correct_count_2_5_1 :
    ((range 10).filter (fun ρ => 2 ∣ ρ ∧ ρ % 5 = 1)).card = 1 := by decide

/-- The *old incorrect* transformation forgets `e ∣ ρ`: `2` points in `[0, 10)`. -/
theorem old_count_2_5_1 : ((range 10).filter (fun ρ => ρ % 5 = 1)).card = 2 := by decide

/-- **Density diagnostic** `e = 2, L = 5, r = 1`: the correct density is `1/10`; forgetting
`e ∣ ρ` gives `1/5`, i.e. doubles it. -/
theorem density_diagnostic_2_5_1 :
    (((range 10).filter (fun ρ => 2 ∣ ρ ∧ ρ % 5 = 1)).card : ℚ) / 10 = 1 / 10 ∧
    (((range 10).filter (fun ρ => ρ % 5 = 1)).card : ℚ) / 10 = 1 / 5 ∧
    (((range 10).filter (fun ρ => ρ % 5 = 1)).card : ℚ) =
      2 * ((range 10).filter (fun ρ => 2 ∣ ρ ∧ ρ % 5 = 1)).card := by
  rw [correct_count_2_5_1, old_count_2_5_1]; norm_num

/-- **Regression firewall**: the old transformation (dropping `e ∣ ρ`) does not have the
density `1/(eL)` of the correct rescaled lattice. -/
theorem old_transform_rejected :
    (((range 10).filter (fun ρ => ρ % 5 = 1)).card : ℚ) / 10 ≠ 1 / (2 * 5) := by
  rw [old_count_2_5_1]; norm_num

end TypeIRescaling
end ResearchBankV10
end Erdos287
