import Mathlib

/-!
# Erdős #287 — Research Bank V19 §7: the outer-cost ledger

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Kernel-proved (LEAN BANK):
* `sqrt_saving` — the source-to-discrepancy square root turns an energy saving `x^{−σ}` into
  `x^{−σ/2}`;
* `sigma_not_preserved` (REPAIRED / RETIRED claim "σ survives the square root") — for `x > 1`,
  `σ > 0`: `x^{−σ} < x^{−σ/2}`;
* `unweighted_divisor_sum_ge` / **`unweighted_divisor_sum_not_polylog`** — negative control:
  already for FIXED `J = 2`, `∑_{D≤Y} τ(D) ≥ Y` is NOT bounded by any `C (log Y)^k`; only the
  weighted sum `∑_{D≤Y} τ_J(D)/D` can be polylogarithmic;
* **`exponent_after_unweighted_sum`** — a fixed-`D` energy cost `D^p x^{−ε}`, followed by the
  square-root transfer and an UNWEIGHTED sum over `D ≤ x^{2δ}`, costs at most
  `x^{−(ε/2 − δ(2+p))}` (conservative exponent `ε/2 − δ(2+p)`);
* `E1_margin`, `E2_margin` — the latest rational margins `17/40000 > 0` and `13/30000 > 0`.  They
  are reproduced exactly by the conservative exponent at `(ε, δ, p) = (1/1000, 1/40000, 1)` (E1
  periodic-q model) and `(1/1000, 1/40000, 2/3)` (E2 monomial-colour model; `p = 2/3` is the
  `E^{2/3}` colour cost).  **Caveat:** these parameter triples are a reconstruction that reproduces
  the supplied margins; the triples themselves were not supplied.  These are LOCAL savings only.
-/

namespace Erdos287
namespace ResearchBankV19
namespace OuterCostLedger

/-- **Square-root transfer halves the saving.** -/
theorem sqrt_saving {x : ℝ} (hx : 0 < x) (σ : ℝ) :
    Real.sqrt (x ^ (-σ)) = x ^ (-σ / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]; ring_nf

/-- **`σ` is not preserved.** -/
theorem sigma_not_preserved {x σ : ℝ} (hx : 1 < x) (hσ : 0 < σ) : x ^ (-σ) < x ^ (-σ / 2) :=
  Real.rpow_lt_rpow_of_exponent_lt hx (by linarith)

/-- The unweighted divisor sum is at least `Y`. -/
theorem unweighted_divisor_sum_ge (Y : ℕ) :
    (Y : ℝ) ≤ ∑ D ∈ Finset.Icc 1 Y, ((Nat.divisors D).card : ℝ) := by
  have : ∀ D ∈ Finset.Icc 1 Y, (1 : ℝ) ≤ ((Nat.divisors D).card : ℝ) := by
    intro D hD
    have hD1 : 1 ≤ D := (Finset.mem_Icc.1 hD).1
    have : 0 < (Nat.divisors D).card :=
      Finset.card_pos.2 ⟨1, Nat.one_mem_divisors.2 (by omega)⟩
    exact_mod_cast this
  calc (Y : ℝ) = ∑ _D ∈ Finset.Icc 1 Y, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum this

/-- `Y` is not bounded by a polylogarithm. -/
theorem not_polylog : ¬ ∃ (C : ℝ) (k : ℕ), ∀ Y : ℕ, 2 ≤ Y → (Y : ℝ) ≤ C * Real.log Y ^ k := by
  rintro ⟨C, k, h⟩
  set C' := max C 1
  have hC' : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlo := (Real.isLittleO_pow_log_id_atTop (n := k)).def (c := 1 / (2 * C')) (by positivity)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 hlo
  set Y : ℕ := max (⌈X⌉₊) 2
  have hY2 : 2 ≤ Y := le_max_right _ _
  have hYX : X ≤ Y := (Nat.le_ceil X).trans (by exact_mod_cast le_max_left _ _)
  have hYpos : (0 : ℝ) < Y := by positivity
  have h1 := h Y hY2
  have h2 := hX Y hYX
  have hlog : 0 ≤ Real.log Y ^ k := pow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y))) _
  rw [Real.norm_of_nonneg hlog, id, Real.norm_of_nonneg hYpos.le] at h2
  have h3 : C * Real.log Y ^ k ≤ C' * Real.log Y ^ k :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hlog
  have h4 : C' * Real.log Y ^ k ≤ C' * (1 / (2 * C') * Y) := mul_le_mul_of_nonneg_left h2 hC'.le
  have h5 : C' * (1 / (2 * C') * Y) = Y / 2 := by field_simp
  linarith

/-- **Negative control: fixed `J` does NOT make the unweighted conductor sum polylogarithmic.** -/
theorem unweighted_divisor_sum_not_polylog :
    ¬ ∃ (C : ℝ) (k : ℕ), ∀ Y : ℕ, 2 ≤ Y →
      ∑ D ∈ Finset.Icc 1 Y, ((Nat.divisors D).card : ℝ) ≤ C * Real.log Y ^ k := by
  rintro ⟨C, k, h⟩
  exact not_polylog ⟨C, k, fun Y hY => (unweighted_divisor_sum_ge Y).trans (h Y hY)⟩

/-- The conservative exponent `ε/2 − δ(2+p)`. -/
noncomputable def conservativeExponent (ε δ p : ℝ) : ℝ := ε / 2 - δ * (2 + p)

/-- **Unweighted conductor sum after the square-root transfer.** -/
theorem exponent_after_unweighted_sum {x ε δ p : ℝ} (hx : 1 ≤ x) (hp : 0 ≤ p) :
    ∑ D ∈ Finset.Icc 1 ⌊x ^ (2 * δ)⌋₊, Real.sqrt ((D : ℝ) ^ p * x ^ (-ε)) ≤
      x ^ (-conservativeExponent ε δ p) := by
  have hx0 : 0 < x := by linarith
  have hY : (0 : ℝ) ≤ x ^ (2 * δ) := by positivity
  have hterm : ∀ D ∈ Finset.Icc 1 ⌊x ^ (2 * δ)⌋₊,
      Real.sqrt ((D : ℝ) ^ p * x ^ (-ε)) ≤ x ^ (δ * p - ε / 2) := by
    intro D hD
    obtain ⟨hD1, hD2⟩ := Finset.mem_Icc.1 hD
    have hDx : (D : ℝ) ≤ x ^ (2 * δ) := (Nat.le_floor_iff hY).1 hD2
    have hD0 : (0 : ℝ) ≤ D := by positivity
    rw [Real.sqrt_eq_rpow, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hD0,
      ← Real.rpow_mul hx0.le]
    have : (D : ℝ) ^ (p * (1 / 2)) ≤ (x ^ (2 * δ)) ^ (p * (1 / 2)) :=
      Real.rpow_le_rpow hD0 hDx (by positivity)
    rw [← Real.rpow_mul hx0.le] at this
    calc (D : ℝ) ^ (p * (1 / 2)) * x ^ (-ε * (1 / 2))
        ≤ x ^ (2 * δ * (p * (1 / 2))) * x ^ (-ε * (1 / 2)) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = x ^ (δ * p - ε / 2) := by rw [← Real.rpow_add hx0]; ring_nf
  calc ∑ D ∈ Finset.Icc 1 ⌊x ^ (2 * δ)⌋₊, Real.sqrt ((D : ℝ) ^ p * x ^ (-ε))
      ≤ ∑ _D ∈ Finset.Icc 1 ⌊x ^ (2 * δ)⌋₊, x ^ (δ * p - ε / 2) := Finset.sum_le_sum hterm
    _ = (⌊x ^ (2 * δ)⌋₊ : ℝ) * x ^ (δ * p - ε / 2) := by simp
    _ ≤ x ^ (2 * δ) * x ^ (δ * p - ε / 2) :=
        mul_le_mul_of_nonneg_right (Nat.floor_le hY) (by positivity)
    _ = x ^ (-conservativeExponent ε δ p) := by
        rw [← Real.rpow_add hx0]; unfold conservativeExponent; ring_nf

/-- **E1 periodic-q model: `17/40000 > 0`.** -/
theorem E1_margin : conservativeExponent (1 / 1000) (1 / 40000) 1 = 17 / 40000 ∧
    (0 : ℝ) < 17 / 40000 := by
  unfold conservativeExponent; constructor <;> norm_num

/-- **E2 monomial-colour model: `13/30000 > 0`.** -/
theorem E2_margin : conservativeExponent (1 / 1000) (1 / 40000) (2 / 3) = 13 / 30000 ∧
    (0 : ℝ) < 13 / 30000 := by
  unfold conservativeExponent; constructor <;> norm_num

end OuterCostLedger
end ResearchBankV19
end Erdos287
