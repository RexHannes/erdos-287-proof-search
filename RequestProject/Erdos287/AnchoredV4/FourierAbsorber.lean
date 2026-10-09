import RequestProject.Erdos287.AnchoredV4.GuardedReservoir

/-!
# Anchored V4 — the exact guarded absorber

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The absorber has to produce an **exact** rational equality `∑_{n ∈ E} 1/n = Δ`, never an
approximate one and never a congruence.  This module separates the three genuinely different
ingredients and proves the deterministic ones.

1. **Lattice reduction** (`recipSum_eq_weightSum`, `exact_absorption_iff_weight_subsetSum`).
   If every reservoir denominator divides `P` and `Δ · P = k ∈ ℕ`, then
   `∑_{n ∈ E} 1/n = Δ` is *equivalent* to the integer subset-sum equation
   `∑_{n ∈ E} (P / n) = k`.  No analysis is involved.

2. **No wraparound** (`exact_absorption_of_congruence`).  A solution of the subset-sum equation
   *modulo* `Qm` is upgraded to an exact solution precisely when the total reservoir weight and
   the target are both `< Qm`.  This is the formal firewall against confusing
   `∑ 1/n = Δ` with a congruence.

3. **Fourier counting** (`fourier_count_identity`, `congCount_pos_of_dominance`).  The exact
   finite identity

   `∑_{j < Qm} (∏_{n ∈ R} (1 + ζ^{j w n})) · (ζ^{j k})⁻¹ = Qm · #{E ⊆ R : ∑_E w ≡ k (mod Qm)}`

   is proved here for an arbitrary primitive `Qm`-th root of unity `ζ`, and yields
   `congCount > 0` whenever the trivial frequency `j = 0` dominates the remaining spectrum.

The composite theorem `exact_absorption_of_fourier_dominance` has exactly these hypotheses and no
hidden analytic input; the *asymptotic supply* of reservoirs satisfying the dominance hypothesis
remains the OPEN owner `GUARDED_ABSORBER_ANALYTIC_SUPPLY` (see `OpenOwners.lean`).
-/

open scoped BigOperators
open Finset

namespace Erdos287
namespace AnchoredV4

/-! ## 1. Lattice reduction -/

/-- The integer weight of a reservoir denominator at common denominator `P`. -/
def weight (P n : ℕ) : ℕ := P / n

/-- With all denominators dividing `P`, the reciprocal sum is the weight sum divided by `P`. -/
theorem recipSum_eq_weightSum {P : ℕ} (hP : P ≠ 0) {E : Finset ℕ}
    (hE : ∀ n ∈ E, n ≠ 0 ∧ n ∣ P) :
    recipSum E = (∑ n ∈ E, (weight P n : ℚ)) / P := by
  rw [recipSum, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro n hn
  obtain ⟨hn0, hdvd⟩ := hE n hn
  obtain ⟨c, hc⟩ := hdvd
  have hw : weight P n = c := by
    rw [weight, hc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn0)]
  have hc0 : (c : ℚ) ≠ 0 := by
    intro h
    rw [Nat.cast_eq_zero] at h
    rw [h, Nat.mul_zero] at hc
    exact hP hc
  have hn0' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn0
  rw [hw, hc]
  push_cast
  field_simp

/-- **Exact absorption is an integer subset-sum problem.** -/
theorem exact_absorption_iff_weight_subsetSum {P k : ℕ} (hP : P ≠ 0) {R : Finset ℕ}
    (hR : ∀ n ∈ R, n ≠ 0 ∧ n ∣ P) {Δ : ℚ} (hΔ : Δ * P = k) :
    (∃ E ⊆ R, recipSum E = Δ) ↔ (∃ E ⊆ R, ∑ n ∈ E, weight P n = k) := by
  have hP' : (P : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hP
  constructor
  · rintro ⟨E, hE, hsum⟩
    refine ⟨E, hE, ?_⟩
    have := recipSum_eq_weightSum hP (fun n hn => hR n (hE hn))
    rw [hsum] at this
    have hq : (∑ n ∈ E, (weight P n : ℚ)) = (k : ℚ) := by
      field_simp at this
      rw [← this, hΔ]
    exact_mod_cast hq
  · rintro ⟨E, hE, hsum⟩
    refine ⟨E, hE, ?_⟩
    rw [recipSum_eq_weightSum hP (fun n hn => hR n (hE hn))]
    have : (∑ n ∈ E, (weight P n : ℚ)) = (k : ℚ) := by exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) hsum
    rw [this, ← hΔ]
    field_simp

/-! ## 2. Exact versus modular: the no-wraparound firewall -/

/-- **No wraparound.**  A congruence solution below the modulus is an exact solution.  This is the
only legitimate way to pass from a modular statement to the exact rational equality. -/
theorem exact_absorption_of_congruence {P k Qm : ℕ} (hP : P ≠ 0) {R : Finset ℕ}
    (hR : ∀ n ∈ R, n ≠ 0 ∧ n ∣ P) {Δ : ℚ} (hΔ : Δ * P = k)
    (hk : k < Qm) (hmass : ∑ n ∈ R, weight P n < Qm)
    (hcong : ∃ E ⊆ R, (∑ n ∈ E, weight P n) ≡ k [MOD Qm]) :
    ∃ E ⊆ R, recipSum E = Δ := by
  obtain ⟨E, hE, hc⟩ := hcong
  refine (exact_absorption_iff_weight_subsetSum hP hR hΔ).2 ⟨E, hE, ?_⟩
  have hle : ∑ n ∈ E, weight P n ≤ ∑ n ∈ R, weight P n :=
    Finset.sum_le_sum_of_subset hE
  have h1 : (∑ n ∈ E, weight P n) % Qm = ∑ n ∈ E, weight P n :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt hle hmass)
  have h2 : k % Qm = k := Nat.mod_eq_of_lt hk
  rw [Nat.ModEq, h1, h2] at hc
  exact hc

/-! ## 3. The exact finite Fourier identity -/

variable {Qm : ℕ} {ζ : ℂ}

private lemma pow_mod_eq (hζ : ζ ^ Qm = 1) (s : ℕ) : ζ ^ s = ζ ^ (s % Qm) := by
  conv_lhs => rw [← Nat.div_add_mod s Qm]
  rw [pow_add, pow_mul, hζ, one_pow, one_mul]

/-- Exponents of a primitive root are determined modulo the order. -/
theorem pow_eq_pow_iff_modEq (hζ : IsPrimitiveRoot ζ Qm) (hQ : 0 < Qm) (s k : ℕ) :
    ζ ^ s = ζ ^ k ↔ s ≡ k [MOD Qm] := by
  constructor
  · intro h
    rw [pow_mod_eq hζ.pow_eq_one s, pow_mod_eq hζ.pow_eq_one k] at h
    exact hζ.pow_inj (Nat.mod_lt _ hQ) (Nat.mod_lt _ hQ) h
  · intro h
    rw [pow_mod_eq hζ.pow_eq_one s, pow_mod_eq hζ.pow_eq_one k, h]

/-- Orthogonality of the geometric sum of a `Qm`-th root of unity. -/
theorem geom_orthogonality (x : ℂ) (hx : x ^ Qm = 1) :
    ∑ j ∈ range Qm, x ^ j = if x = 1 then (Qm : ℂ) else 0 := by
  by_cases h : x = 1
  · simp [h]
  · rw [if_neg h, geom_sum_eq h, hx]; simp

/-- Expansion of the absorber generating product over all subsets. -/
theorem prod_one_add_pow (R : Finset ℕ) (w : ℕ → ℕ) (z : ℂ) :
    ∏ n ∈ R, (1 + z ^ (w n)) = ∑ E ∈ R.powerset, z ^ (∑ n ∈ E, w n) := by
  classical
  rw [show (fun n => 1 + z ^ w n) = (fun n => z ^ w n + 1) from funext fun n => add_comm _ _,
    Finset.prod_add]
  refine Finset.sum_congr rfl ?_
  intro E _
  rw [Finset.prod_pow_eq_pow_sum]
  simp

/-- The number of subsets of the reservoir whose weight sum hits the target modulo `Qm`. -/
def congCount (R : Finset ℕ) (w : ℕ → ℕ) (k Qm : ℕ) : ℕ :=
  (R.powerset.filter (fun E => (∑ n ∈ E, w n) ≡ k [MOD Qm])).card

/-- **Exact finite Fourier counting identity** for subset sums of the reservoir weights. -/
theorem fourier_count_identity (hζ : IsPrimitiveRoot ζ Qm) (hQ : 0 < Qm)
    (R : Finset ℕ) (w : ℕ → ℕ) (k : ℕ) :
    ∑ j ∈ range Qm, (∏ n ∈ R, (1 + ζ ^ (j * w n))) * (ζ ^ (j * k))⁻¹
      = Qm * (congCount R w k Qm : ℂ) := by
  classical
  have hζ0 : ζ ≠ 0 := by
    intro h
    have h1 := hζ.pow_eq_one
    rw [h, zero_pow (by omega)] at h1
    exact zero_ne_one h1
  have hz : ∀ m : ℕ, (ζ ^ m) ^ Qm = 1 := by
    intro m; rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have key : ∀ j ∈ range Qm, (∏ n ∈ R, (1 + ζ ^ (j * w n))) * (ζ ^ (j * k))⁻¹
      = ∑ E ∈ R.powerset, (ζ ^ (∑ n ∈ E, w n) * (ζ ^ k)⁻¹) ^ j := by
    intro j _
    have h1 : ∀ n, ζ ^ (j * w n) = (ζ ^ j) ^ (w n) := fun n => by rw [← pow_mul]
    simp only [h1]
    rw [prod_one_add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro E _
    have hterm : ∀ S : ℕ, ζ ^ (j * S) * (ζ ^ (j * k))⁻¹ = (ζ ^ S * (ζ ^ k)⁻¹) ^ j := by
      intro S
      rw [mul_pow, ← pow_mul, inv_pow, ← pow_mul, mul_comm S j, mul_comm k j]
    rw [← pow_mul]
    exact hterm _
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  have key2 : ∀ E ∈ R.powerset, ∑ j ∈ range Qm, (ζ ^ (∑ n ∈ E, w n) * (ζ ^ k)⁻¹) ^ j
      = if (∑ n ∈ E, w n) ≡ k [MOD Qm] then (Qm : ℂ) else 0 := by
    intro E _
    have hx : ((ζ ^ (∑ n ∈ E, w n)) * (ζ ^ k)⁻¹) ^ Qm = 1 := by
      rw [mul_pow, inv_pow, hz, hz, inv_one, mul_one]
    rw [geom_orthogonality _ hx]
    congr 1
    simp only [eq_iff_iff]
    rw [mul_inv_eq_one₀ (pow_ne_zero _ hζ0)]
    exact pow_eq_pow_iff_modEq hζ hQ _ _
  rw [Finset.sum_congr rfl key2, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
    add_zero, congCount, nsmul_eq_mul]
  ring

/-- **Dominance of the trivial frequency implies a congruence solution.**  If the `j = 0` term
`2 ^ |R|` strictly exceeds the total size of the remaining spectrum, the modular subset-sum
equation has a solution. -/
theorem congCount_pos_of_dominance (hζ : IsPrimitiveRoot ζ Qm) (hQ : 0 < Qm)
    (R : Finset ℕ) (w : ℕ → ℕ) (k : ℕ)
    (hdom : ∑ j ∈ Ico 1 Qm, ‖(∏ n ∈ R, (1 + ζ ^ (j * w n))) * (ζ ^ (j * k))⁻¹‖
      < 2 ^ R.card) :
    0 < congCount R w k Qm := by
  classical
  by_contra hcount
  have hzero : congCount R w k Qm = 0 := by omega
  have hid := fourier_count_identity hζ hQ R w k
  rw [hzero] at hid
  simp only [Nat.cast_zero, mul_zero] at hid
  have hsplit : ∑ j ∈ range Qm, (∏ n ∈ R, (1 + ζ ^ (j * w n))) * (ζ ^ (j * k))⁻¹
      = (∏ n ∈ R, (1 + ζ ^ (0 * w n))) * (ζ ^ (0 * k))⁻¹
        + ∑ j ∈ Ico 1 Qm, (∏ n ∈ R, (1 + ζ ^ (j * w n))) * (ζ ^ (j * k))⁻¹ := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hQ]
  have hzeroterm : (∏ n ∈ R, (1 + ζ ^ (0 * w n))) * (ζ ^ (0 * k))⁻¹ = 2 ^ R.card := by
    simp
    norm_num
  rw [hsplit, hzeroterm] at hid
  have hnorm : ‖(2 : ℂ) ^ R.card‖ ≤ ∑ j ∈ Ico 1 Qm,
      ‖(∏ n ∈ R, (1 + ζ ^ (j * w n))) * (ζ ^ (j * k))⁻¹‖ := by
    have : ((2 : ℂ) ^ R.card) = - ∑ j ∈ Ico 1 Qm,
        (∏ n ∈ R, (1 + ζ ^ (j * w n))) * (ζ ^ (j * k))⁻¹ := by linear_combination hid
    rw [this, norm_neg]
    exact norm_sum_le _ _
  rw [norm_pow] at hnorm
  simp only [Complex.norm_ofNat] at hnorm
  linarith

/-- **Exact absorption from Fourier dominance.**  Every analytic input is a visible hypothesis:
the lattice condition `Δ · P = k`, the divisibility of the reservoir denominators, the
no-wraparound bounds, and the spectral dominance inequality. -/
theorem exact_absorption_of_fourier_dominance {P k : ℕ} (hP : P ≠ 0) {R : Finset ℕ}
    (hR : ∀ n ∈ R, n ≠ 0 ∧ n ∣ P) {Δ : ℚ} (hΔ : Δ * P = k)
    (hζ : IsPrimitiveRoot ζ Qm) (hQ : 0 < Qm)
    (hk : k < Qm) (hmass : ∑ n ∈ R, weight P n < Qm)
    (hdom : ∑ j ∈ Ico 1 Qm, ‖(∏ n ∈ R, (1 + ζ ^ (j * weight P n))) * (ζ ^ (j * k))⁻¹‖
      < 2 ^ R.card) :
    ∃ E ⊆ R, recipSum E = Δ := by
  classical
  have hpos := congCount_pos_of_dominance hζ hQ R (weight P) k hdom
  have : ∃ E ∈ R.powerset.filter (fun E => (∑ n ∈ E, weight P n) ≡ k [MOD Qm]), True := by
    rcases Finset.card_pos.1 hpos with ⟨E, hE⟩
    exact ⟨E, hE, trivial⟩
  obtain ⟨E, hE, -⟩ := this
  rw [Finset.mem_filter, Finset.mem_powerset] at hE
  exact exact_absorption_of_congruence hP hR hΔ hk hmass ⟨E, hE.1, hE.2⟩

end AnchoredV4
end Erdos287
