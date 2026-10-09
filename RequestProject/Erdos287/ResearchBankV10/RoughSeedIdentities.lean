import Mathlib

/-!
# Erdős #287 — Research Bank V10 §N: rough HB seed identities

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Exact Dirichlet-convolution identities (Mathlib `ArithmeticFunction` API):

* `rough_eq_zeta_mul` — `ρ_z = 1 ⋆ (μ · 1_{P⁺ ≤ z})`;
* `moebius_rough_eq` — `μ ρ_z = μ ⋆ 1_{P⁺ ≤ z}`;

where `ρ_z(n) = 1` iff every prime factor of `n` exceeds `z` (`z`-rough), and `1_{P⁺ ≤ z}(n) = 1`
iff every prime factor of `n` is `≤ z` (`z`-smooth).  Both sides are multiplicative and agree on
prime powers.

* `rankin_split` — the elementary Rankin inequality used to split small/large smooth divisors:
  `∑_{d ∈ S, d > Y} a_d ≤ Y^{-σ} ∑_{d ∈ S} a_d d^σ` for `a ≥ 0`, `σ ≥ 0`, `Y > 0`;
* `RoughSeedSWProvider` — the genuinely analytic Siegel–Walfisz-type estimate for the rough seed,
  an explicit **hypothesis structure** (never inhabited here; Siegel–Walfisz is not proved).
-/

namespace Erdos287
namespace ResearchBankV10
namespace RoughSeedIdentities

open ArithmeticFunction Finset

/-- Indicator of "`n ≠ 0` and every prime factor satisfies `P`". -/
def primeInd (P : ℕ → Prop) [DecidablePred P] : ArithmeticFunction ℤ :=
  ⟨fun n => if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, P p then 1 else 0, by simp⟩

theorem primeInd_apply (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    primeInd P n = if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, P p then 1 else 0 := rfl

/-- `1_{P⁺ ≤ z}`: the `z`-smooth indicator. -/
def smoothInd (z : ℕ) : ArithmeticFunction ℤ := primeInd (· ≤ z)

/-- `ρ_z`: the `z`-rough indicator. -/
def roughInd (z : ℕ) : ArithmeticFunction ℤ := primeInd (z < ·)

theorem primeInd_isMultiplicative (P : ℕ → Prop) [DecidablePred P] :
    (primeInd P).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [primeInd_apply], ?_⟩
  intro m n hm hn _
  have key : (m * n ≠ 0 ∧ ∀ p ∈ (m * n).primeFactors, P p) ↔
      (m ≠ 0 ∧ ∀ p ∈ m.primeFactors, P p) ∧ (n ≠ 0 ∧ ∀ p ∈ n.primeFactors, P p) := by
    rw [Nat.primeFactors_mul hm hn]
    simp only [Finset.mem_union]
    constructor
    · rintro ⟨-, h⟩
      exact ⟨⟨hm, fun p hp => h p (Or.inl hp)⟩, ⟨hn, fun p hp => h p (Or.inr hp)⟩⟩
    · rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
      exact ⟨mul_ne_zero hm hn, fun p hp => hp.elim (h1 p) (h2 p)⟩
  rw [primeInd_apply, primeInd_apply, primeInd_apply]
  by_cases h1 : m ≠ 0 ∧ ∀ p ∈ m.primeFactors, P p <;>
    by_cases h2 : n ≠ 0 ∧ ∀ p ∈ n.primeFactors, P p
  · rw [if_pos (key.2 ⟨h1, h2⟩), if_pos h1, if_pos h2, mul_one]
  · rw [if_neg (fun h => h2 (key.1 h).2), if_pos h1, if_neg h2, mul_zero]
  · rw [if_neg (fun h => h1 (key.1 h).1), if_neg h1, zero_mul]
  · rw [if_neg (fun h => h1 (key.1 h).1), if_neg h1, zero_mul]

theorem primeInd_prime_pow (P : ℕ → Prop) [DecidablePred P] {p : ℕ} (hp : p.Prime) (i : ℕ) :
    primeInd P (p ^ i) = if i = 0 then 1 else if P p then 1 else 0 := by
  rw [primeInd_apply]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · rw [Nat.primeFactors_prime_pow hi.ne' hp]
    simp [hi.ne', hp.ne_zero]

theorem moebius_prime_pow_int {p : ℕ} (hp : p.Prime) (i : ℕ) :
    (moebius : ArithmeticFunction ℤ) (p ^ i) = if i = 0 then 1 else if i = 1 then -1 else 0 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · rw [if_neg hi.ne', moebius_apply_prime_pow hp hi.ne']

/-- **`ρ_z = 1 ⋆ (μ · 1_{P⁺ ≤ z})`.** -/
theorem rough_eq_zeta_mul (z : ℕ) :
    roughInd z = (zeta : ArithmeticFunction ℤ) * (moebius : ArithmeticFunction ℤ).pmul (smoothInd z) := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (primeInd_isMultiplicative _) _
    (isMultiplicative_zeta.natCast.mul (isMultiplicative_moebius.pmul
      (primeInd_isMultiplicative _)))).2 ?_
  intro p i hp
  rw [coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  simp only [pmul_apply, primeInd_prime_pow _ hp, moebius_prime_pow_int hp]
  rcases i with _ | m
  · simp
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have h0 : ∀ j ∈ range m, (if j + 1 + 1 = 0 then (1 : ℤ) else if j + 1 + 1 = 1 then -1 else 0) *
        (if j + 1 + 1 = 0 then 1 else if p ≤ z then 1 else 0) = 0 := by
      intro j _; simp
    rw [Finset.sum_eq_zero h0]
    by_cases hz : p ≤ z
    · simp [hz]
    · simp [hz, not_le.1 hz]

/-- **`μ ρ_z = μ ⋆ 1_{P⁺ ≤ z}`.** -/
theorem moebius_rough_eq (z : ℕ) :
    (moebius : ArithmeticFunction ℤ).pmul (roughInd z) =
      (moebius : ArithmeticFunction ℤ) * smoothInd z := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_moebius.pmul (primeInd_isMultiplicative _)) _
    (isMultiplicative_moebius.mul (primeInd_isMultiplicative _))).2 ?_
  intro p i hp
  rw [mul_apply]
  erw [Nat.sum_divisorsAntidiagonal (fun a b => (moebius : ArithmeticFunction ℤ) a *
    smoothInd z b)]
  rw [Nat.sum_divisors_prime_pow hp]
  have hdiv : ∀ j ∈ range (i + 1), p ^ i / p ^ j = p ^ (i - j) := by
    intro j hj
    exact Nat.pow_div (by simpa [Nat.lt_succ_iff] using hj) hp.pos
  rw [Finset.sum_congr rfl fun j hj => by rw [hdiv j hj]]
  simp only [pmul_apply, smoothInd, primeInd_prime_pow _ hp, moebius_prime_pow_int hp]
  rcases i with _ | m
  · simp
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have h0 : ∀ j ∈ range m, (if j + 1 + 1 = 0 then (1 : ℤ) else if j + 1 + 1 = 1 then -1 else 0) *
        (if m + 1 - (j + 1 + 1) = 0 then 1 else if p ≤ z then 1 else 0) = 0 := by
      intro j _; simp
    rw [Finset.sum_eq_zero h0]
    rcases m with _ | m
    · by_cases hz : p ≤ z
      · simp [hz]
      · simp [hz, not_le.1 hz]
    · by_cases hz : p ≤ z
      · simp [hz]
      · simp [hz]

/-- **Rankin's elementary split**: `∑_{d ∈ S, d > Y} a_d ≤ Y^{-σ} ∑_{d ∈ S} a_d d^σ`. -/
theorem rankin_split (S : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ d, 0 ≤ a d) {Y σ : ℝ} (hY : 0 < Y)
    (hσ : 0 ≤ σ) :
    ∑ d ∈ S.filter (fun d : ℕ => Y < (d : ℝ)), a d ≤ Y ^ (-σ) * ∑ d ∈ S, a d * (d : ℝ) ^ σ := by
  rw [Finset.mul_sum]
  calc ∑ d ∈ S.filter (fun d : ℕ => Y < (d : ℝ)), a d
      ≤ ∑ d ∈ S.filter (fun d : ℕ => Y < (d : ℝ)), Y ^ (-σ) * (a d * (d : ℝ) ^ σ) := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hYd : Y < d := (Finset.mem_filter.1 hd).2
        have h1 : 1 ≤ Y ^ (-σ) * (d : ℝ) ^ σ := by
          rw [Real.rpow_neg hY.le, ← div_eq_inv_mul, one_le_div (Real.rpow_pos_of_pos hY σ)]
          exact Real.rpow_le_rpow hY.le hYd.le hσ
        nlinarith [ha d]
    _ ≤ ∑ d ∈ S, Y ^ (-σ) * (a d * (d : ℝ) ^ σ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro d _ _
        have : 0 ≤ (d : ℝ) ^ σ := Real.rpow_nonneg (Nat.cast_nonneg d) σ
        have : 0 ≤ Y ^ (-σ) := Real.rpow_nonneg hY.le _
        have := ha d
        positivity

/-- **The rough-seed Siegel–Walfisz provider** (external, never inhabited here).  For the error
`Δ(q, a; X)` of the rough seed `μ ρ_z` in the progression `a (mod q)`, for every `A > 0` there is a
constant `C` such that `|Δ(q, a; X)| ≤ C · X (log X)^{-A}` for all `q ≤ (log X)^A`, `X ≥ 2`. -/
structure RoughSeedSWProvider (Δ : ℕ → ℤ → ℝ → ℝ) : Prop where
  bound : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ q : ℕ, ∀ a : ℤ, ∀ X : ℝ, 2 ≤ X →
    (q : ℝ) ≤ Real.log X ^ A → |Δ q a X| ≤ C * X * Real.log X ^ (-A)

/-- The provider is not vacuous: the zero error satisfies it. -/
theorem roughSeedSW_zero : RoughSeedSWProvider (fun _ _ _ => 0) :=
  ⟨fun _ _ => ⟨0, fun q a X _ _ => by simp⟩⟩

/-- The provider is not automatic: the error `Δ = X²` violates it. -/
theorem roughSeedSW_not_automatic : ¬ RoughSeedSWProvider (fun _ _ X => X ^ 2) := by
  intro ⟨h⟩
  obtain ⟨C, hC⟩ := h 1 one_pos
  -- choose X large: X² > C X (log X)^{-1} fails for large X
  set X : ℝ := max 3 (|C| + 3) with hXdef
  have hX3 : 3 ≤ X := le_max_left _ _
  have hXC : |C| + 3 ≤ X := le_max_right _ _
  have hlog : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hq : ((0 : ℕ) : ℝ) ≤ Real.log X ^ (1 : ℝ) := by
    rw [Real.rpow_one]; push_cast; linarith
  have h := hC 0 0 X (by linarith) hq
  rw [Real.rpow_neg_one] at h
  have hX0 : 0 < X := by linarith
  rw [abs_of_nonneg (by positivity)] at h
  have hinv : (Real.log X)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlog
  have : C * X * (Real.log X)⁻¹ ≤ |C| * X := by
    calc C * X * (Real.log X)⁻¹ ≤ |C| * X * (Real.log X)⁻¹ := by
          gcongr; exact le_abs_self C
      _ ≤ |C| * X * 1 := by gcongr
      _ = |C| * X := by ring
  nlinarith [abs_nonneg C]

end RoughSeedIdentities
end ResearchBankV10
end Erdos287
