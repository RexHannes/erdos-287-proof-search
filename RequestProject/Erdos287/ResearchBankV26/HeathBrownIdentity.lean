import Mathlib

/-!
# Erdős #287 — Research Bank V26 §4.3: the Heath-Brown identity

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Let `M_y(n) = μ(n) 1_{n ≤ y}` (real-valued arithmetic function).  All convolutions are Dirichlet
convolutions in the commutative ring `ArithmeticFunction ℝ`.

**LEAN BANK.**

* `hb_ring_identity` — for every `k`, the exact ring identity
  `Λ = (1 − 1⋆M_y)^k ⋆ Λ + Σ_{j<k} (−1)^j C(k, j+1) · (M_y^{⋆(j+1)} ⋆ 1^{⋆j} ⋆ log)`
  (binomial theorem + `Λ ⋆ 1 = log`);
* `one_sub_zeta_My` — `1 − 1⋆M_y = 1⋆(μ − M_y)`, a function supported on `n > y`;
* `pow_supported` — `(1⋆(μ − M_y))^{⋆k}` is supported on `n > y^k` (`k ≥ 1`, `y ≥ 0`);
* **`heath_brown_identity`** — for `n ≤ y^k` (`k ≥ 1`, `y ≥ 0`):

      Λ(n) = Σ_{j=1}^{k} (−1)^{j−1} C(k, j) (M_y^{⋆j} ⋆ 1^{⋆(j−1)} ⋆ log)(n)

  (written with `j ↦ j+1`, `j < k`);
* `heath_brown_k3` — the instance `k = 3`;
* `hb_k3_at_most_six_variables` — every `k = 3` term has `j + (j−1) + 1 ≤ 6` convolution
  factors; missing factors are the singleton sequence `{1}` (see `SingletonBins.lean`).

No requirement that any rough bin contain a value `> x^ν` is made.
-/

namespace Erdos287
namespace ResearchBankV26
namespace HeathBrownIdentity

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- `μ` as a real arithmetic function. -/
noncomputable abbrev muR : ArithmeticFunction ℝ := (μ : ArithmeticFunction ℝ)

/-- `1 = ζ` as a real arithmetic function. -/
noncomputable abbrev zetaR : ArithmeticFunction ℝ := (ζ : ArithmeticFunction ℝ)

/-- `M_y(n) = μ(n) 1_{n ≤ y}`. -/
noncomputable def My (y : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if (n : ℝ) ≤ y then ((μ n : ℤ) : ℝ) else 0, by simp⟩

theorem My_apply (y : ℝ) (n : ℕ) : My y n = if (n : ℝ) ≤ y then ((μ n : ℤ) : ℝ) else 0 := rfl

/-- The tail `μ − M_y`, supported on `n > y`. -/
noncomputable def Mb (y : ℝ) : ArithmeticFunction ℝ := muR - My y

theorem Mb_apply_ne_zero {y : ℝ} {n : ℕ} (h : Mb y n ≠ 0) : y < n := by
  unfold Mb at h
  rw [show (muR - My y) n = muR n - My y n from rfl, My_apply] at h
  by_contra hle
  push_neg at hle
  rw [if_pos hle] at h
  simp [muR, intCoe_apply] at h

/-- **`1 − 1⋆M_y = 1⋆(μ − M_y)`** (LEAN BANK). -/
theorem one_sub_zeta_My (y : ℝ) : 1 - zetaR * My y = zetaR * Mb y := by
  unfold Mb
  rw [mul_sub, mul_comm zetaR muR, coe_moebius_mul_coe_zeta]

/-- Support predicate: `F(n) ≠ 0 ⟹ a < n`. -/
def SupportedAbove (F : ArithmeticFunction ℝ) (a : ℝ) : Prop := ∀ n : ℕ, F n ≠ 0 → a < n

theorem supportedAbove_mul {F G : ArithmeticFunction ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hF : SupportedAbove F a) (hG : SupportedAbove G b) : SupportedAbove (F * G) (a * b) := by
  intro n hn
  rw [mul_apply] at hn
  obtain ⟨⟨d, e⟩, hde, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hd := hF d (left_ne_zero_of_mul hne)
  have he := hG e (right_ne_zero_of_mul hne)
  have hn' : d * e = n := (Nat.mem_divisorsAntidiagonal.1 hde).1
  rw [← hn']
  push_cast
  exact mul_lt_mul'' hd he ha hb

theorem zeta_Mb_supported {y : ℝ} : SupportedAbove (zetaR * Mb y) y := by
  intro n hn
  rw [coe_zeta_mul_apply] at hn
  obtain ⟨d, hd, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have := Mb_apply_ne_zero hne
  have hdn : d ≤ n := Nat.divisor_le hd
  exact lt_of_lt_of_le this (by exact_mod_cast hdn)

/-- **`(1⋆(μ − M_y))^{⋆k}` is supported on `n > y^k`** (LEAN BANK). -/
theorem pow_supported {y : ℝ} (hy : 0 ≤ y) :
    ∀ k : ℕ, 1 ≤ k → SupportedAbove ((zetaR * Mb y) ^ k) (y ^ k)
  | 0, h => absurd h (by norm_num)
  | 1, _ => by simpa using zeta_Mb_supported
  | k + 2, _ => by
    rw [pow_succ, pow_succ y]
    exact supportedAbove_mul (pow_nonneg hy _) hy (pow_supported hy (k + 1) (by omega))
      (zeta_Mb_supported)

theorem vanish_of_supported {G : ArithmeticFunction ℝ} {a : ℝ} (hG : SupportedAbove G a)
    (F : ArithmeticFunction ℝ) {n : ℕ} (hn : (n : ℝ) ≤ a) : (G * F) n = 0 := by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun ⟨d, e⟩ hde => ?_
  have hde' := Nat.mem_divisorsAntidiagonal.1 hde
  have hdn : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hde'.2) ⟨e, hde'.1.symm⟩
  by_contra hne
  have := hG d (left_ne_zero_of_mul hne)
  have : (d : ℝ) ≤ n := by exact_mod_cast hdn
  linarith

/-- Real scalars as arithmetic functions: `c ↦ c · δ₁`. -/
noncomputable def dlt : ℝ →+* ArithmeticFunction ℝ where
  toFun c := ⟨fun n => if n = 1 then c else 0, by simp⟩
  map_one' := by ext n; simp [one_apply]
  map_mul' a b := by
    ext n
    simp only [ArithmeticFunction.coe_mk, mul_apply]
    by_cases hn : n = 1
    · subst hn; simp
    · rw [if_neg hn]
      refine (Finset.sum_eq_zero fun ⟨d, e⟩ hde => ?_).symm
      have hde' := (Nat.mem_divisorsAntidiagonal.1 hde).1
      by_cases hd : d = 1
      · have he : e ≠ 1 := fun he => hn (by simp [hd, he] at hde'; omega)
        simp [he]
      · simp [hd]
  map_zero' := by ext n; simp
  map_add' a b := by ext n; simp only [ArithmeticFunction.coe_mk, add_apply]; split_ifs <;> simp

theorem dlt_mul_apply (c : ℝ) (F : ArithmeticFunction ℝ) (n : ℕ) : (dlt c * F) n = c * F n := by
  rw [mul_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [Finset.sum_eq_single (1, n)]
  · simp [dlt]
  · rintro ⟨d, e⟩ hde hne
    have hde' := (Nat.mem_divisorsAntidiagonal.1 hde).1
    have hd : d ≠ 1 := fun hd => hne (by rw [hd] at hde' ⊢; simp at hde'; rw [hde'])
    simp [dlt, hd]
  · intro h; exact absurd (Nat.mem_divisorsAntidiagonal.2 ⟨one_mul n, hn⟩) h

/-- The Heath-Brown term `M_y^{⋆(j+1)} ⋆ 1^{⋆j} ⋆ log`. -/
noncomputable def hbTerm (y : ℝ) (j : ℕ) : ArithmeticFunction ℝ := My y ^ (j + 1) * zetaR ^ j * log

/-- The HB coefficient `(−1)^j C(k, j+1)`. -/
def hbCoeff (k j : ℕ) : ℝ := (-1) ^ j * (k.choose (j + 1) : ℝ)

/-- **Heath-Brown ring identity** (LEAN BANK). -/
theorem hb_ring_identity (y : ℝ) (k : ℕ) :
    (vonMangoldt : ArithmeticFunction ℝ) = (1 - zetaR * My y) ^ k * vonMangoldt +
      ∑ j ∈ Finset.range k, dlt (hbCoeff k j) * hbTerm y j := by
  rw [sub_eq_neg_add, add_pow, Finset.sum_range_succ', add_mul, Finset.sum_mul,
    Nat.choose_zero_right]
  have key : ∑ j ∈ Finset.range k, (-(zetaR * My y)) ^ (j + 1) * 1 ^ (k - (j + 1)) *
      ((k.choose (j + 1) : ℕ) : ArithmeticFunction ℝ) * vonMangoldt +
      ∑ j ∈ Finset.range k, dlt (hbCoeff k j) * hbTerm y j = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    unfold hbCoeff hbTerm
    rw [map_mul, map_pow, map_neg, map_one, map_natCast, ← vonMangoldt_mul_zeta]
    ring
  linear_combination -key

/-- Evaluation at `n` as an additive map. -/
noncomputable def evalAt (n : ℕ) : ArithmeticFunction ℝ →+ ℝ where
  toFun F := F n
  map_zero' := rfl
  map_add' _ _ := add_apply

/-- **The Heath-Brown identity** (LEAN BANK): for `y ≥ 0`, `k ≥ 1` and `n ≤ y^k`,
`Λ(n) = Σ_{j<k} (−1)^j C(k, j+1) (M_y^{⋆(j+1)} ⋆ 1^{⋆j} ⋆ log)(n)`. -/
theorem heath_brown_identity {y : ℝ} (hy : 0 ≤ y) {k : ℕ} (hk : 1 ≤ k) {n : ℕ}
    (hn : (n : ℝ) ≤ y ^ k) :
    (vonMangoldt : ArithmeticFunction ℝ) n = ∑ j ∈ Finset.range k, hbCoeff k j * hbTerm y j n := by
  have h := congrArg (fun F : ArithmeticFunction ℝ => F n) (hb_ring_identity y k)
  simp only at h
  rw [h, add_apply, one_sub_zeta_My,
    vanish_of_supported (pow_supported hy k hk) _ hn, zero_add]
  have := map_sum (evalAt n) (fun j => dlt (hbCoeff k j) * hbTerm y j) (Finset.range k)
  simp only [evalAt, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  rw [this]
  exact Finset.sum_congr rfl fun j _ => dlt_mul_apply _ _ _

/-- **The `k = 3` instance** (LEAN BANK): for `n ≤ y³`,
`Λ(n) = 3 (M_y ⋆ log)(n) − 3 (M_y^{⋆2} ⋆ 1 ⋆ log)(n) + (M_y^{⋆3} ⋆ 1^{⋆2} ⋆ log)(n)`. -/
theorem heath_brown_k3 {y : ℝ} (hy : 0 ≤ y) {n : ℕ} (hn : (n : ℝ) ≤ y ^ 3) :
    (vonMangoldt : ArithmeticFunction ℝ) n =
      3 * hbTerm y 0 n - 3 * hbTerm y 1 n + hbTerm y 2 n := by
  rw [heath_brown_identity hy (by norm_num) hn]
  simp [Finset.sum_range_succ, hbCoeff]
  ring

/-- **At most six variables** (LEAN BANK): the `j`-th `k = 3` term has `j` Möbius factors,
`j − 1` constant factors and one `log` factor (here with `j ↦ j+1`). -/
theorem hb_k3_at_most_six_variables : ∀ j < 3, (j + 1) + j + 1 ≤ 6 := by decide

end HeathBrownIdentity
end ResearchBankV26
end Erdos287
