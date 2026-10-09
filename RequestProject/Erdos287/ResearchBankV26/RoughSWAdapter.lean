import RequestProject.Erdos287.ResearchBankV26.RoughConvolution
import RequestProject.Erdos287.ResearchBankV25.Counterfixtures

/-!
# Erdős #287 — Research Bank V26 §4.2 + §4.4: truncated smooth-divisor tail and source types

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## §4.2  Truncated smooth-divisor tail

`R_z(n) = Σ_{d ∣ n} μ(d) H_z(d)` (V26 §4.1).  Truncating at `d ≤ y` leaves the error
`E_y(n) = Σ_{d ∣ n, d > y} μ(d) H_z(d)`.

**LEAN BANK.**
* `rough_truncation_split` — `R_z(n) = Σ_{d∣n, d≤y} μ(d)H_z(d) + E_y(n)` exactly;
* `truncation_error_le` — `Σ_{n ≤ N} |E_y(n)| ≤ N · Σ_{y < d ≤ N} H_z(d)/d`.  The count of
  multiples is `⌊N/d⌋ ≤ N/d`; NO extra `+1` per divisor is inserted.

**EXTERNAL PROVIDER.**
* `SmoothTailProvider` — the Rankin-type reciprocal tail
  `Σ_{d > y, P⁺(d) < z} 1/d ≤ exp(−(log log x)²) log^C x`.

**LEAN CONDITIONAL.**
* `truncation_error_conditional` — the absolute source error is at most
  `N · exp(−(log log x)²) log^C x`.

## §4.4  Source sequence types

`RoughMuSequence`, `RoughOneSequence`, `RoughLogSequence`, `ComplementaryDivisorBoundedSequence`
are concrete coefficient sequences.  One-boundedness (`OneBounded`), rough support
(`RoughSupported`), an SW property and an `L²` divisor bound are SEPARATE predicates.

**Firewall (LEAN BANK).**  `rough_does_not_imply_SW`: a one-bounded, rough-supported sequence
(the indicator of `{1}`) is NOT balanced modulo `3`; so no implication `rough ⟹ SW` exists.
-/

namespace Erdos287
namespace ResearchBankV26
namespace RoughSWAdapter

open Finset ArithmeticFunction RoughConvolution
open scoped ArithmeticFunction.Moebius

/-- The truncation error `E_y(n) = Σ_{d ∣ n, d > y} μ(d) H_z(d)`. -/
noncomputable def truncErr (z y n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => y < d), ((μ d * H z d : ℤ) : ℝ)

/-- **Exact truncation split** (LEAN BANK). -/
theorem rough_truncation_split (z y n : ℕ) :
    ((R z n : ℤ) : ℝ) = ∑ d ∈ n.divisors.filter (fun d => d ≤ y), ((μ d * H z d : ℤ) : ℝ) +
      truncErr z y n := by
  unfold truncErr
  rw [rough_one_identity_apply, Int.cast_sum]
  rw [← Finset.sum_filter_add_sum_filter_not n.divisors (fun d => d ≤ y)]
  congr 1
  refine Finset.sum_congr (by ext d; simp) fun _ _ => rfl

theorem H_nonneg_le_one (z d : ℕ) : 0 ≤ H z d ∧ H z d ≤ 1 := by
  unfold H; rw [primeIndicator_apply]; split_ifs <;> norm_num

/-- **Truncation error bound** (LEAN BANK): `Σ_{n ≤ N} |E_y(n)| ≤ N · Σ_{y<d≤N} H_z(d)/d`. -/
theorem truncation_error_le (z y N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, |truncErr z y n| ≤
      (N : ℝ) * ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => y < d), ((H z d : ℤ) : ℝ) / d := by
  have hterm : ∀ n, |truncErr z y n| ≤
      ∑ d ∈ n.divisors.filter (fun d => y < d), ((H z d : ℤ) : ℝ) := by
    intro n
    unfold truncErr
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ => ?_)
    rw [Int.cast_mul, abs_mul]
    have hμ : |((μ d : ℤ) : ℝ)| ≤ 1 := by
      have := abs_moebius_le_one (n := d)
      exact_mod_cast this
    have hH := H_nonneg_le_one z d
    have : |((H z d : ℤ) : ℝ)| = ((H z d : ℤ) : ℝ) := abs_of_nonneg (by exact_mod_cast hH.1)
    rw [this]
    calc |((μ d : ℤ) : ℝ)| * ((H z d : ℤ) : ℝ) ≤ 1 * ((H z d : ℤ) : ℝ) :=
          mul_le_mul_of_nonneg_right hμ (by exact_mod_cast hH.1)
      _ = _ := one_mul _
  have hswap : ∑ n ∈ Finset.Ioc 0 N, ∑ d ∈ n.divisors.filter (fun d => y < d),
      ((H z d : ℤ) : ℝ) = ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => y < d),
        ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => d ∣ n), ((H z d : ℤ) : ℝ) := by
    refine Finset.sum_comm' fun n d => ?_
    simp only [Finset.mem_Ioc, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h0, hN⟩, ⟨hdn, -⟩, hyd⟩
      exact ⟨⟨⟨h0, hN⟩, hdn⟩, ⟨Nat.pos_of_dvd_of_pos hdn h0, (Nat.le_of_dvd h0 hdn).trans hN⟩, hyd⟩
    · rintro ⟨⟨⟨h0, hN⟩, hdn⟩, -, hyd⟩
      exact ⟨⟨h0, hN⟩, ⟨hdn, by omega⟩, hyd⟩
  calc ∑ n ∈ Finset.Ioc 0 N, |truncErr z y n|
      ≤ ∑ n ∈ Finset.Ioc 0 N, ∑ d ∈ n.divisors.filter (fun d => y < d), ((H z d : ℤ) : ℝ) :=
        Finset.sum_le_sum fun n _ => hterm n
    _ = ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => y < d), ((H z d : ℤ) : ℝ) * ((N / d : ℕ) : ℝ) := by
        rw [hswap]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div, mul_comm]
    _ ≤ ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => y < d), ((H z d : ℤ) : ℝ) * ((N : ℝ) / d) :=
        Finset.sum_le_sum fun d _ =>
          mul_le_mul_of_nonneg_left Nat.cast_div_le (by exact_mod_cast (H_nonneg_le_one z d).1)
    _ = (N : ℝ) * ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => y < d), ((H z d : ℤ) : ℝ) / d := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => by ring

/-- **Rankin-type smooth tail** (EXTERNAL PROVIDER; never constructed).  Scale-indexed
parameters `z x, y x, N x`, fixed exponent `C`. -/
structure SmoothTailProvider (z y N : ℝ → ℕ) (C : ℝ) : Prop where
  tail : ∃ x0 : ℝ, ∀ x ≥ x0,
    ∑ d ∈ (Finset.Ioc 0 (N x)).filter (fun d => y x < d), ((H (z x) d : ℤ) : ℝ) / d ≤
      Real.exp (-(Real.log (Real.log x)) ^ 2) * Real.log x ^ C

/-- **Absolute truncation error** (LEAN CONDITIONAL on `SmoothTailProvider`). -/
theorem truncation_error_conditional {z y N : ℝ → ℕ} {C : ℝ} (P : SmoothTailProvider z y N C) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∑ n ∈ Finset.Ioc 0 (N x), |truncErr (z x) (y x) n| ≤
      (N x : ℝ) * (Real.exp (-(Real.log (Real.log x)) ^ 2) * Real.log x ^ C) := by
  obtain ⟨x0, hx0⟩ := P.tail
  exact ⟨x0, fun x hx => (truncation_error_le _ _ _).trans
    (mul_le_mul_of_nonneg_left (hx0 x hx) (Nat.cast_nonneg _))⟩

/-! ## §4.4 Source sequence types -/

/-- One-boundedness. -/
def OneBounded (c : ℕ → ℝ) : Prop := ∀ n, |c n| ≤ 1

/-- Rough support: `c(n) ≠ 0 ⟹ R_z(n) = 1`. -/
def RoughSupported (z : ℕ) (c : ℕ → ℝ) : Prop := ∀ n, c n ≠ 0 → R z n = 1

/-- `L²` complementary divisor bound with exponent `C`. -/
def L2DivisorBound (C : ℕ) (c : ℕ → ℝ) : Prop := ∀ n, |c n| ≤ ((n.divisors.card : ℝ)) ^ C

/-- `RoughMuSequence`: `μ(n) R_z(n) 1_{n ≤ y}`. -/
noncomputable def RoughMuSequence (z y : ℕ) (n : ℕ) : ℝ :=
  if n ≤ y then ((μ n * R z n : ℤ) : ℝ) else 0

/-- `RoughOneSequence`: `R_z(n) 1_{n ≤ N}`. -/
noncomputable def RoughOneSequence (z N : ℕ) (n : ℕ) : ℝ :=
  if n ≤ N then ((R z n : ℤ) : ℝ) else 0

/-- `RoughLogSequence`: `R_z(n) log n 1_{n ≤ N}`. -/
noncomputable def RoughLogSequence (z N : ℕ) (n : ℕ) : ℝ :=
  if n ≤ N then ((R z n : ℤ) : ℝ) * Real.log n else 0

/-- `ComplementaryDivisorBoundedSequence`: any coefficient with an `L²` divisor bound. -/
structure ComplementaryDivisorBoundedSequence (C : ℕ) where
  c : ℕ → ℝ
  bound : L2DivisorBound C c

theorem R_values (z n : ℕ) : R z n = 0 ∨ R z n = 1 := by
  unfold R; rw [primeIndicator_apply]; split_ifs <;> simp

theorem roughMu_oneBounded (z y : ℕ) : OneBounded (RoughMuSequence z y) := by
  intro n; unfold RoughMuSequence; split_ifs
  · rw [Int.cast_mul, abs_mul]
    have h1 : |((μ n : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := n)
    rcases R_values z n with h | h <;> simp [h, h1]
  · simp

theorem roughMu_roughSupported (z y : ℕ) : RoughSupported z (RoughMuSequence z y) := by
  intro n hn; unfold RoughMuSequence at hn; split_ifs at hn
  · rcases R_values z n with h | h
    · simp [h] at hn
    · exact h
  · exact absurd rfl hn

theorem roughOne_oneBounded (z N : ℕ) : OneBounded (RoughOneSequence z N) := by
  intro n; unfold RoughOneSequence; split_ifs
  · rcases R_values z n with h | h <;> simp [h]
  · simp

theorem roughOne_roughSupported (z N : ℕ) : RoughSupported z (RoughOneSequence z N) := by
  intro n hn; unfold RoughOneSequence at hn; split_ifs at hn
  · rcases R_values z n with h | h
    · simp [h] at hn
    · exact h
  · exact absurd rfl hn

theorem roughLog_roughSupported (z N : ℕ) : RoughSupported z (RoughLogSequence z N) := by
  intro n hn; unfold RoughLogSequence at hn; split_ifs at hn
  · rcases R_values z n with h | h
    · simp [h] at hn
    · exact h
  · exact absurd rfl hn

/-- The indicator of `{1}` as a complex sequence. -/
noncomputable def deltaOne (n : ℕ) : ℂ := if n = 1 then 1 else 0

/-- **Firewall: rough ⟹ SW is FALSE** (LEAN BANK).  `1_{n=1}` is one-bounded and supported on
`z`-rough integers for every `z`, but `Δ(3, 1) = 1 − 1/2 ≠ 0` on `[1, 6]`. -/
theorem rough_does_not_imply_SW (z : ℕ) :
    OneBounded (fun n => if n = 1 then (1 : ℝ) else 0) ∧
    RoughSupported z (fun n => if n = 1 then (1 : ℝ) else 0) ∧
    ¬ ResearchBankV25.Counterfixtures.Balanced 3 (Finset.Icc 1 6) deltaOne := by
  refine ⟨fun n => by beta_reduce; split_ifs <;> simp, fun n hn => ?_, fun h => ?_⟩
  · beta_reduce at hn
    split_ifs at hn with h1
    · subst h1; unfold R; rw [primeIndicator_apply]; simp
    · exact absurd rfl hn
  · have := h 1
    unfold ResearchBankV25.FixedResidueEnergy.Disc deltaOne at this
    simp_rw [← ite_and] at this
    rw [Finset.sum_boole, Finset.sum_boole, ResearchBankV25.Counterfixtures.totient_three] at this
    have e1 : ((Finset.Icc (1 : ℕ) 6).filter
        (fun n : ℕ => (n : ZMod 3) = ((1 : (ZMod 3)ˣ) : ZMod 3) ∧ n = 1)).card = 1 := by decide
    have e2 : ((Finset.Icc (1 : ℕ) 6).filter (fun n : ℕ => Nat.Coprime n 3 ∧ n = 1)).card = 1 := by
      decide
    rw [e1, e2] at this
    norm_num at this

end RoughSWAdapter
end ResearchBankV26
end Erdos287
