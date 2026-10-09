import RequestProject.Erdos287.ResearchBankV13.FiniteRepresentationModel
import RequestProject.Erdos287.Universal

/-!
# Erdős #287 — Research Bank V13 §19: the prime-layer lemma

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `L J = lcm(1, …, J)` (the project's `lcmUpto`), `A J = ∑_{j=1}^{J} L J / j`.
* `A_eq` — `(A J : ℚ) = L J · H_J` (every `L J / j` is exact).
* `C_le_A` — every subset numerator, hence the project's `C j` for `j ≤ J`, is `≤ A J`.
* **`primeLayer_exclusion`** — if `r` is prime, `M < (J+1) r` and `A J < r`, then no denominator
  of an exact representation (`Erdos287Counterexample`, endpoint `M = max A`) is divisible by
  `r`.  Proof route: the `r`-multiples in `[1, M]` are `r j` with `j ≤ J`; the top `r`-adic layer
  congruence (`topLayer_congruence`, via `primePower_window_exclusion`) forces `r` to divide the
  reduced numerator of `∑_{j ∈ S} 1/j` for a nonempty `S ⊆ {1..J}`; that numerator is
  `≤ A J < r`, a contradiction.  (This is the same `r`-adic argument as the prompt's skeleton —
  the negative `r`-adic valuation of the `r`-layer cannot cancel — executed through the already
  kernel-checked top-layer theorem.)
* Kernel values (`decide`): `L 2 = 2`, `A 2 = 3`, `L 5 = 60`, `A 5 = 137`, `L 10 = 2520`,
  `A 10 = 7381`.
-/

namespace Erdos287
namespace ResearchBankV13
namespace PrimeLayer

open FiniteRepresentationModel

/-- `L J = lcm(1, …, J)`. -/
def L (J : ℕ) : ℕ := lcmUpto J

/-- `A J = ∑_{j=1}^{J} L J / j`. -/
def A (J : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 J, L J / j

theorem L_2 : L 2 = 2 := by decide
theorem A_2 : A 2 = 3 := by decide
theorem L_5 : L 5 = 60 := by decide
theorem A_5 : A 5 = 137 := by decide
theorem L_10 : L 10 = 2520 := by decide
theorem A_10 : A 10 = 7381 := by decide

/-- `(A J : ℚ) = L J · H_J`. -/
theorem A_eq (J : ℕ) : (A J : ℚ) = L J * harmonic J := by
  unfold A
  rw [harmonic_eq_sum_Icc, Finset.mul_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
  rw [Nat.cast_div (show j ∣ L J from dvd_lcmUpto hj) (by exact_mod_cast (show j ≠ 0 by omega))]
  field_simp

/-- Every nonempty-subset numerator of `∑ 1/s`, `S ⊆ {1..J}`, is `≤ A J`. -/
theorem num_le_A {J : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 J) :
    (∑ s ∈ S, (1 : ℚ) / s).num ≤ (A J : ℤ) := by
  have h := numerator_le_lcm_mul_harmonic hS
  rw [← L, ← A_eq] at h
  exact_mod_cast h

/-- The project's exact maximal numerator `C J` is `≤ A J`. -/
theorem C_le_A (J : ℕ) : C J ≤ (A J : ℤ) := by
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · decide
  · obtain ⟨S, -, hS, hnum⟩ := C_attained J hJ
    rw [← hnum]; exact num_le_A hS

/-- **The prime-layer lemma.**  If `r` is prime, `M < (J+1) r` and `A J < r`, no denominator of
an exact representation with endpoint `M` is divisible by `r`. -/
theorem primeLayer_exclusion {Aset : Finset ℕ} (hA : Erdos287Counterexample Aset) {r J : ℕ}
    (hr : r.Prime) (hM : Aset.max' hA.nonempty < (J + 1) * r) (hAJ : A J < r) :
    ∀ a ∈ Aset, ¬ r ∣ a := by
  set M := Aset.max' hA.nonempty
  intro a ha hra
  obtain ⟨hapos, haM⟩ := mem_le_max hA ha
  have hrM : r ≤ M := le_trans (Nat.le_of_dvd hapos hra) haM
  have hj : M / r ≤ J := by
    have := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hM)
    omega
  have hC : C (M / r ^ 1) < (r : ℤ) := by
    rw [pow_one]
    calc C (M / r) ≤ C J := C_mono hj
      _ ≤ (A J : ℤ) := C_le_A J
      _ < r := by exact_mod_cast hAJ
  exact primePower_window_exclusion Aset M r 1 hr (fun b hb => (mem_le_max hA hb).1)
    (fun b hb => (mem_le_max hA hb).2) hA.sum_one le_rfl (by rw [pow_one]; exact hrM) hC a ha
    (by rw [pow_one]; exact hra)

/-- The `r`-multiples below `(J+1) r` are exactly `r j`, `1 ≤ j ≤ J` (the first step of the
skeleton, stated separately). -/
theorem r_multiples {r J a : ℕ} (ha : 0 < a) (haM : a < (J + 1) * r) (hra : r ∣ a) :
    ∃ j, 1 ≤ j ∧ j ≤ J ∧ a = r * j := by
  obtain ⟨j, rfl⟩ := hra
  refine ⟨j, ?_, ?_, rfl⟩
  · rcases Nat.eq_zero_or_pos j with rfl | h
    · simp at ha
    · exact h
  · by_contra h; push_neg at h
    have : (J + 1) * r ≤ r * j := by rw [mul_comm]; exact Nat.mul_le_mul_left _ h
    omega

/-- `gcd(r, L J) = 1` for a prime `r > J` (in particular for `r > A J ≥ J`). -/
theorem coprime_L {r J : ℕ} (hr : r.Prime) (hrJ : J < r) : Nat.Coprime r (L J) := by
  have hcop : Nat.Coprime r ((Finset.Icc 1 J).prod id) := by
    refine Nat.coprime_prod_right_iff.mpr fun j hj => ?_
    have hj' := Finset.mem_Icc.1 hj
    rw [Nat.Prime.coprime_iff_not_dvd hr]
    intro h; have := Nat.le_of_dvd (by simp; omega) h; simp at this; omega
  exact Nat.Coprime.coprime_dvd_right (Finset.lcm_dvd_prod _ id) hcop

end PrimeLayer
end ResearchBankV13
end Erdos287
