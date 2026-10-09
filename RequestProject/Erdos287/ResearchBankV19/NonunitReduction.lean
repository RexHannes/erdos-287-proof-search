import Mathlib

/-!
# Erdős #287 — Research Bank V19 §4: the nonunit coefficient congruence

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For `n m ≡ a (mod q)`, `q > 0`, `d = gcd(n, q)`:

Kernel-proved (LEAN BANK):
* `no_solution_of_not_dvd` — if `d ∤ a` there is no solution (the count is zero);
* `reduce_iff` — if `d ∣ a`: `n m ≡ a (mod q) ↔ (n/d) m ≡ a/d (mod q/d)`;
* `reduced_coprime` — `gcd(n/d, q/d) = 1`, i.e. the reduced congruence has a unit coefficient;
* `reduced_unit_solution` — so it has the unique-class solution `m ≡ (a/d) · (n/d)⁻¹ (mod q/d)`.
-/

namespace Erdos287
namespace ResearchBankV19
namespace NonunitReduction

/-- **No solution when `gcd(n, q) ∤ a`.** -/
theorem no_solution_of_not_dvd {n q a : ℤ} (h : ¬ (Int.gcd n q : ℤ) ∣ a) :
    ¬ ∃ m, n * m ≡ a [ZMOD q] := by
  rintro ⟨m, hm⟩
  apply h
  have h1 : (Int.gcd n q : ℤ) ∣ n * m := Dvd.dvd.mul_right (Int.gcd_dvd_left n q) _
  have h2 : (Int.gcd n q : ℤ) ∣ a - n * m :=
    (Int.gcd_dvd_right n q).trans (Int.modEq_iff_dvd.1 hm)
  have := dvd_add h2 h1
  simpa using this

/-- **Dividing out `d = gcd(n, q)`.** -/
theorem reduce_iff {n q a : ℤ} (hq : q ≠ 0) (hd : (Int.gcd n q : ℤ) ∣ a) (m : ℤ) :
    n * m ≡ a [ZMOD q] ↔
      (n / Int.gcd n q) * m ≡ a / Int.gcd n q [ZMOD q / Int.gcd n q] := by
  set d : ℤ := ((Int.gcd n q : ℕ) : ℤ)
  have hd0 : d ≠ 0 := by
    have : 0 < Int.gcd n q := Int.gcd_pos_of_ne_zero_right _ hq
    simp only [d]; exact_mod_cast this.ne'
  obtain ⟨n', hn⟩ : d ∣ n := Int.gcd_dvd_left n q
  obtain ⟨q', hq'⟩ : d ∣ q := Int.gcd_dvd_right n q
  obtain ⟨a', ha⟩ := hd
  have en : n / d = n' := by rw [hn, Int.mul_ediv_cancel_left _ hd0]
  have eq' : q / d = q' := by rw [hq', Int.mul_ediv_cancel_left _ hd0]
  have ea : a / d = a' := by rw [ha, Int.mul_ediv_cancel_left _ hd0]
  rw [en, eq', ea, Int.modEq_iff_dvd, Int.modEq_iff_dvd, hn, hq', ha]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, mul_left_cancel₀ hd0 (by linarith)⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [show d * a' - d * n' * m = d * (a' - n' * m) by ring, hk]; ring⟩

/-- **The reduced coefficient is a unit.** -/
theorem reduced_coprime {n q : ℤ} (hq : q ≠ 0) :
    IsCoprime (n / Int.gcd n q) (q / Int.gcd n q) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  exact Int.gcd_div_gcd_div_gcd (Int.gcd_pos_of_ne_zero_right _ hq)

/-- **The reduced congruence is solved by one residue class.** -/
theorem reduced_unit_solution {n' q' a' : ℤ} (hc : IsCoprime n' q') :
    ∃ i : ℤ, n' * i ≡ 1 [ZMOD q'] ∧ ∀ m, (n' * m ≡ a' [ZMOD q'] ↔ m ≡ a' * i [ZMOD q']) := by
  obtain ⟨u, v, huv⟩ := hc
  have hi : n' * u ≡ 1 [ZMOD q'] := Int.modEq_iff_dvd.2 ⟨v, by linarith⟩
  refine ⟨u, hi, fun m => ⟨fun h => ?_, fun h => ?_⟩⟩
  · calc m = m * 1 := by ring
      _ ≡ m * (n' * u) [ZMOD q'] := Int.ModEq.mul_left _ hi.symm
      _ = (n' * m) * u := by ring
      _ ≡ a' * u [ZMOD q'] := Int.ModEq.mul_right _ h
  · calc n' * m ≡ n' * (a' * u) [ZMOD q'] := Int.ModEq.mul_left _ h
      _ = a' * (n' * u) := by ring
      _ ≡ a' * 1 [ZMOD q'] := Int.ModEq.mul_left _ hi
      _ = a' := by ring

end NonunitReduction
end ResearchBankV19
end Erdos287
