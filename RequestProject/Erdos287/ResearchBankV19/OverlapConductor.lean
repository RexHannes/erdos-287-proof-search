import RequestProject.Erdos287.ResearchBankV19.PrimePowerCRT

/-!
# Erdős #287 — Research Bank V19 §4: overlap conductors

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Kernel-proved (LEAN BANK):
* `overlap_conductor_dvd` — in the overlap CRT reduction the primitive additive conductor of
  `h ↦ e_{[D,s]}(h Δ)` divides `D₁ / gcd(D₁, c)`, hence divides `D₁ = D / gcd(D, s)` and `D`;
* `prime_power_overlap` — for `β ≤ α`: `gcd(p^α, p^β) = p^β`, `D₁ = p^{α−β}`, `s₁ = 1`, so the
  whole CRT difference lives at the prime power `p^{α−β}`;
* `overlap_fixture` — `D = 27`, `s = 9`: `g = 9`, `D₁ = 3`, `s₁ = 1`.
-/

namespace Erdos287
namespace ResearchBankV19
namespace OverlapConductor

open ResearchBankV18.ColourConductor PrimePowerCRT

/-- The primitive conductor divides `D₁` and `D`. -/
theorem overlap_conductor_dvd {D s : ℕ} (hD : 0 < D) (c s1i : ℤ) {p₀ : ℕ} (hp₀ : 0 < p₀)
    (hper₀ : IsPeriod (fun h => e (D / Nat.gcd D s) (h * c * s1i)) p₀)
    (hmin : ∀ q, 0 < q → IsPeriod (fun h => e (D / Nat.gcd D s) (h * c * s1i)) q → p₀ ≤ q) :
    p₀ ∣ D / Nat.gcd D s ∧ p₀ ∣ D := by
  have hg := Nat.gcd_pos_of_pos_left s hD
  have hD1 : 0 < D / Nat.gcd D s := Nat.div_pos (Nat.le_of_dvd hD (Nat.gcd_dvd_left D s)) hg
  have h1 := conductor_dvd hD1 c s1i hp₀ hper₀ hmin
  have h2 : p₀ ∣ D / Nat.gcd D s := h1.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
  exact ⟨h2, h2.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left D s))⟩

/-- Prime-power overlap. -/
theorem prime_power_overlap {p α β : ℕ} (hp : 0 < p) (hβ : β ≤ α) :
    Nat.gcd (p ^ α) (p ^ β) = p ^ β ∧ p ^ α / Nat.gcd (p ^ α) (p ^ β) = p ^ (α - β) ∧
      p ^ β / Nat.gcd (p ^ α) (p ^ β) = 1 := by
  have hg : Nat.gcd (p ^ α) (p ^ β) = p ^ β := Nat.gcd_eq_right (pow_dvd_pow p hβ)
  refine ⟨hg, ?_, ?_⟩
  · rw [hg, Nat.pow_div hβ hp]
  · rw [hg, Nat.div_self (pow_pos hp _)]

theorem overlap_fixture :
    Nat.gcd 27 9 = 9 ∧ 27 / Nat.gcd 27 9 = 3 ∧ 9 / Nat.gcd 27 9 = 1 := by decide

end OverlapConductor
end ResearchBankV19
end Erdos287
