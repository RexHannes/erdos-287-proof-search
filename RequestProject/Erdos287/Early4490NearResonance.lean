import Mathlib
import RequestProject.Erdos287.ProperGammaOddConvolution

/-!
# Erdős #287 effectivity — the exact near-resonant odd divisor identity (§47)

```
NEAR-RESONANT DIVISOR IDENTITY : KERNEL-PROVED (exact algebraic identity)
GLOBAL NEAR-RESONANT SUM       : OPEN (no smallness inferred)
ERDŐS #287                     : OPEN
```

Reusing the banked odd-convolution weights `h_z`, `g_z` and the exact signed odd-count function
`ρ_odd(x) = ⌊(x+1)/2⌋ − x/2` of §38, the exact neighbourhood identity is, for odd `M ≥ 1` and
`−1 < δ < 1`,

    Σ_{d ∣ M} h_z(d) ρ_odd((M+δ)/d)
        = sgn⁺(δ)/2 · g_z(M) − (δ/2) Σ_{d ∣ M} h_z(d)/d,

with the strict convention `sgn⁺(δ) = 1` for `δ ≥ 0` and `−1` for `δ < 0`
(`nearResonance_identity`).  This is *only* an algebraic identity: the global near-resonant
aggregate remains `OPEN` and `nearResonance_no_smallness` records that nothing here bounds it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287
namespace Effectivity

/-! ## §47.1  The strict signed indicator -/

/-- `sgn⁺(δ) = 1` for `δ ≥ 0`, `−1` for `δ < 0` (strict convention, matching the endpoint
convention of the repository's sawtooth). -/
def sgnPlus (delta : ℚ) : ℚ := if 0 ≤ delta then 1 else -1

/-- **`rhoOdd_near_odd`.**  `KERNEL-PROVED`.  The exact local evaluation of the signed
odd-count function next to an odd integer: for odd `m` and `|e| < 1`,

    ρ_odd(m + e) = sgn⁺(e)/2 − e/2. -/
theorem rhoOdd_near_odd {m : ℕ} (hm : ¬ 2 ∣ m) {e : ℚ} (h1 : -1 < e) (h2 : e < 1) :
    rhoOdd ((m : ℚ) + e) = sgnPlus e / 2 - e / 2 := by
  obtain ⟨k, hk⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
  have hcast : ((m : ℚ) + e + 1) / 2 = ((k : ℤ) : ℚ) + 1 + e / 2 := by
    rw [hk]; push_cast; ring
  have hfloor : ⌊((m : ℚ) + e + 1) / 2⌋ = (k : ℤ) + 1 + ⌊e / 2⌋ := by
    rw [hcast, show ((k : ℤ) : ℚ) + 1 + e / 2 = (e / 2) + (((k : ℤ) + 1 : ℤ) : ℚ) by
      push_cast; ring, Int.floor_add_intCast]
    ring
  have hfl : ⌊e / 2⌋ = if 0 ≤ e then (0 : ℤ) else -1 := by
    by_cases he : 0 ≤ e
    · rw [if_pos he, Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    · push_neg at he
      rw [if_neg (not_le.2 he), Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
  rw [rhoOdd, hfloor, hfl, hk, sgnPlus]
  by_cases he : 0 ≤ e
  · rw [if_pos he, if_pos he]; push_cast; ring
  · rw [if_neg he, if_neg he]; push_cast; ring

/-! ## §47.2  The exact near-resonant identity -/

/-- **`sum_divisors_hz_odd`.**  `KERNEL-PROVED`.  For odd `M` the full divisor sum of `h_z` is
`g_z(M)`: every divisor is odd, so the odd support is inactive. -/
theorem sum_divisors_hz_odd (z : ℕ) {M : ℕ} (hM : 0 < M) (hodd : ¬ 2 ∣ M) :
    ∑ d ∈ M.divisors, hz z d = gz z M := by
  rw [← sum_divisors_hzRaw z hM]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdvd, -⟩ := Nat.mem_divisors.1 hd
  exact hz_of_odd (fun h2 => hodd (h2.trans hdvd))

/-- **`nearResonance_identity`.**  `KERNEL-PROVED`.  The exact near-resonant odd identity:
for odd `M ≥ 1` and `−1 < δ < 1`,

    Σ_{d ∣ M} h_z(d) ρ_odd((M+δ)/d) = sgn⁺(δ)/2 · g_z(M) − (δ/2) Σ_{d ∣ M} h_z(d)/d. -/
theorem nearResonance_identity (z : ℕ) {M : ℕ} (hM : 0 < M) (hodd : ¬ 2 ∣ M) {delta : ℚ}
    (h1 : -1 < delta) (h2 : delta < 1) :
    ∑ d ∈ M.divisors, hz z d * rhoOdd (((M : ℚ) + delta) / d)
      = sgnPlus delta / 2 * gz z M - delta / 2 * ∑ d ∈ M.divisors, hz z d / (d : ℚ) := by
  have hterm : ∀ d ∈ M.divisors,
      hz z d * rhoOdd (((M : ℚ) + delta) / d)
        = sgnPlus delta / 2 * hz z d - delta / 2 * (hz z d / (d : ℚ)) := by
    intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.1 hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd hM
    have hd0' : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd0
    have hd1 : (1 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd0
    obtain ⟨m, hm⟩ := hdvd
    have hmodd : ¬ 2 ∣ m := fun h => hodd (hm ▸ Dvd.dvd.mul_left h d)
    have harg : ((M : ℚ) + delta) / d = (m : ℚ) + delta / d := by
      rw [hm]; push_cast; field_simp
    have he1 : -1 < delta / (d : ℚ) := by
      rcases le_or_gt 0 delta with h | h
      · have : 0 ≤ delta / (d : ℚ) := div_nonneg h hd0'.le
        linarith
      · rw [lt_div_iff₀ hd0']
        nlinarith
    have he2 : delta / (d : ℚ) < 1 := by
      rcases le_or_gt 0 delta with h | h
      · rw [div_lt_one hd0']
        linarith
      · have : delta / (d : ℚ) < 0 := div_neg_of_neg_of_pos h hd0'
        linarith
    have hsgn : sgnPlus (delta / (d : ℚ)) = sgnPlus delta := by
      unfold sgnPlus
      by_cases hdel : 0 ≤ delta
      · rw [if_pos hdel, if_pos (div_nonneg hdel hd0'.le)]
      · push_neg at hdel
        rw [if_neg (not_le.2 hdel), if_neg (not_le.2 (div_neg_of_neg_of_pos hdel hd0'))]
    rw [harg, rhoOdd_near_odd hmodd he1 he2, hsgn]
    field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_divisors_hz_odd z hM hodd]

/-! ## §47.3  No smallness is inferred -/

/-- The (open) claim that the global near-resonant aggregate is small. -/
def NearResonantAggregateSmall (S bound : ℚ) : Prop := |S| < bound

/-- **`nearResonance_no_smallness`.**  `KERNEL-PROVED`.  The identity carries no smallness
information: the aggregate claim is a genuine proposition, false for concrete data, and
nothing above inhabits it. -/
theorem nearResonance_no_smallness : ¬ NearResonantAggregateSmall 1 (1 / 2) := by
  unfold NearResonantAggregateSmall
  norm_num

end Effectivity
end Erdos287
