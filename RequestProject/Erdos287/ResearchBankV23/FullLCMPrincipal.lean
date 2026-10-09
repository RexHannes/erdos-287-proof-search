import RequestProject.Erdos287.ResearchBankV23.PrincipalCRTMeasure

/-!
# Erdős #287 — Research Bank V23 §2: the full-lcm principal modulus

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`fullLCM W0 s qs = lcm(W0, s, q₁, …, q_r)` — the COMPLETE modulus `L0` (shared primes counted
once).  Kernel-proved (LEAN BANK):
* `dvd_fullLCM`, `W0_dvd_fullLCM`, `s_dvd_fullLCM`, `q_dvd_fullLCM`, `fullLCM_pos`;
* **`principal_prob_fullLCM`** — the exact principal probability at the full lcm:
  `Prob_i(t ≡ t0 mod L0) = φ(A_i W0)/φ(A_i L0) · 1(gcd(A_i t0 + 1, A_i L0) = 1)`;
* **`principal_sum_fullLCM`** — summed against any test function over the compatible residues:
  `Li/φ(A W0) · Σ_{t0} Prob(t0) F(t0) = Li/φ(A L0) · Σ_{t0} 1(unit) F(t0)`.
-/

namespace Erdos287
namespace ResearchBankV23
namespace FullLCMPrincipal

open Finset PrincipalCRTMeasure

/-- `L0 = lcm(W0, s, q₁, …, q_r)`. -/
def fullLCM (W0 s : ℕ) (qs : List ℕ) : ℕ := (W0 :: s :: qs).foldr Nat.lcm 1

theorem dvd_foldr_lcm : ∀ (l : List ℕ), ∀ x ∈ l, x ∣ l.foldr Nat.lcm 1
  | [], x, hx => absurd hx (by simp)
  | a :: l, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Nat.dvd_lcm_left _ _
    · exact dvd_trans (dvd_foldr_lcm l x hx) (Nat.dvd_lcm_right _ _)

theorem foldr_lcm_pos : ∀ (l : List ℕ), (∀ x ∈ l, 0 < x) → 0 < l.foldr Nat.lcm 1
  | [], _ => one_pos
  | a :: l, h => Nat.lcm_pos (h a (by simp)) (foldr_lcm_pos l fun x hx => h x (by simp [hx]))

theorem dvd_fullLCM {W0 s : ℕ} {qs : List ℕ} {x : ℕ} (hx : x ∈ W0 :: s :: qs) :
    x ∣ fullLCM W0 s qs := dvd_foldr_lcm _ x hx

theorem W0_dvd_fullLCM (W0 s : ℕ) (qs : List ℕ) : W0 ∣ fullLCM W0 s qs :=
  dvd_fullLCM (by simp)

theorem s_dvd_fullLCM (W0 s : ℕ) (qs : List ℕ) : s ∣ fullLCM W0 s qs := dvd_fullLCM (by simp)

theorem q_dvd_fullLCM (W0 s : ℕ) {qs : List ℕ} {q : ℕ} (hq : q ∈ qs) : q ∣ fullLCM W0 s qs :=
  dvd_fullLCM (by simp [hq])

theorem fullLCM_pos {W0 s : ℕ} {qs : List ℕ} (hW : 0 < W0) (hs : 0 < s) (hq : ∀ q ∈ qs, 0 < q) :
    0 < fullLCM W0 s qs := by
  refine foldr_lcm_pos _ fun x hx => ?_
  rcases List.mem_cons.1 hx with rfl | hx
  · exact hW
  rcases List.mem_cons.1 hx with rfl | hx
  · exact hs
  · exact hq x hx

variable {A W0 s tW : ℕ} {qs : List ℕ}

/-- **The exact principal probability at the COMPLETE modulus `L0 = lcm(W0, s, q₁..q_r)`.** -/
theorem principal_prob_fullLCM (hA : 0 < A) (hW : 0 < W0) (hs : 0 < s) (hq : ∀ q ∈ qs, 0 < q)
    (hc : Nat.Coprime (A * tW + 1) (A * W0)) {t0 : ℕ} (ht0 : t0 < fullLCM W0 s qs)
    (hcompat : t0 ≡ tW [MOD W0]) :
    principalProb A W0 (fullLCM W0 s qs) tW t0 =
      (Nat.totient (A * W0) : ℝ) / Nat.totient (A * fullLCM W0 s qs) *
        (if Nat.gcd (A * t0 + 1) (A * fullLCM W0 s qs) = 1 then 1 else 0) :=
  principal_prob hA hW (fullLCM_pos hW hs hq) (W0_dvd_fullLCM W0 s qs) hc ht0 hcompat

/-- **Principal sums at the full lcm** (any test function `F`, compatible residues only). -/
theorem principal_sum_fullLCM (hA : 0 < A) (hW : 0 < W0) (hs : 0 < s) (hq : ∀ q ∈ qs, 0 < q)
    (hc : Nat.Coprime (A * tW + 1) (A * W0)) (Li : ℝ) (F : ℕ → ℝ) :
    Li / Nat.totient (A * W0) *
        ∑ t0 ∈ (range (fullLCM W0 s qs)).filter (· ≡ tW [MOD W0]),
          principalProb A W0 (fullLCM W0 s qs) tW t0 * F t0 =
      Li / Nat.totient (A * fullLCM W0 s qs) *
        ∑ t0 ∈ (range (fullLCM W0 s qs)).filter (· ≡ tW [MOD W0]),
          (if Nat.gcd (A * t0 + 1) (A * fullLCM W0 s qs) = 1 then 1 else 0) * F t0 := by
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun t0 ht0 => ?_
  rw [mem_filter, mem_range] at ht0
  rw [← mul_assoc, ← mul_assoc,
    principal_Li_identity hA hW (fullLCM_pos hW hs hq) (W0_dvd_fullLCM W0 s qs) hc ht0.1 ht0.2]

end FullLCMPrincipal
end ResearchBankV23
end Erdos287
