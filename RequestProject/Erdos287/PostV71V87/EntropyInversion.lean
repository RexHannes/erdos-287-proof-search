import RequestProject.Erdos287.PostV71V87.ShellFingerprint
import RequestProject.Erdos287.PostV71V87.ReciprocalImageBound

/-!
# Erdős #287 — V87 entropy inequality (unconditional, from imported Chebyshev bounds)

* `shellPrimes_card_lower` — for `q ≥ q0`,
  `#{p prime : q/16 < p < q} ≥ q / (8 log q)`
  (lower bound from the central binomial coefficient, proved in `AnalyticToolkit`, upper bound
  from Mathlib's Chebyshev theorem);
* `entropy_inequality` — for every exact word with `a > 1` and `q_* ≥ q0`, with
  `H = ⌊16 M / q_*⌋`:

    `log q_* ≤ log 16 + log S_rec(H) + 2 log(H + 1)`.

  This combines the fingerprint/entropy core (`ExactWord.entropy_core`, `K = 16`) with the
  prime count.  No analytic hypothesis is assumed.
-/

open Real
open scoped BigOperators

namespace Erdos287.PostV71V87

/-- The shell primes `{p prime : p < q, q < K p}`. -/
def shellPrimes (K q : ℕ) : Finset ℕ := (Finset.range q).filter (fun p => p.Prime ∧ q < K * p)

theorem ExactWord.topShellPrimes_eq (W : ExactWord) (K : ℕ) :
    W.topShellPrimes K = shellPrimes K W.qstar := rfl

/-- `π(q - 1) ≤ #shellPrimes K q + π(q / K)`. -/
theorem shellPrimes_card_ge (K q : ℕ) (hK : 1 ≤ K) :
    Nat.primeCounting (q - 1) ≤ (shellPrimes K q).card + Nat.primeCounting (q / K) := by
  classical
  rw [Nat.primeCounting_sub_one, ← Nat.primesBelow_card_eq_primeCounting']
  have hsub : Nat.primesBelow q ⊆
      shellPrimes K q ∪ Nat.primesBelow (q / K + 1) := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    by_cases h : q < K * p
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 hp.1, hp.2, h⟩)
    · push_neg at h
      refine Finset.mem_union_right _ ?_
      rw [Nat.mem_primesBelow]
      refine ⟨?_, hp.2⟩
      have : p ≤ q / K := (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact h)
      omega
  have hc : (Nat.primesBelow (q / K + 1)).card = Nat.primeCounting (q / K) := by
    rw [Nat.primesBelow_card_eq_primeCounting']; rfl
  calc (Nat.primesBelow q).card ≤ (shellPrimes K q ∪ Nat.primesBelow (q / K + 1)).card :=
        Finset.card_le_card hsub
    _ ≤ (shellPrimes K q).card + (Nat.primesBelow (q / K + 1)).card := Finset.card_union_le _ _
    _ = _ := by rw [hc]

/-- `log x ≤ x / 16` for `x ≥ 256`. -/
theorem log_le_div_sixteen {x : ℝ} (hx : 256 ≤ x) : Real.log x ≤ x / 16 := by
  have hx0 : 0 ≤ x := by linarith
  set t := x ^ (1 / 4 : ℝ)
  have ht4 : t ^ 4 = x := rpow_quarter_pow_four hx0
  have ht0 : 0 ≤ t := Real.rpow_nonneg hx0 _
  have ht : 4 ≤ t := by
    by_contra hc; push_neg at hc
    have : t ^ 4 < 4 ^ 4 := pow_lt_pow_left₀ hc ht0 (by norm_num)
    norm_num at this; linarith
  have h1 := log_le_four_rpow hx0
  have h3 : (64 : ℝ) ≤ t ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) ht 3; norm_num at this; linarith
  have h4 : 64 * t ≤ t ^ 4 := by
    have : t ^ 4 = t ^ 3 * t := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right h3 ht0
  linarith

/-- **Top-shell prime count.**  For `q ≥ q0`: `q / (8 log q) ≤ #{p prime : q/16 < p < q}`. -/
theorem shellPrimes_card_lower :
    ∃ q0 : ℕ, 256 ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q →
      (q : ℝ) ≤ 8 * Real.log q * (shellPrimes 16 q).card := by
  obtain ⟨X0, hX0, hcheb⟩ := chebyshev_upper
  refine ⟨max 256 ⌈16 * X0⌉₊, le_max_left _ _, ?_⟩
  intro q hq
  have hq256 : 256 ≤ q := le_trans (le_max_left _ _) hq
  have hqX : 16 * X0 ≤ (q : ℝ) := by
    have := le_trans (le_max_right _ _) hq
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast this)
  have hqr : (256 : ℝ) ≤ q := by exact_mod_cast hq256
  set L := Real.log q with hLdef
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hLle : L ≤ q / 16 := log_le_div_sixteen hqr
  -- lower count
  set n := (q - 1) / 2 with hndef
  have hn1 : 1 ≤ n := by omega
  have h2n : 2 * n ≤ q - 1 := by omega
  have hnr : ((q : ℝ) - 2) / 2 ≤ n := by
    have : q - 2 ≤ 2 * n := by omega
    have h' : ((q - 2 : ℕ) : ℝ) ≤ 2 * n := by exact_mod_cast this
    rw [Nat.cast_sub (by omega)] at h'
    push_cast at h'; linarith
  set A := (Nat.primeCounting (2 * n) : ℝ) with hA
  have hlow := primeCounting_lower n hn1
  have hlog2n : Real.log (2 * n) ≤ L := by
    rw [hLdef]
    refine Real.log_le_log (by positivity) ?_
    have : ((2 * n : ℕ) : ℝ) ≤ q := by exact_mod_cast (by omega : 2 * n ≤ q)
    push_cast at this; exact this
  have hA0 : 0 ≤ A + 1 := by positivity
  have hAL : (n : ℝ) * Real.log 4 ≤ (A + 1) * L :=
    le_trans hlow (mul_le_mul_of_nonneg_left hlog2n hA0)
  -- upper count
  set B := (Nat.primeCounting (q / 16) : ℝ) with hB
  have hfl : ⌊(q : ℝ) / 16⌋₊ = q / 16 := by
    have := Nat.floor_div_eq_div (K := ℝ) q 16; push_cast at this; exact this
  have hBup : B ≤ Cpi * ((q : ℝ) / 16) / Real.log ((q : ℝ) / 16) := by
    have := hcheb ((q : ℝ) / 16) (by linarith); rw [hfl] at this; exact this
  have hlog16 : L / 2 ≤ Real.log ((q : ℝ) / 16) := by
    rw [Real.log_div (by positivity) (by norm_num)]
    have : Real.log 16 ≤ L / 2 := by
      have h256 : Real.log 256 ≤ L := Real.log_le_log (by norm_num) hqr
      have : Real.log 256 = 2 * Real.log 16 := by
        rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith
    linarith
  have hl16pos : 0 < Real.log ((q : ℝ) / 16) := by linarith
  have hBL : B * L ≤ Cpi * q / 8 := by
    have h1 : B * Real.log ((q : ℝ) / 16) ≤ Cpi * ((q : ℝ) / 16) := by
      rwa [le_div_iff₀ hl16pos] at hBup
    have hB0 : 0 ≤ B := by positivity
    have h2 : B * (L / 2) ≤ B * Real.log ((q : ℝ) / 16) := mul_le_mul_of_nonneg_left hlog16 hB0
    linarith
  -- combine
  have hcount := shellPrimes_card_ge 16 q (by norm_num)
  have hmono : Nat.primeCounting (2 * n) ≤ Nat.primeCounting (q - 1) :=
    Nat.monotone_primeCounting h2n
  set P := ((shellPrimes 16 q).card : ℝ) with hP
  have hAPB : A ≤ P + B := by
    have : Nat.primeCounting (2 * n) ≤ (shellPrimes 16 q).card + Nat.primeCounting (q / 16) :=
      le_trans hmono hcount
    have h' : ((Nat.primeCounting (2 * n) : ℕ) : ℝ) ≤
        ((shellPrimes 16 q).card : ℝ) + (Nat.primeCounting (q / 16) : ℝ) := by
      exact_mod_cast this
    simpa [hA, hP, hB] using h'
  have hAPBL : A * L ≤ (P + B) * L := mul_le_mul_of_nonneg_right hAPB hLpos.le
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hCpi : Cpi = 2 * Real.log 2 + 1 := by unfold Cpi; rw [hl4]
  have hnl : ((q : ℝ) - 2) / 2 * Real.log 4 ≤ n * Real.log 4 :=
    mul_le_mul_of_nonneg_right hnr (by rw [hl4]; linarith)
  rw [hl4] at hnl hAL
  rw [hCpi] at hBL
  nlinarith

/-- `H · H! ≤ (H + 1)^(H + 1)`. -/
theorem mul_factorial_le (H : ℕ) : H * H.factorial ≤ (H + 1) ^ (H + 1) := by
  calc H * H.factorial ≤ (H + 1) * (H + 1) ^ H :=
        Nat.mul_le_mul (by omega) (le_trans (Nat.factorial_le_pow H)
          (Nat.pow_le_pow_left (by omega) H))
    _ = (H + 1) ^ (H + 1) := by ring

/-- **V87 entropy inequality.**  There is `q0` such that every exact word with `a > 1` and
`q_* ≥ q0` satisfies, with `H = ⌊16 M / q_*⌋`,
`log q_* ≤ log 16 + log S_rec(H) + 2 log(H + 1)`. -/
theorem entropy_inequality :
    ∃ q0 : ℕ, 256 ≤ q0 ∧ ∀ W : ExactWord, 1 < W.a → q0 ≤ W.qstar →
      Real.log W.qstar ≤ Real.log 16 + Real.log (Srec (16 * W.M / W.qstar)) +
        2 * Real.log ((16 * W.M / W.qstar : ℕ) + 1) := by
  obtain ⟨q0, hq0, hcnt⟩ := shellPrimes_card_lower
  refine ⟨q0, hq0, fun W ha hq => ?_⟩
  have hqD : W.qstar ≤ W.D := le_trans (W.qstar_le Nat.prime_two) (W.Q_two_le_D ha)
  have hDM : W.D ≤ W.M := Nat.sub_le _ _
  have hqpos : 0 < W.qstar := by omega
  have hH : 1 ≤ 16 * W.M / W.qstar := (Nat.le_div_iff_mul_le hqpos).2 (by omega)
  have hcore := W.entropy_core 16 hH
  rw [W.topShellPrimes_eq] at hcore
  have hc := hcnt W.qstar hq
  set q := W.qstar with hqdef
  set H := 16 * W.M / q with hHdef
  set P := (shellPrimes 16 q).card with hPdef
  set S := Srec H with hSdef
  have hqr : (256 : ℝ) ≤ q := by exact_mod_cast le_trans hq0 hq
  have hqrpos : (0 : ℝ) < q := by linarith
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hSpos : (0 : ℝ) < S := by exact_mod_cast Srec_pos H
  have hcore' : (q : ℝ) ^ P ≤ (16 : ℝ) ^ P * ((H : ℝ) * H.factorial) ^ S := by
    exact_mod_cast hcore
  have hmf : (H : ℝ) * H.factorial ≤ ((H : ℝ) + 1) ^ (H + 1) := by
    exact_mod_cast mul_factorial_le H
  have hfpos : (0 : ℝ) < (H : ℝ) * H.factorial := by
    have := Nat.factorial_pos H; positivity
  have hlogc := Real.log_le_log (by positivity) hcore'
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    at hlogc
  have hlogmf : Real.log ((H : ℝ) * H.factorial) ≤ ((H : ℝ) + 1) * ((H : ℝ) + 1) := by
    have h1 := Real.log_le_log hfpos hmf
    rw [Real.log_pow] at h1
    have h2 : Real.log ((H : ℝ) + 1) ≤ (H : ℝ) + 1 := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (H : ℝ) + 1); linarith
    have h3 : (((H + 1 : ℕ) : ℝ)) * Real.log ((H : ℝ) + 1) ≤ ((H : ℝ) + 1) * ((H : ℝ) + 1) := by
      push_cast; exact mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  set L := Real.log q with hLdef
  have hl16 : Real.log 16 ≤ L / 2 := by
    have h256 : Real.log 256 ≤ L := Real.log_le_log (by norm_num) hqr
    have : Real.log 256 = 2 * Real.log 16 := by
      rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hPr : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  have hS0 : (0 : ℝ) ≤ S := hSpos.le
  have hkey : (P : ℝ) * (L - Real.log 16) ≤ S * (((H : ℝ) + 1) * ((H : ℝ) + 1)) := by
    have := mul_le_mul_of_nonneg_left hlogmf hS0
    linarith
  have hkey2 : (q : ℝ) / 16 ≤ S * ((H : ℝ) + 1) ^ 2 := by
    have h1 : (P : ℝ) * (L / 2) ≤ (P : ℝ) * (L - Real.log 16) :=
      mul_le_mul_of_nonneg_left (by linarith) hPr
    have h2 : (q : ℝ) ≤ 8 * L * P := hc
    nlinarith
  have hfin := Real.log_le_log (by positivity) hkey2
  rw [Real.log_div (by positivity) (by norm_num), Real.log_mul hSpos.ne' (by positivity),
    Real.log_pow] at hfin
  push_cast at hfin
  linarith

end Erdos287.PostV71V87
