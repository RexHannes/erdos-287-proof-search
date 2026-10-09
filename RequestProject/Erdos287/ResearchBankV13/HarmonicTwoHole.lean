import RequestProject.Erdos287.ResearchBankV13.PrimeLayer

/-!
# Erdős #287 — Research Bank V13 §20: the harmonic two-hole theorem

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `eta = 685/252`; `eta_lt_exp : (685/252 : ℝ) < e` (from Mathlib's `Real.exp_one_gt_d9`, no
  numerical axiom).
* `harmonic_tail_le_log`: `∑_{n=H+1}^{M} 1/n ≤ log M − log H` (discrete bound, from
  `log x ≤ x − 1`).
* `cannot_cross_two_holes`: a gap-`≤ 2` representation cannot contain `N ≤ h` and `h+1 ≤ M` when
  `h` and `h+1` are both absent (holes are isolated).
* **`two_hole_exclusion`**: if `h, h+1` are both forbidden (not denominators) and
  `h ≤ M ≤ ⌊η (h+1)⌋`, no exact representation with endpoint `M` exists.  Either the
  representation crosses the two holes (impossible), or all denominators exceed `H = h+1`, and
  then `1 = ∑ 1/a ≤ ∑_{n=H+1}^{M} 1/n ≤ log(M/H) ≤ log η < 1`.
* `etaFloor H = 685·H / 252 = ⌊η H⌋` (`etaFloor_eq_floor`).
* **`interval_exclusion_of_adjacent_holes`** — the generic interval-exclusion theorem.
-/

namespace Erdos287
namespace ResearchBankV13
namespace HarmonicTwoHole

open FiniteRepresentationModel

/-- `η = 685/252`. -/
def eta : ℚ := 685 / 252

/-- **`η < e`** (trusted Mathlib bound `2.7182818283 < e`). -/
theorem eta_lt_exp : ((eta : ℚ) : ℝ) < Real.exp 1 := by
  have := Real.exp_one_gt_d9
  unfold eta; push_cast
  linarith [show (685 : ℝ) / 252 < 2.7182818283 by norm_num]

/-- `log η < 1`. -/
theorem log_eta_lt_one : Real.log ((eta : ℚ) : ℝ) < 1 := by
  have hpos : (0 : ℝ) < ((eta : ℚ) : ℝ) := by unfold eta; norm_num
  rw [Real.log_lt_iff_lt_exp hpos]; exact eta_lt_exp

/-- `⌊η H⌋` as a natural number: `685 H / 252`. -/
def etaFloor (H : ℕ) : ℕ := 685 * H / 252

theorem etaFloor_eq_floor (H : ℕ) : etaFloor H = ⌊(eta : ℚ) * H⌋₊ := by
  unfold etaFloor eta
  rw [show (685 / 252 : ℚ) * H = ((685 * H : ℕ) : ℚ) / (252 : ℕ) by push_cast; ring]
  rw [Nat.floor_div_eq_div]

theorem le_eta_mul_of_le_etaFloor {H M : ℕ} (h : M ≤ etaFloor H) :
    (M : ℝ) ≤ ((eta : ℚ) : ℝ) * H := by
  have h1 : 252 * M ≤ 685 * H := by unfold etaFloor at h; omega
  have h2 : (252 * M : ℝ) ≤ 685 * H := by exact_mod_cast h1
  unfold eta; push_cast; linarith

/-- One step: `1/(n+1) ≤ log(n+1) − log n` for `n ≥ 1`. -/
theorem inv_succ_le_log_diff {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) / (n + 1) ≤ Real.log (n + 1) - Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < n + 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n / (n + 1) by positivity)
  rw [Real.log_div hn0.ne' hn1.ne'] at h
  have : (n : ℝ) / (n + 1) - 1 = -(1 / (n + 1)) := by field_simp; ring
  linarith

/-- **Discrete harmonic tail bound**: `∑_{n ∈ (H, M]} 1/n ≤ log M − log H` for `1 ≤ H ≤ M`. -/
theorem harmonic_tail_le_log {H : ℕ} (hH : 1 ≤ H) :
    ∀ M, H ≤ M → ∑ n ∈ Finset.Ioc H M, (1 : ℝ) / n ≤ Real.log M - Real.log H := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hHM ih =>
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have := inv_succ_le_log_diff (n := M) (by omega)
    push_cast
    linarith

/-- **A gap-`≤ 2` representation cannot cross two adjacent forbidden integers.** -/
theorem cannot_cross_two_holes {A : Finset ℕ} (hA : Erdos287Counterexample A) {h : ℕ}
    (hh : h ∉ A) (hH : h + 1 ∉ A) (hN : A.min' hA.nonempty ≤ h)
    (hM : h + 1 ≤ A.max' hA.nonempty) : False := by
  rcases (hA.toGap2CE).holes_isolated h hN hM with h1 | h1
  · exact hh h1
  · exact hH h1

/-- **The harmonic two-hole theorem.**  If `h` and `h+1` are not denominators and
`h ≤ M ≤ ⌊η (h+1)⌋`, then no exact representation has endpoint `M`. -/
theorem two_hole_exclusion {A : Finset ℕ} (hA : Erdos287Counterexample A) {h : ℕ}
    (hh : h ∉ A) (hH : h + 1 ∉ A) (hlo : h ≤ A.max' hA.nonempty)
    (hhi : A.max' hA.nonempty ≤ etaFloor (h + 1)) : False := by
  set M := A.max' hA.nonempty with hMdef
  set N := A.min' hA.nonempty with hNdef
  have hMA : M ∈ A := Finset.max'_mem _ _
  have hNA : N ∈ A := Finset.min'_mem _ _
  have hM2 : h + 2 ≤ M := by
    have h1 : M ≠ h := fun e => hh (e ▸ hMA)
    have h2 : M ≠ h + 1 := fun e => hH (e ▸ hMA)
    omega
  by_cases hN : N ≤ h
  · exact cannot_cross_two_holes hA hh hH hN (by omega)
  · -- all denominators exceed `H = h + 1`
    have hN2 : h + 2 ≤ N := by
      have : N ≠ h + 1 := fun e => hH (e ▸ hNA)
      omega
    have hsub : A ⊆ Finset.Ioc (h + 1) M := by
      intro a ha
      exact Finset.mem_Ioc.2 ⟨by have := Finset.min'_le A a ha; omega, Finset.le_max' _ _ ha⟩
    have hsumR : ∑ a ∈ A, (1 : ℝ) / a = 1 := by
      have := congrArg (fun q : ℚ => (q : ℝ)) hA.sum_one
      simpa using this
    have hle : ∑ a ∈ A, (1 : ℝ) / a ≤ ∑ n ∈ Finset.Ioc (h + 1) M, (1 : ℝ) / n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have htail := harmonic_tail_le_log (H := h + 1) (by omega) M (by omega)
    have hH0 : (0 : ℝ) < ((h + 1 : ℕ) : ℝ) := by positivity
    have hMle := le_eta_mul_of_le_etaFloor hhi
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hlog : Real.log M - Real.log ((h + 1 : ℕ) : ℝ) ≤ Real.log ((eta : ℚ) : ℝ) := by
      rw [← Real.log_div hM0.ne' hH0.ne']
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ hH0]; exact hMle
    have := log_eta_lt_one
    linarith

/-- **Generic interval exclusion.**  If `h ≤ lo`, `hi ≤ ⌊η (h+1)⌋`, and for every exact
representation with endpoint in `[lo, hi]` both `h` and `h+1` are forbidden, then no endpoint in
`[lo, hi]` occurs. -/
theorem interval_exclusion_of_adjacent_holes {h lo hi : ℕ} (hlo : h ≤ lo)
    (hhi : hi ≤ etaFloor (h + 1))
    (hforb : ∀ A : Finset ℕ, ∀ hA : Erdos287Counterexample A,
      lo ≤ A.max' hA.nonempty → A.max' hA.nonempty ≤ hi → h ∉ A ∧ h + 1 ∉ A) :
    ∀ M, lo ≤ M → M ≤ hi → NoCounterexampleAt M := by
  intro M h1 h2 A hA hAM
  obtain ⟨a, b⟩ := hforb A hA (hAM ▸ h1) (hAM ▸ h2)
  exact two_hole_exclusion hA a b (by omega) (by omega)

end HarmonicTwoHole
end ResearchBankV13
end Erdos287
