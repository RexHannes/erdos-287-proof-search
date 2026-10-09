import Mathlib

/-!
# Erdős #287 — Research Bank V10 §E: the common Bonferroni roughness layer

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Finite combinatorics of the repaired common roughness reduction.

* `allowedPrimes z₀ L` — primes `p ≤ z₀` with `p ∤ L` (the **unit condition**: only primes that are
  units modulo `L` are sieved);
* `bonf P J m = ∑_{d ⊆ P, |d| ≤ J} (-1)^{|d|} 1_{∏d ∣ m}` — Bonferroni truncation at depth `J`;
* `roughInd P m = 1_{no p ∈ P divides m}`;
* `bonf_eq` — exact evaluation: `bonf P J m = 1` if no allowed prime divides `m`, and
  `(-1)^J · C(t-1, J)` if exactly `t ≥ 1` allowed primes divide `m`;
* `lowerBonf_le` / `le_upperBonf` — for **odd** `J`: `L_J(m) ≤ 1_{rough}(m) ≤ U_J(m)` with
  `L_J = bonf J`, `U_J = bonf (J-1)`;
* `upper_sub_lower_eq_shell` — `U_J − L_J` is **exactly** the shell `ω(e) = J`:
  `∑_{d ⊆ P, |d| = J} 1_{∏d ∣ m}`;
* `shell_modulus_le` — every shell modulus satisfies `e = ∏d ≤ z₀^J`;
* `esymm_le` / `shell_reciprocal_le` — `∑_{ω(e)=J} 1/e ≤ s₀^J / J!` with `s₀ = ∑_{p} 1/p`;
* `shell_reciprocal_le_exp` — the factorial estimate pushed through: `s₀^J/J! ≤ (e·s₀/J)^J`;
* `exp_loglog_sq_le_rpow` — the asymptotic statement `exp(C (log log X)²) ≤ X^δ` eventually,
  for every `C, δ > 0` (i.e. `exp(O((log log X)²)) = X^{o(1)}`), **proved** from Mathlib's
  `log^2 = o(id)`; no external provider is needed for this step.
-/

namespace Erdos287
namespace ResearchBankV10
namespace TypeIRoughness

open Finset

/-- Allowed small primes: `p ≤ z₀`, `p` prime, `p ∤ L` (unit condition). -/
def allowedPrimes (z₀ L : ℕ) : Finset ℕ :=
  (range (z₀ + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ L)

theorem mem_allowedPrimes {z₀ L p : ℕ} :
    p ∈ allowedPrimes z₀ L ↔ p ≤ z₀ ∧ p.Prime ∧ ¬ p ∣ L := by
  simp [allowedPrimes]

/-- Bonferroni truncation at depth `J` over a finite set of primes `P`. -/
def bonf (P : Finset ℕ) (J m : ℕ) : ℤ :=
  ∑ d ∈ P.powerset.filter (fun d => d.card ≤ J), (-1) ^ d.card * if (∏ p ∈ d, p) ∣ m then 1 else 0

/-- The shell `ω(e) = J`: squarefree moduli `e = ∏d`, `d ⊆ P`, `|d| = J`, dividing `m`. -/
def shell (P : Finset ℕ) (J m : ℕ) : ℤ :=
  ∑ d ∈ P.powerset.filter (fun d => d.card = J), if (∏ p ∈ d, p) ∣ m then 1 else 0

/-- Roughness indicator. -/
def roughInd (P : Finset ℕ) (m : ℕ) : ℤ := if ∀ p ∈ P, ¬ p ∣ m then 1 else 0

/-- For a set of primes, `∏d ∣ m ⟺ d ⊆ {p ∈ P : p ∣ m}` (for `d ⊆ P`). -/
theorem prod_dvd_iff {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {d : Finset ℕ} (hd : d ⊆ P)
    (m : ℕ) : (∏ p ∈ d, p) ∣ m ↔ d ⊆ P.filter (· ∣ m) := by
  constructor
  · intro h p hp
    exact mem_filter.2 ⟨hd hp, (Finset.dvd_prod_of_mem _ hp).trans h⟩
  · intro h
    exact Finset.prod_primes_dvd m (fun p hp => (hP p (hd hp)).prime)
      (fun p hp => (mem_filter.1 (h hp)).2)

/-- Bonferroni sum reduced to the powerset of the divisor set `T = {p ∈ P : p ∣ m}`. -/
theorem bonf_eq_sum_T {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (J m : ℕ) :
    bonf P J m = ∑ d ∈ (P.filter (· ∣ m)).powerset, if d.card ≤ J then (-1) ^ d.card else 0 := by
  classical
  unfold bonf
  rw [Finset.sum_filter]
  have hsub : (P.filter (· ∣ m)).powerset ⊆ P.powerset :=
    Finset.powerset_mono.2 (Finset.filter_subset _ _)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun d hd => ?_
    have hdT := Finset.mem_powerset.1 hd
    have hdP : d ⊆ P := hdT.trans (Finset.filter_subset _ _)
    rw [if_pos ((prod_dvd_iff hP hdP m).2 hdT)]
    split_ifs <;> simp
  · intro d hd hdT
    have hdP := Finset.mem_powerset.1 hd
    rw [if_neg (fun h => hdT (Finset.mem_powerset.2 ((prod_dvd_iff hP hdP m).1 h)))]
    split_ifs <;> simp

/-- **Exact evaluation of the Bonferroni truncation**, via the partial alternating binomial sum. -/
theorem bonf_eq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (J m : ℕ) :
    bonf P J m = if (P.filter (· ∣ m)).card = 0 then 1
      else (-1) ^ J * ((((P.filter (· ∣ m)).card - 1).choose J : ℕ) : ℤ) := by
  rw [bonf_eq_sum_T hP]
  set T := P.filter (· ∣ m)
  have h := Finset.sum_powerset_apply_card (fun k => if k ≤ J then ((-1 : ℤ) ^ k) else 0) (x := T)
  simp only at h
  rw [h]
  split_ifs with hT
  · rw [hT]; simp
  · obtain ⟨t, ht⟩ : ∃ t, T.card = t + 1 := ⟨T.card - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel, ← Int.alternating_sum_range_choose_eq_choose]
    have hext : ∀ k, ((t + 1).choose k) • (if k ≤ J then ((-1 : ℤ) ^ k) else 0) =
        if k ≤ J then (-1) ^ k * (((t + 1).choose k : ℕ) : ℤ) else 0 := by
      intro k; split_ifs <;> simp [mul_comm]
    simp_rw [hext]
    rw [← Finset.sum_filter]
    have hS : (range (t + 1 + 1)).filter (· ≤ J) ⊆ range (J + 1) := by
      intro k hk; simp only [mem_filter, mem_range] at hk ⊢; omega
    apply Finset.sum_subset hS
    intro k hk hk'
    simp only [mem_filter, mem_range, not_and] at hk hk'
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- `roughInd` in terms of the divisor set. -/
theorem roughInd_eq (P : Finset ℕ) (m : ℕ) :
    roughInd P m = if (P.filter (· ∣ m)).card = 0 then 1 else 0 := by
  unfold roughInd
  congr 1
  apply propext
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]

/-- **Lower Bonferroni inequality** (odd depth): `L_J(m) ≤ 1_{rough}(m)`. -/
theorem lowerBonf_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {J : ℕ} (hJ : Odd J) (m : ℕ) :
    bonf P J m ≤ roughInd P m := by
  rw [bonf_eq hP, roughInd_eq]
  split_ifs
  · exact le_rfl
  · rw [hJ.neg_one_pow]; simp

/-- **Upper Bonferroni inequality** (odd `J`, upper truncation at the even depth `J - 1`):
`1_{rough}(m) ≤ U_J(m)`. -/
theorem le_upperBonf {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {J : ℕ} (hJ : Odd J) (m : ℕ) :
    roughInd P m ≤ bonf P (J - 1) m := by
  rw [bonf_eq hP, roughInd_eq]
  have he : Even (J - 1) := by
    obtain ⟨k, rfl⟩ := hJ; exact ⟨k, by omega⟩
  split_ifs
  · exact le_rfl
  · rw [he.neg_one_pow]; simp

/-- **`U_J − L_J` is exactly the shell `ω(e) = J`** (odd `J`). -/
theorem upper_sub_lower_eq_shell (P : Finset ℕ) {J : ℕ} (hJ : Odd J) (m : ℕ) :
    bonf P (J - 1) m - bonf P J m = shell P J m := by
  have hJ1 : 1 ≤ J := hJ.pos
  unfold bonf shell
  have hsplit : P.powerset.filter (fun d => d.card ≤ J) =
      P.powerset.filter (fun d => d.card ≤ J - 1) ∪ P.powerset.filter (fun d => d.card = J) := by
    ext d
    by_cases h : d ∈ P.powerset
    · simp only [mem_filter, mem_union, h, true_and]; omega
    · simp only [mem_filter, mem_union, h, false_and, or_self]
  have hdisj : Disjoint (P.powerset.filter (fun d => d.card ≤ J - 1))
      (P.powerset.filter (fun d => d.card = J)) := by
    rw [Finset.disjoint_filter]; intro d _ h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj]
  have : ∀ d ∈ P.powerset.filter (fun d => d.card = J),
      (-1 : ℤ) ^ d.card * (if (∏ p ∈ d, p) ∣ m then 1 else 0) =
        -(if (∏ p ∈ d, p) ∣ m then 1 else 0) := by
    intro d hd
    rw [(mem_filter.1 hd).2, hJ.neg_one_pow]; ring
  rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib]
  ring

/-- **Shell moduli are bounded**: `e = ∏d ≤ z₀^J` for `d ⊆ allowedPrimes z₀ L`, `|d| = J`. -/
theorem shell_modulus_le {z₀ L J : ℕ} {d : Finset ℕ} (hd : d ⊆ allowedPrimes z₀ L)
    (hJ : d.card = J) : ∏ p ∈ d, p ≤ z₀ ^ J := by
  rw [← hJ]
  exact Finset.prod_le_pow_card _ _ _ fun p hp => (mem_allowedPrimes.1 (hd hp)).1

/-- The allowed primes are primes. -/
theorem allowedPrimes_prime {z₀ L : ℕ} : ∀ p ∈ allowedPrimes z₀ L, p.Prime :=
  fun _ hp => (mem_allowedPrimes.1 hp).2.1

/-! ## The elementary symmetric bound -/

/-- Bernoulli-type expansion bound: `s^{n+1} + (n+1) x s^n ≤ (s + x)^{n+1}` for `s, x ≥ 0`. -/
theorem pow_succ_add_le {s x : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) (n : ℕ) :
    s ^ (n + 1) + (n + 1) * x * s ^ n ≤ (s + x) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 0 ≤ s ^ n := pow_nonneg hs n
    have h2 : 0 ≤ x * x * s ^ n := by positivity
    calc s ^ (n + 1 + 1) + ((n + 1 : ℕ) + 1 : ℝ) * x * s ^ (n + 1)
        ≤ (s + x) * (s ^ (n + 1) + (n + 1) * x * s ^ n) := by
          push_cast; ring_nf; nlinarith [h2]
      _ ≤ (s + x) * (s + x) ^ (n + 1) := by
          exact mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (s + x) ^ (n + 1 + 1) := by ring

/-- **Elementary symmetric sum bound** `e_J(x) ≤ (∑ x)^J / J!` for nonnegative weights. -/
theorem esymm_le (x : ℕ → ℝ) (hx : ∀ p, 0 ≤ x p) (P : Finset ℕ) (J : ℕ) :
    ∑ d ∈ P.powersetCard J, ∏ p ∈ d, x p ≤ (∑ p ∈ P, x p) ^ J / J.factorial := by
  induction P using Finset.induction_on generalizing J with
  | empty =>
    cases J with
    | zero => simp
    | succ j => rw [Finset.powersetCard_eq_empty.2 (by simp)]; simp
  | insert a P ha ih =>
    cases J with
    | zero => simp
    | succ j =>
      rw [Finset.powersetCard_succ_insert ha, Finset.sum_union]
      · rw [Finset.sum_image]
        · have hins : ∀ d ∈ P.powersetCard j, ∏ p ∈ insert a d, x p = x a * ∏ p ∈ d, x p := by
            intro d hd
            have : a ∉ d := fun h => ha ((mem_powersetCard.1 hd).1 h)
            rw [Finset.prod_insert this]
          rw [Finset.sum_congr rfl hins, ← Finset.mul_sum, Finset.sum_insert ha]
          have h1 := ih (j + 1)
          have h2 := ih j
          set s := ∑ p ∈ P, x p
          have hs : 0 ≤ s := Finset.sum_nonneg fun p _ => hx p
          have hxa := hx a
          have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
          have hB := pow_succ_add_le hs hxa j
          have hfs : ((j + 1).factorial : ℝ) = (j + 1) * j.factorial := by
            push_cast [Nat.factorial_succ]; ring
          calc ∑ d ∈ P.powersetCard (j + 1), ∏ p ∈ d, x p + x a * ∑ d ∈ P.powersetCard j, ∏ p ∈ d, x p
              ≤ s ^ (j + 1) / (j + 1).factorial + x a * (s ^ j / j.factorial) := by
                gcongr
            _ = (s ^ (j + 1) + (j + 1) * x a * s ^ j) / (j + 1).factorial := by
                rw [hfs]; field_simp
            _ ≤ (x a + s) ^ (j + 1) / (j + 1).factorial := by
                gcongr; rw [add_comm (x a) s]; exact hB
        · intro d₁ hd₁ d₂ hd₂ h
          have h1 : a ∉ d₁ := fun h' => ha ((mem_powersetCard.1 hd₁).1 h')
          have h2 : a ∉ d₂ := fun h' => ha ((mem_powersetCard.1 hd₂).1 h')
          rw [← Finset.erase_insert h1, ← Finset.erase_insert h2, h]
      · rw [Finset.disjoint_left]
        intro d hd hd'
        obtain ⟨d', -, rfl⟩ := Finset.mem_image.1 hd'
        exact ha ((mem_powersetCard.1 hd).1 (Finset.mem_insert_self a d'))

/-- **Shell reciprocal bound**: `∑_{d ⊆ P, |d| = J} 1/∏d ≤ s₀^J / J!` with `s₀ = ∑_{p∈P} 1/p`. -/
theorem shell_reciprocal_le (P : Finset ℕ) (J : ℕ) :
    ∑ d ∈ P.powersetCard J, (1 / ((∏ p ∈ d, p : ℕ) : ℝ)) ≤
      (∑ p ∈ P, (1 / (p : ℝ))) ^ J / J.factorial := by
  have := esymm_le (fun p => 1 / (p : ℝ)) (fun p => by positivity) P J
  refine le_trans (le_of_eq ?_) this
  refine Finset.sum_congr rfl fun d _ => ?_
  push_cast
  rw [Finset.prod_div_distrib, Finset.prod_const_one]

/-- The factorial estimate pushed through: `s^J / J! ≤ (e·s/J)^J` (`J ≥ 1`, `s ≥ 0`). -/
theorem pow_div_factorial_le_exp_bound {s : ℝ} (hs : 0 ≤ s) {J : ℕ} (hJ : 1 ≤ J) :
    s ^ J / J.factorial ≤ (Real.exp 1 * s / J) ^ J := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hf : (0 : ℝ) < J.factorial := by exact_mod_cast Nat.factorial_pos J
  have key := Real.pow_div_factorial_le_exp (J : ℝ) hJ'.le J
  rw [div_le_iff₀ hf] at key
  have hexp : Real.exp (J : ℝ) = Real.exp 1 ^ J := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [hexp] at key
  rw [div_le_iff₀ hf, div_pow, mul_pow]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  calc s ^ J * (J : ℝ) ^ J ≤ s ^ J * (Real.exp 1 ^ J * J.factorial) := by
        exact mul_le_mul_of_nonneg_left key (by positivity)
    _ = Real.exp 1 ^ J * s ^ J * J.factorial := by ring

/-- Combined: `∑_{ω(e)=J} 1/e ≤ (e·s₀/J)^J`. -/
theorem shell_reciprocal_le_exp (P : Finset ℕ) {J : ℕ} (hJ : 1 ≤ J) :
    ∑ d ∈ P.powersetCard J, (1 / ((∏ p ∈ d, p : ℕ) : ℝ)) ≤
      (Real.exp 1 * (∑ p ∈ P, (1 / (p : ℝ))) / J) ^ J :=
  (shell_reciprocal_le P J).trans
    (pow_div_factorial_le_exp_bound (Finset.sum_nonneg fun p _ => by positivity) hJ)

/-! ## The asymptotic step `exp(O((log log X)²)) = X^{o(1)}` -/

open Filter Real in
/-- **`exp(C (log log X)²) ≤ X^δ` eventually**, for every `C, δ > 0`. -/
theorem exp_loglog_sq_le_rpow {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) :
    ∀ᶠ X in atTop, exp (C * (log (log X)) ^ 2) ≤ X ^ δ := by
  have h1 := (Real.isLittleO_pow_log_id_atTop (n := 2)).def (c := δ / C) (by positivity)
  have h2 := Real.tendsto_log_atTop.eventually h1
  filter_upwards [h2, eventually_gt_atTop (1 : ℝ)] with X hX hX1
  have hlog : 0 < log X := log_pos hX1
  rw [rpow_def_of_pos (by linarith), exp_le_exp]
  simp only [id, norm_pow, Real.norm_eq_abs, sq_abs] at hX
  rw [abs_of_pos hlog] at hX
  have := mul_le_mul_of_nonneg_left hX hC.le
  calc C * log (log X) ^ 2 ≤ C * (δ / C * log X) := this
    _ = log X * δ := by field_simp

end TypeIRoughness
end ResearchBankV10
end Erdos287
