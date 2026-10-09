import RequestProject.Erdos287.SourceChain.OAIImport.Dictionary
import RequestProject.Erdos287.ResearchBankV15.BombieriVinogradovProvider

/-!
# Erdős #287 — source chain: from the external `ψ`-endpoint BV statement to the project's
prime-counting `OrdinaryBVProvider`

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

The project's provider `ResearchBankV15.BombieriVinogradovProvider.OrdinaryBVProvider` is stated
for the prime-counting function, with main term `π(x)/φ(Q)`, for **all** `x ≥ 2`, maximal over
reduced residues.  The external statement `OAIBombieriVinogradov` is stated for `ψ` (von
Mangoldt weights), with main term `x/φ(q)`, only at the endpoint `x` and only for `x ≥ x₀`.
The types differ; this module proves the missing implication

  `ordinaryBVProvider_of_OAI : OAIBombieriVinogradov → OrdinaryBVProvider`.

Proof outline (all kernel-proved):

1. discrete summation by parts (`sbp_identity`) turns `π(N; Q, r) - π(N)/φ(Q)` into the
   log-weighted errors `G_Q(n) = θ(n; Q, r) - θ(n)/φ(Q)`, `n ≤ N` (`apError_sbp`);
2. `|G_Q(n)|` is bounded trivially (`abs_Gfun_le_triv`) and by the external endpoint error
   plus `ψ - θ` (`abs_Gfun_le_bv`); `|ψ(n) - n|` is the `q = 1` endpoint error;
3. `∑_{Q ≤ X} 1/φ(Q) ≤ (1 + log X)^2` via `φ(Q) τ(Q) ≥ Q` (`sum_inv_totient_le`);
4. for `n ≥ N/(log N)^{2k+4}` the external BV statement applies at the point `n` with the
   moduli range `√N/(log N)^K`; smaller `n` are handled by the trivial bound.
-/

open scoped BigOperators
open Finset

namespace Erdos287.SourceChain.OAIImport

open Erdos287.CurrentTail
open Erdos287.ResearchBankV15.BombieriVinogradovProvider

/-! ### Discrete summation by parts -/

/-- `w(n) = 1/log n - 1/log(n+1)`. -/
noncomputable def sbpW (n : ℕ) : ℝ := 1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)

theorem sbp_identity (g : ℕ → ℝ) (h0 : g 0 = 0) (h1 : g 1 = 0) (N : ℕ) :
    ∑ m ∈ range (N + 1), g m =
      (∑ m ∈ range (N + 1), g m * Real.log m) / Real.log N +
        ∑ n ∈ range N, (∑ m ∈ range (n + 1), g m * Real.log m) * sbpW n := by
  induction N with
  | zero => simp [h0]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun m => g m * Real.log m) (N + 1),
      Finset.sum_range_succ (fun n => (∑ m ∈ range (n + 1), g m * Real.log m) * sbpW n) N]
    have key : g (N + 1) =
        g (N + 1) * Real.log ((N + 1 : ℕ) : ℝ) / Real.log ((N + 1 : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp [h1]
      · have : Real.log ((N + 1 : ℕ) : ℝ) ≠ 0 := by
          apply ne_of_gt; apply Real.log_pos; exact_mod_cast (by omega : 1 < N + 1)
        field_simp
    unfold sbpW
    push_cast at key ⊢
    linear_combination key

theorem sbpW_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ sbpW n := by
  unfold sbpW
  have h1 : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hl : 0 < Real.log n := Real.log_pos h1
  have hle : Real.log n ≤ Real.log ((n:ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
  rw [sub_nonneg]
  exact one_div_le_one_div_of_le hl hle

theorem sbpW_le {n : ℕ} (hn : 2 ≤ n) : sbpW n ≤ 1 / (n * Real.log n ^ 2) := by
  unfold sbpW
  have h1 : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn0 : (0:ℝ) < n := by linarith
  have hl : 0 < Real.log n := Real.log_pos h1
  have hle : Real.log n ≤ Real.log ((n:ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
  have hl2 : 0 < Real.log ((n:ℝ) + 1) := by linarith
  have hdiff : Real.log ((n:ℝ) + 1) - Real.log n ≤ 1 / n := by
    rw [← Real.log_div (by linarith) hn0.ne']
    have := Real.log_le_sub_one_of_pos (show 0 < ((n:ℝ)+1)/n by positivity)
    have e : ((n:ℝ)+1)/n - 1 = 1/n := by field_simp; ring
    linarith
  rw [div_sub_div _ _ hl.ne' hl2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  have : (1 * Real.log ((n:ℝ) + 1) - Real.log n * 1) * (n * Real.log n ^ 2) ≤
      1 * (Real.log n * Real.log (↑n + 1)) := by
    have h3 : (Real.log ((n:ℝ) + 1) - Real.log n) * n ≤ 1 := by
      rw [le_div_iff₀ hn0] at hdiff; linarith
    have h4 : 0 ≤ Real.log ((n:ℝ) + 1) - Real.log n := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hle (sq_nonneg (Real.log n)), mul_nonneg h4 hn0.le]
  linarith

/-! ### The prime-counting error as a summation-by-parts transform -/

/-- `1_{m prime, m ≡ r (Q)} - 1_{m prime}/φ(Q)`. -/
noncomputable def primeInd (Q r m : ℕ) : ℝ :=
  (if m.Prime ∧ m % Q = r % Q then 1 else 0) - (if m.Prime then 1 else 0) / (Nat.totient Q : ℝ)

/-- `G_Q(n) = ∑_{m ≤ n} primeInd · log m = θ(n; Q, r) - θ(n)/φ(Q)`. -/
noncomputable def Gfun (Q r n : ℕ) : ℝ := ∑ m ∈ range (n + 1), primeInd Q r m * Real.log m

theorem sum_range_succ_eq_Icc (f : ℕ → ℝ) (h0 : f 0 = 0) (N : ℕ) :
    ∑ m ∈ range (N + 1), f m = ∑ m ∈ Icc 1 N, f m := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), h0, zero_add]
  rfl

theorem Gfun_zero (Q r : ℕ) : Gfun Q r 0 = 0 := by simp [Gfun]

theorem Gfun_one (Q r : ℕ) : Gfun Q r 1 = 0 := by simp [Gfun, Finset.sum_range_succ]

theorem apError_eq_sum_primeInd (N Q r : ℕ) :
    apError N Q r = ∑ m ∈ range (N + 1), primeInd Q r m := by
  rw [sum_range_succ_eq_Icc _ (by simp [primeInd, Nat.not_prime_zero])]
  unfold apError primeAPCount primeCount primeInd
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.card_filter, Finset.card_filter]
  push_cast
  rfl

theorem apError_sbp (N Q r : ℕ) :
    apError N Q r = Gfun Q r N / Real.log N + ∑ n ∈ Ico 2 N, Gfun Q r n * sbpW n := by
  rw [apError_eq_sum_primeInd, sbp_identity _ (by simp [primeInd, Nat.not_prime_zero])
    (by simp [primeInd, Nat.not_prime_one])]
  congr 1
  rcases Nat.lt_or_ge N 2 with hN | hN
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    interval_cases N
    · simp
    · simp [Finset.sum_range_succ, primeInd]
  · have e : ∀ n, (∑ m ∈ range (n + 1), primeInd Q r m * Real.log m) * sbpW n =
        Gfun Q r n * sbpW n := fun n => rfl
    simp only [e]
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (show 0 < N by omega),
      Finset.sum_eq_sum_Ico_succ_bot (show 0 + 1 < N by omega), Gfun_zero, Gfun_one]
    simp

theorem sum_abs_apError_le (N Qm : ℕ) (r : ℕ → ℕ) :
    ∑ Q ∈ Icc 1 Qm, |apError N Q (r Q)| ≤
      (∑ Q ∈ Icc 1 Qm, |Gfun Q (r Q) N|) / Real.log N +
        ∑ n ∈ Ico 2 N, (∑ Q ∈ Icc 1 Qm, |Gfun Q (r Q) n|) * sbpW n := by
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  calc ∑ Q ∈ Icc 1 Qm, |apError N Q (r Q)|
      ≤ ∑ Q ∈ Icc 1 Qm, (|Gfun Q (r Q) N| / Real.log N +
          ∑ n ∈ Ico 2 N, |Gfun Q (r Q) n| * sbpW n) := by
        refine Finset.sum_le_sum (fun Q _ => ?_)
        rw [apError_sbp]
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_div, abs_of_nonneg hL]
        · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun n hn => ?_))
          rw [abs_mul, abs_of_nonneg (sbpW_nonneg (Finset.mem_Ico.1 hn).1)]
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.sum_mul]

/-! ### Pointwise bounds for `G_Q(n)` -/

theorem card_mod_class_le (n Q c : ℕ) :
    ((range (n + 1)).filter (fun m => m % Q = c)).card ≤ n / Q + 1 := by
  have : ((range (n + 1)).filter (fun m => m % Q = c)).card ≤ (range (n / Q + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun m => m / Q)
    · intro m hm
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hm
      simp only [coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
    · intro a ha b hb hab
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at ha hb
      simp only at hab
      rw [← Nat.div_add_mod a Q, ← Nat.div_add_mod b Q, hab, ha.2, hb.2]
  simpa using this

theorem theta_eq_sum (n : ℕ) :
    ∑ m ∈ range (n + 1), (if m.Prime then (1:ℝ) else 0) * Real.log m = Chebyshev.theta n := by
  rw [sum_range_succ_eq_Icc _ (by simp [Nat.not_prime_zero]), Chebyshev.theta, Nat.floor_natCast,
    Finset.sum_filter, show Finset.Icc 1 n = Finset.Ioc 0 n from rfl]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  split_ifs <;> simp

theorem abs_Gfun_le_triv (Q r n : ℕ) (hQ : 0 < Q) :
    |Gfun Q r n| ≤ Real.log n * ((n : ℝ) / Q + 1) + Real.log 4 * n / (Nat.totient Q : ℝ) := by
  have hφ : (0:ℝ) < Nat.totient Q := by exact_mod_cast Nat.totient_pos.2 hQ
  have hsplit : Gfun Q r n = ∑ m ∈ range (n + 1),
      (if m.Prime ∧ m % Q = r % Q then (1:ℝ) else 0) * Real.log m -
      (∑ m ∈ range (n + 1), (if m.Prime then (1:ℝ) else 0) * Real.log m) /
        (Nat.totient Q : ℝ) := by
    unfold Gfun primeInd
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m _ => by ring)
  rw [hsplit, theta_eq_sum]
  have h1 : 0 ≤ ∑ m ∈ range (n + 1),
      (if m.Prime ∧ m % Q = r % Q then (1:ℝ) else 0) * Real.log m :=
    Finset.sum_nonneg (fun m _ => mul_nonneg (by split_ifs <;> norm_num)
      (Real.log_natCast_nonneg m))
  have h2 : ∑ m ∈ range (n + 1), (if m.Prime ∧ m % Q = r % Q then (1:ℝ) else 0) * Real.log m ≤
      Real.log n * ((n : ℝ) / Q + 1) := by
    calc _ ≤ ∑ m ∈ (range (n + 1)).filter (fun m => m % Q = r % Q), Real.log n := by
          rw [Finset.sum_filter]
          refine Finset.sum_le_sum (fun m hm => ?_)
          have hmn : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
          split_ifs with ha hb hb
          · rw [one_mul]
            exact Real.log_le_log (by exact_mod_cast ha.1.pos) (by exact_mod_cast hmn)
          · exact absurd ha.2 hb
          · rw [zero_mul]; exact Real.log_natCast_nonneg n
          · simp
      _ = Real.log n * ((range (n + 1)).filter (fun m => m % Q = r % Q)).card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ Real.log n * ((n : ℝ) / Q + 1) := by
          apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg n)
          calc (((range (n + 1)).filter (fun m => m % Q = r % Q)).card : ℝ) ≤
                ((n / Q + 1 : ℕ) : ℝ) := by
                exact_mod_cast card_mod_class_le n Q (r % Q)
            _ ≤ _ := by push_cast; gcongr; exact Nat.cast_div_le
  have h3 : 0 ≤ Chebyshev.theta n := Chebyshev.theta_nonneg _
  have h4 : Chebyshev.theta n ≤ Real.log 4 * n := Chebyshev.theta_le_log4_mul_x (by positivity)
  have h5 : Chebyshev.theta n / (Nat.totient Q : ℝ) ≤ Real.log 4 * n / (Nat.totient Q : ℝ) :=
    div_le_div_of_nonneg_right h4 hφ.le
  have h6 : 0 ≤ Chebyshev.theta n / (Nat.totient Q : ℝ) := div_nonneg h3 hφ.le
  rw [abs_le]; constructor <;> linarith

theorem Gfun_decomp (Q r n : ℕ) :
    Gfun Q r n = progErr (Ioc 0 n) vonMangoldtR n Q r -
      progErr (Ioc 0 n) vonMangoldtR n 1 0 / (Nat.totient Q : ℝ) -
      ∑ m ∈ Ioc 0 n, (if m % Q = r % Q then (1:ℝ) else 0) *
        (if m.Prime then 0 else vonMangoldtR m) +
      (∑ m ∈ Ioc 0 n, (if m.Prime then 0 else vonMangoldtR m)) / (Nat.totient Q : ℝ) := by
  unfold Gfun
  rw [sum_range_succ_eq_Icc _ (by simp), show Finset.Icc 1 n = Finset.Ioc 0 n from rfl]
  unfold progErr progSum
  rw [Finset.sum_filter, Finset.sum_filter]
  simp only [Nat.totient_one, Nat.cast_one, div_one, Nat.ModEq, Nat.mod_one, if_true]
  have : ∀ m ∈ Ioc 0 n, primeInd Q r m * Real.log m =
      ((if m % Q = r % Q then vonMangoldtR m else 0) - vonMangoldtR m / (Nat.totient Q : ℝ)) -
      (if m % Q = r % Q then (1:ℝ) else 0) * (if m.Prime then 0 else vonMangoldtR m) +
      (if m.Prime then 0 else vonMangoldtR m) / (Nat.totient Q : ℝ) := by
    intro m _
    unfold primeInd
    by_cases hp : m.Prime
    · simp only [vonMangoldtR, ArithmeticFunction.vonMangoldt_apply_prime hp, hp, true_and,
        if_true]
      split_ifs <;> ring
    · simp only [hp, false_and, if_false]
      split_ifs <;> ring
  rw [Finset.sum_congr rfl this]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
  ring

theorem abs_Gfun_le_bv (Q r n : ℕ) (hQ : 0 < Q) (hr : Nat.Coprime r Q) (hn : 1 ≤ n) :
    |Gfun Q r n| ≤ (endpointError n Q : ℝ) + 2 * Real.sqrt n * Real.log n +
      ((endpointError n 1 : ℝ) + 2 * Real.sqrt n * Real.log n) / (Nat.totient Q : ℝ) := by
  have hφ : (0:ℝ) < Nat.totient Q := by exact_mod_cast Nat.totient_pos.2 hQ
  have e1 := abs_progErr_le_endpointError (n : ℝ) hQ hr
  have e2 := abs_progErr_le_endpointError (n : ℝ) one_pos (show Nat.Coprime 0 1 by norm_num)
  rw [Nat.floor_natCast] at e1 e2
  set D := ∑ m ∈ Ioc 0 n, (if m.Prime then 0 else vonMangoldtR m) with hDdef
  have hD0 : 0 ≤ D := Finset.sum_nonneg (fun m _ => by
    split_ifs
    · exact le_refl 0
    · exact ArithmeticFunction.vonMangoldt_nonneg)
  have hDeq : D = Chebyshev.psi n - Chebyshev.theta n := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, Finset.sum_filter, hDdef]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    split_ifs <;> rfl
  have hDle : D ≤ 2 * Real.sqrt n * Real.log n := by
    rw [hDeq]
    exact (le_abs_self _).trans
      (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by exact_mod_cast hn))
  set Cn := ∑ m ∈ Ioc 0 n, (if m % Q = r % Q then (1:ℝ) else 0) *
    (if m.Prime then 0 else vonMangoldtR m) with hCdef
  have hC0 : 0 ≤ Cn := Finset.sum_nonneg (fun m _ => mul_nonneg (by split_ifs <;> norm_num)
    (by split_ifs
        · exact le_refl 0
        · exact ArithmeticFunction.vonMangoldt_nonneg))
  have hCD : Cn ≤ D := Finset.sum_le_sum (fun m _ => by
    have hν : 0 ≤ (if m.Prime then 0 else vonMangoldtR m) := by
      split_ifs
      · exact le_refl 0
      · exact ArithmeticFunction.vonMangoldt_nonneg
    split_ifs <;> simp_all)
  rw [Gfun_decomp Q r n]
  have h2 : |progErr (Ioc 0 n) vonMangoldtR n 1 0 / (Nat.totient Q : ℝ)| ≤
      (endpointError n 1 : ℝ) / (Nat.totient Q : ℝ) := by
    rw [abs_div, abs_of_pos hφ]; exact div_le_div_of_nonneg_right e2 hφ.le
  have h3 : D / (Nat.totient Q : ℝ) ≤ 2 * Real.sqrt n * Real.log n / (Nat.totient Q : ℝ) :=
    div_le_div_of_nonneg_right hDle hφ.le
  have h4 : 0 ≤ D / (Nat.totient Q : ℝ) := div_nonneg hD0 hφ.le
  rw [add_div]
  calc |progErr (Ioc 0 n) vonMangoldtR n Q r -
        progErr (Ioc 0 n) vonMangoldtR n 1 0 / (Nat.totient Q : ℝ) - Cn + D / (Nat.totient Q : ℝ)|
      ≤ |progErr (Ioc 0 n) vonMangoldtR n Q r| +
        |progErr (Ioc 0 n) vonMangoldtR n 1 0 / (Nat.totient Q : ℝ)| + |Cn| +
        |D / (Nat.totient Q : ℝ)| := by
        have t1 := abs_add_le (progErr (Ioc 0 n) vonMangoldtR n Q r -
          progErr (Ioc 0 n) vonMangoldtR n 1 0 / (Nat.totient Q : ℝ) - Cn)
          (D / (Nat.totient Q : ℝ))
        have t2 := abs_sub (progErr (Ioc 0 n) vonMangoldtR n Q r -
          progErr (Ioc 0 n) vonMangoldtR n 1 0 / (Nat.totient Q : ℝ)) Cn
        have t3 := abs_sub (progErr (Ioc 0 n) vonMangoldtR n Q r)
          (progErr (Ioc 0 n) vonMangoldtR n 1 0 / (Nat.totient Q : ℝ))
        linarith
    _ ≤ _ := by
        rw [abs_of_nonneg hC0, abs_of_nonneg h4]
        linarith

/-! ### Reciprocal sums -/

theorem le_totient_mul_card_divisors (n : ℕ) : n ≤ Nat.totient n * n.divisors.card := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp
  | prime_pow p k hp hk =>
    rw [Nat.totient_prime_pow hp hk, Nat.divisors_prime_pow hp, Finset.card_map,
      Finset.card_range]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    have h2 := hp.two_le
    have : p ≤ (p - 1) * (j + 1 + 1) := by
      have : 2 * (p - 1) ≤ (p - 1) * (j + 1 + 1) := by
        rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
      omega
    calc p ^ j * p ≤ p ^ j * ((p - 1) * (j + 1 + 1)) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.totient_mul hab, Nat.Coprime.card_divisors_mul hab]
    calc a * b ≤ (Nat.totient a * a.divisors.card) * (Nat.totient b * b.divisors.card) :=
          Nat.mul_le_mul iha ihb
      _ = _ := by ring

theorem sum_inv_le (X : ℕ) : ∑ Q ∈ Icc 1 X, 1 / (Q : ℝ) ≤ 1 + Real.log X := by
  have h := harmonic_le_one_add_log X
  have e : (harmonic X : ℝ) = ∑ Q ∈ Finset.Icc 1 X, 1 / (Q : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast; simp
  rw [← e]; exact h

theorem sum_inv_totient_le (X : ℕ) :
    ∑ Q ∈ Icc 1 X, 1 / (Nat.totient Q : ℝ) ≤ (1 + Real.log X) ^ 2 := by
  have step1 : ∀ Q ∈ Finset.Icc 1 X,
      1 / (Nat.totient Q : ℝ) ≤ ∑ d ∈ Q.divisors, 1 / (Q : ℝ) := by
    intro Q hQ
    have hQ1 : 1 ≤ Q := (Finset.mem_Icc.1 hQ).1
    have hφ : (0:ℝ) < Nat.totient Q := by exact_mod_cast Nat.totient_pos.2 hQ1
    have hQ0 : (0:ℝ) < Q := by exact_mod_cast hQ1
    rw [Finset.sum_const, nsmul_eq_mul, div_le_iff₀ hφ, mul_one_div, div_mul_eq_mul_div,
      le_div_iff₀ hQ0, one_mul]
    exact_mod_cast (le_totient_mul_card_divisors Q).trans_eq (mul_comm _ _)
  have step2 : ∑ Q ∈ Finset.Icc 1 X, ∑ d ∈ Q.divisors, 1 / (Q : ℝ) =
      ∑ d ∈ Finset.Icc 1 X, ∑ Q ∈ (Finset.Icc 1 X).filter (fun Q => d ∣ Q), 1 / (Q : ℝ) := by
    apply Finset.sum_comm'
    intro Q d
    simp only [Finset.mem_Icc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, h2⟩, hd, hQ0⟩
      have := Nat.le_of_dvd (by omega) hd
      have := Nat.pos_of_dvd_of_pos hd (by omega)
      exact ⟨⟨⟨h1, h2⟩, hd⟩, by omega, by omega⟩
    · rintro ⟨⟨⟨h1, h2⟩, hd⟩, h3, h4⟩
      exact ⟨⟨h1, h2⟩, hd, by omega⟩
  have step3 : ∀ d ∈ Finset.Icc 1 X,
      ∑ Q ∈ (Finset.Icc 1 X).filter (fun Q => d ∣ Q), 1 / (Q : ℝ) ≤
        (1 / (d : ℝ)) * ∑ e ∈ Finset.Icc 1 X, 1 / (e : ℝ) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.1 hd).1
    have hsub : (Finset.Icc 1 X).filter (fun Q => d ∣ Q) ⊆
        (Finset.Icc 1 X).image (fun e => d * e) := by
      intro Q hQ
      simp only [Finset.mem_filter, Finset.mem_Icc] at hQ
      obtain ⟨⟨h1, h2⟩, ⟨e, rfl⟩⟩ := hQ
      refine Finset.mem_image.2 ⟨e, Finset.mem_Icc.2 ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos e with he | he
        · subst he; omega
        · exact he
      · calc e = 1 * e := (one_mul e).symm
          _ ≤ d * e := Nat.mul_le_mul_right _ hd1
          _ ≤ X := h2
    calc _ ≤ ∑ Q ∈ (Finset.Icc 1 X).image (fun e => d * e), 1 / (Q : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = ∑ e ∈ Finset.Icc 1 X, 1 / ((d * e : ℕ) : ℝ) := by
          rw [Finset.sum_image]
          intro a _ b _ hab
          exact Nat.eq_of_mul_eq_mul_left hd1 hab
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun e _ => ?_)
          push_cast
          rw [one_div_mul_one_div]
  have hS := sum_inv_le X
  have hS0 : 0 ≤ ∑ e ∈ Finset.Icc 1 X, 1 / (e : ℝ) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  calc ∑ Q ∈ Finset.Icc 1 X, 1 / (Nat.totient Q : ℝ)
      ≤ ∑ Q ∈ Finset.Icc 1 X, ∑ d ∈ Q.divisors, 1 / (Q : ℝ) := Finset.sum_le_sum step1
    _ = _ := step2
    _ ≤ ∑ d ∈ Finset.Icc 1 X, (1 / (d : ℝ)) * ∑ e ∈ Finset.Icc 1 X, 1 / (e : ℝ) :=
        Finset.sum_le_sum step3
    _ = (∑ e ∈ Finset.Icc 1 X, 1 / (e : ℝ)) ^ 2 := by rw [← Finset.sum_mul, sq]
    _ ≤ (1 + Real.log X) ^ 2 := pow_le_pow_left₀ hS0 hS 2

/-! ### Summed bounds -/

theorem T_le_triv (Qm n : ℕ) (r : ℕ → ℕ) :
    ∑ Q ∈ Icc 1 Qm, |Gfun Q (r Q) n| ≤
      Real.log n * (n * (1 + Real.log Qm) + Qm) + Real.log 4 * n * (1 + Real.log Qm) ^ 2 := by
  have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  calc ∑ Q ∈ Icc 1 Qm, |Gfun Q (r Q) n|
      ≤ ∑ Q ∈ Icc 1 Qm, (Real.log n * ((n : ℝ) / Q + 1) +
          Real.log 4 * n / (Nat.totient Q : ℝ)) :=
        Finset.sum_le_sum (fun Q hQ => abs_Gfun_le_triv Q (r Q) n (Finset.mem_Icc.1 hQ).1)
    _ = Real.log n * n * ∑ Q ∈ Icc 1 Qm, 1 / (Q : ℝ) + Qm * Real.log n +
          Real.log 4 * n * ∑ Q ∈ Icc 1 Qm, 1 / (Nat.totient Q : ℝ) := by
        have e : ∀ Q ∈ Icc 1 Qm, Real.log n * ((n : ℝ) / Q + 1) +
            Real.log 4 * n / (Nat.totient Q : ℝ) = Real.log n * n * (1 / (Q : ℝ)) +
              Real.log n + Real.log 4 * n * (1 / (Nat.totient Q : ℝ)) := fun Q _ => by ring
        rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp
    _ ≤ _ := by
        have h1 := sum_inv_le Qm
        have h2 := sum_inv_totient_le Qm
        have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        have h5 : Real.log n * n * ∑ Q ∈ Icc 1 Qm, 1 / (Q : ℝ) ≤
            Real.log n * n * (1 + Real.log Qm) := mul_le_mul_of_nonneg_left h1 (by positivity)
        have h6 : Real.log 4 * n * ∑ Q ∈ Icc 1 Qm, 1 / (Nat.totient Q : ℝ) ≤
            Real.log 4 * n * (1 + Real.log Qm) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        nlinarith

theorem T_le_bv (Qm n : ℕ) (r : ℕ → ℕ) (hr : ∀ Q, Nat.Coprime (r Q) Q) (hn : 1 ≤ n) :
    ∑ Q ∈ Icc 1 Qm, |Gfun Q (r Q) n| ≤
      (∑ Q ∈ Icc 1 Qm, (endpointError n Q : ℝ)) + Qm * (2 * Real.sqrt n * Real.log n) +
        ((endpointError n 1 : ℝ) + 2 * Real.sqrt n * Real.log n) * (1 + Real.log Qm) ^ 2 := by
  have hD : 0 ≤ 2 * Real.sqrt n * Real.log n := by
    have := Real.log_natCast_nonneg n; positivity
  have he : 0 ≤ (endpointError n 1 : ℝ) := NNReal.coe_nonneg _
  calc ∑ Q ∈ Icc 1 Qm, |Gfun Q (r Q) n|
      ≤ ∑ Q ∈ Icc 1 Qm, ((endpointError n Q : ℝ) + 2 * Real.sqrt n * Real.log n +
          ((endpointError n 1 : ℝ) + 2 * Real.sqrt n * Real.log n) /
            (Nat.totient Q : ℝ)) :=
        Finset.sum_le_sum (fun Q hQ => abs_Gfun_le_bv Q (r Q) n (Finset.mem_Icc.1 hQ).1 (hr Q) hn)
    _ = (∑ Q ∈ Icc 1 Qm, (endpointError n Q : ℝ)) + Qm * (2 * Real.sqrt n * Real.log n) +
          ((endpointError n 1 : ℝ) + 2 * Real.sqrt n * Real.log n) *
            ∑ Q ∈ Icc 1 Qm, 1 / (Nat.totient Q : ℝ) := by
        have e : ∀ Q ∈ Icc 1 Qm, (endpointError n Q : ℝ) + 2 * Real.sqrt n * Real.log n +
            ((endpointError n 1 : ℝ) + 2 * Real.sqrt n * Real.log n) / (Nat.totient Q : ℝ) =
            (endpointError n Q : ℝ) + 2 * Real.sqrt n * Real.log n +
            ((endpointError n 1 : ℝ) + 2 * Real.sqrt n * Real.log n) *
              (1 / (Nat.totient Q : ℝ)) := fun Q _ => by ring
        rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum (Icc 1 Qm) (fun Q => 1 / (Nat.totient Q : ℝ)), Finset.sum_const,
          Nat.card_Icc, nsmul_eq_mul]
        simp
    _ ≤ _ := by
        have h2 := sum_inv_totient_le Qm
        have := mul_le_mul_of_nonneg_left h2 (add_nonneg he hD)
        linarith

/-! ### Assembly -/

theorem eventually_nat_cond (k : ℕ) (x₀ : ℝ) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    3 ≤ N ∧ Real.log N ^ (2 * k + 8) ≤ Real.sqrt N ∧ x₀ ≤ Real.sqrt N := by
  have hlo := isLittleO_log_rpow_rpow_atTop ((2 * k + 8 : ℕ) : ℝ) (show (0:ℝ) < 1/2 by norm_num)
  have hev := hlo.bound (show (0:ℝ) < 1 by norm_num)
  have hsq : Filter.Tendsto (fun x : ℝ => Real.sqrt x) Filter.atTop Filter.atTop := by
    simpa [Real.sqrt_eq_rpow] using tendsto_rpow_atTop (show (0:ℝ) < 1/2 by norm_num)
  have hev2 : ∀ᶠ x : ℝ in Filter.atTop, (3 ≤ x ∧
      ‖Real.log x ^ ((2 * k + 8 : ℕ) : ℝ)‖ ≤ 1 * ‖x ^ (1/2:ℝ)‖) ∧ x₀ ≤ Real.sqrt x :=
    ((Filter.eventually_ge_atTop _).and hev).and (hsq.eventually_ge_atTop x₀)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev2)
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨⟨h3, hb⟩, hx⟩ := hN₀ N hN
  have hN3 : (3:ℝ) ≤ N := h3
  have hL0 : 0 < Real.log N := Real.log_pos (by linarith)
  refine ⟨by exact_mod_cast h3, ?_, hx⟩
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
    one_mul, Real.rpow_natCast, ← Real.sqrt_eq_rpow] at hb
  exact hb

/-- Basic size facts at scale `N`. -/
theorem logN_facts {N : ℕ} (hN3 : 3 ≤ N) : 1 ≤ Real.log N := by
  have : (3:ℝ) ≤ N := by exact_mod_cast hN3
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])

/-- **High range bound for `T(n)`**: for `n ≥ N/(log N)^{2k+4}` the external BV statement
applies at the point `n`. -/
theorem T_high {k K : ℕ} {M b x₀ : ℝ} (hM : 0 < M) (hb : 0 < b) (hK : ⌈b⌉₊ + 2 * k + 4 ≤ K)
    (hbv : ∀ x : ℝ, x₀ ≤ x →
      ∑ q ∈ Icc 1 ⌊x^(1/2:ℝ) * (Real.log x)^(-b)⌋₊, (endpointError x q : ℝ) ≤
        M * x * (Real.log x)^(-((k:ℝ) + 2)))
    {N n : ℕ} (hN3 : 3 ≤ N) (hLN : Real.log N ^ (2 * k + 8) ≤ Real.sqrt N)
    (hx₀ : x₀ ≤ Real.sqrt N) (hnN : n ≤ N) (hY : (N:ℝ) / Real.log N ^ (2 * k + 4) ≤ n)
    (hQm : 1 ≤ ⌊Real.sqrt N / Real.log N ^ K⌋₊) (r : ℕ → ℕ) (hr : ∀ Q, Nat.Coprime (r Q) Q) :
    ∑ Q ∈ Icc 1 ⌊Real.sqrt N / Real.log N ^ K⌋₊, |Gfun Q (r Q) n| ≤
      5 * Real.log N ^ 2 * (M * n * 2 ^ (k + 2) / Real.log N ^ (k + 2)) +
        2 * Real.sqrt n * Real.log N *
          ((⌊Real.sqrt N / Real.log N ^ K⌋₊ : ℝ) + 4 * Real.log N ^ 2) := by
  set L := Real.log N with hLdef
  set Qm := ⌊Real.sqrt N / L ^ K⌋₊ with hQmdef
  have hL1 : 1 ≤ L := logN_facts hN3
  have hL0 : 0 < L := by linarith
  have hNr : (3:ℝ) ≤ N := by exact_mod_cast hN3
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
  -- `Y ≥ √N`
  have hpow_le : L ^ (2 * k + 4) ≤ Real.sqrt N :=
    le_trans (pow_le_pow_right₀ hL1 (by omega)) hLN
  have hY_ge : Real.sqrt N ≤ (N:ℝ) / L ^ (2 * k + 4) := by
    rw [le_div_iff₀ (by positivity)]
    calc Real.sqrt N * L ^ (2 * k + 4) ≤ Real.sqrt N * Real.sqrt N :=
          mul_le_mul_of_nonneg_left hpow_le hsN.le
      _ = N := Real.mul_self_sqrt (by linarith)
  have hn_ge : Real.sqrt N ≤ n := hY_ge.trans hY
  have hn_pos : (0:ℝ) < n := lt_of_lt_of_le hsN hn_ge
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1:ℝ) ≤ n by
    have : (1:ℝ) ≤ Real.sqrt N := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
    linarith)
  -- logarithms
  have hlogn_le : Real.log n ≤ L := Real.log_le_log hn_pos (by exact_mod_cast hnN)
  have hlogn_ge : L / 2 ≤ Real.log n := by
    have h1 : Real.log (Real.sqrt N) = L / 2 := by
      rw [Real.log_sqrt (by linarith)]
    rw [← h1]; exact Real.log_le_log hsN hn_ge
  have hlogn_pos : 0 < Real.log n := by linarith
  -- the moduli range fits in the BV range at the point `n`
  have hsqrt_n : Real.sqrt N / L ^ (k + 2) ≤ Real.sqrt n := by
    have h := Real.sqrt_le_sqrt hY
    rwa [Real.sqrt_div' _ (by positivity), show 2 * k + 4 = 2 * (k + 2) by ring, pow_mul',
      Real.sqrt_sq (by positivity)] at h
  have hrpow : 1 / L ^ ⌈b⌉₊ ≤ (Real.log n) ^ (-b) := by
    have h1 : L ^ (-b) ≤ (Real.log n) ^ (-b) :=
      Real.rpow_le_rpow_of_nonpos hlogn_pos hlogn_le (by linarith)
    have h2 : L ^ (-(⌈b⌉₊ : ℝ)) ≤ L ^ (-b) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [Nat.le_ceil b])
    rw [Real.rpow_neg hL0.le, Real.rpow_natCast, ← one_div] at h2
    linarith
  have hrange : (Qm : ℝ) ≤ (n:ℝ) ^ (1/2:ℝ) * (Real.log n) ^ (-b) := by
    rw [← Real.sqrt_eq_rpow]
    calc (Qm : ℝ) ≤ Real.sqrt N / L ^ K := Nat.floor_le (by positivity)
      _ ≤ Real.sqrt N / L ^ (k + 2 + ⌈b⌉₊) := by
          apply div_le_div_of_nonneg_left hsN.le (by positivity)
          exact pow_le_pow_right₀ hL1 (by omega)
      _ = (Real.sqrt N / L ^ (k + 2)) * (1 / L ^ ⌈b⌉₊) := by
          rw [pow_add]; field_simp
      _ ≤ Real.sqrt n * (Real.log n) ^ (-b) :=
          mul_le_mul hsqrt_n hrpow (by positivity) (Real.sqrt_nonneg _)
  have hQm_le : Qm ≤ ⌊(n:ℝ)^(1/2:ℝ) * (Real.log n)^(-b)⌋₊ := Nat.le_floor hrange
  -- endpoint errors at the point `n`
  have hBV := hbv n (hx₀.trans hn_ge)
  have hEbound : M * n * (Real.log n) ^ (-((k:ℝ) + 2)) ≤ M * n * 2 ^ (k + 2) / L ^ (k + 2) := by
    rw [Real.rpow_neg hlogn_pos.le, show ((k:ℝ) + 2) = ((k + 2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    calc L ^ (k + 2) = (2 * (L / 2)) ^ (k + 2) := by ring
      _ = 2 ^ (k + 2) * (L / 2) ^ (k + 2) := by rw [mul_pow]
      _ ≤ 2 ^ (k + 2) * Real.log n ^ (k + 2) := by gcongr
  have hS : ∑ Q ∈ Icc 1 Qm, (endpointError n Q : ℝ) ≤ M * n * 2 ^ (k + 2) / L ^ (k + 2) := by
    refine le_trans ?_ (hBV.trans hEbound)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hQm_le)
      (fun _ _ _ => NNReal.coe_nonneg _)
  have hE1 : (endpointError n 1 : ℝ) ≤ M * n * 2 ^ (k + 2) / L ^ (k + 2) := by
    refine le_trans ?_ (hBV.trans hEbound)
    exact Finset.single_le_sum (f := fun q => (endpointError (n:ℝ) q : ℝ))
      (fun _ _ => NNReal.coe_nonneg _) (Finset.mem_Icc.2 ⟨le_rfl, hQm.trans hQm_le⟩)
  -- the remaining factors
  have hQm_log : (1 + Real.log Qm) ^ 2 ≤ 4 * L ^ 2 := by
    have hQ1 : (1:ℝ) ≤ Qm := by exact_mod_cast hQm
    have h0 : 0 ≤ Real.log Qm := Real.log_nonneg hQ1
    have h1 : Real.log Qm ≤ L := by
      apply Real.log_le_log (by linarith)
      calc (Qm : ℝ) ≤ Real.sqrt N / L ^ K := Nat.floor_le (by positivity)
        _ ≤ Real.sqrt N := div_le_self hsN.le (one_le_pow₀ hL1)
        _ ≤ N := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    nlinarith
  have hD : 2 * Real.sqrt n * Real.log n ≤ 2 * Real.sqrt n * L :=
    mul_le_mul_of_nonneg_left hlogn_le (by positivity)
  have hD0 : 0 ≤ 2 * Real.sqrt n * Real.log n := by positivity
  have hT := T_le_bv Qm n r hr hn1
  have hEnn : 0 ≤ M * n * 2 ^ (k + 2) / L ^ (k + 2) := by positivity
  have hQ0 : (0:ℝ) ≤ Qm := Nat.cast_nonneg _
  calc ∑ Q ∈ Icc 1 Qm, |Gfun Q (r Q) n|
      ≤ (∑ Q ∈ Icc 1 Qm, (endpointError n Q : ℝ)) + Qm * (2 * Real.sqrt n * Real.log n) +
        ((endpointError n 1 : ℝ) + 2 * Real.sqrt n * Real.log n) * (1 + Real.log Qm) ^ 2 := hT
    _ ≤ (M * n * 2 ^ (k + 2) / L ^ (k + 2)) + Qm * (2 * Real.sqrt n * L) +
        ((M * n * 2 ^ (k + 2) / L ^ (k + 2)) + 2 * Real.sqrt n * L) * (4 * L ^ 2) := by
        have a1 : (Qm : ℝ) * (2 * Real.sqrt n * Real.log n) ≤ Qm * (2 * Real.sqrt n * L) :=
          mul_le_mul_of_nonneg_left hD hQ0
        have a2 : ((endpointError n 1 : ℝ) + 2 * Real.sqrt n * Real.log n) ≤
            (M * n * 2 ^ (k + 2) / L ^ (k + 2)) + 2 * Real.sqrt n * L := add_le_add hE1 hD
        have a3 := mul_le_mul a2 hQm_log (sq_nonneg _) (by positivity)
        linarith
    _ ≤ _ := by
        set E := M * n * 2 ^ (k + 2) / L ^ (k + 2) with hE
        have hE2 : E ≤ L ^ 2 * E := le_mul_of_one_le_left hEnn (by nlinarith)
        have eq : E + Qm * (2 * Real.sqrt n * L) + (E + 2 * Real.sqrt n * L) * (4 * L ^ 2) =
            5 * L ^ 2 * E + 2 * Real.sqrt n * L * ((Qm : ℝ) + 4 * L ^ 2) - (L ^ 2 * E - E) := by
          ring
        rw [eq]; linarith

/-- Pure arithmetic of the high range. -/
theorem high_arith {L σ s n Qm T w M : ℝ} {k K : ℕ} (hL1 : 1 ≤ L) (hσ : L ^ (2 * k + 8) ≤ σ)
    (hs : σ / L ^ (k + 2) ≤ s) (hs2 : s ^ 2 = n) (hQ : Qm ≤ σ / L ^ K) (hK : 2 * k + 4 ≤ K)
    (hQ0 : 0 ≤ Qm) (hM : 0 ≤ M)
    (hT : T ≤ 5 * L ^ 2 * (M * n * 2 ^ (k + 2) / L ^ (k + 2)) + 2 * s * L * (Qm + 4 * L ^ 2))
    (hT0 : 0 ≤ T) (hw : w ≤ 4 / (n * L ^ 2)) :
    T * w ≤ (20 * M * 2 ^ (k + 2) + 40) / L ^ (k + 2) := by
  have hL0 : 0 < L := by linarith
  have hσ0 : 0 < σ := lt_of_lt_of_le (by positivity) hσ
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hn0 : 0 < n := by rw [← hs2]; positivity
  have hLk : 0 < L ^ (k + 2) := by positivity
  have h1 : T * w ≤ T * (4 / (n * L ^ 2)) := mul_le_mul_of_nonneg_left hw hT0
  have hinv_s : 1 / s ≤ L ^ (k + 2) / σ := by
    rw [div_le_div_iff₀ hs0 hσ0, one_mul]
    rw [div_le_iff₀ hLk] at hs; linarith
  have hQs : Qm / s ≤ 1 / L ^ (k + 2) := by
    calc Qm / s = Qm * (1 / s) := by ring
      _ ≤ (σ / L ^ K) * (L ^ (k + 2) / σ) :=
          mul_le_mul hQ hinv_s (by positivity) (by positivity)
      _ = L ^ (k + 2) / L ^ K := by field_simp
      _ ≤ L ^ (k + 2) / L ^ (2 * (k + 2)) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact pow_le_pow_right₀ hL1 (by omega)
      _ = 1 / L ^ (k + 2) := by rw [pow_mul', sq]; field_simp
  have hLs : L ^ 2 / s ≤ 1 / L ^ (k + 2) := by
    calc L ^ 2 / s = L ^ 2 * (1 / s) := by ring
      _ ≤ L ^ 2 * (L ^ (k + 2) / σ) := mul_le_mul_of_nonneg_left hinv_s (by positivity)
      _ ≤ L ^ 2 * (L ^ (k + 2) / L ^ (2 * k + 8)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hσ
      _ = 1 / L ^ (k + 4) := by
          rw [show 2 * k + 8 = (k + 2) + 2 + (k + 4) by ring, pow_add, pow_add]
          field_simp; ring
      _ ≤ 1 / L ^ (k + 2) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          exact pow_le_pow_right₀ hL1 (by omega)
  have hTn : T * (4 / (n * L ^ 2)) ≤
      20 * M * 2 ^ (k + 2) / L ^ (k + 2) + 8 * (Qm / s + 4 * (L ^ 2 / s)) / L := by
    calc T * (4 / (n * L ^ 2)) ≤ (5 * L ^ 2 * (M * n * 2 ^ (k + 2) / L ^ (k + 2)) +
          2 * s * L * (Qm + 4 * L ^ 2)) * (4 / (n * L ^ 2)) :=
          mul_le_mul_of_nonneg_right hT (by positivity)
      _ = _ := by rw [← hs2]; field_simp; ring
  have h3 : 8 * (Qm / s + 4 * (L ^ 2 / s)) / L ≤ 40 / L ^ (k + 2) := by
    have h5 : Qm / s + 4 * (L ^ 2 / s) ≤ 5 / L ^ (k + 2) := by
      have := add_le_add hQs (mul_le_mul_of_nonneg_left hLs (by norm_num : (0:ℝ) ≤ 4))
      calc _ ≤ 1 / L ^ (k + 2) + 4 * (1 / L ^ (k + 2)) := this
        _ = 5 / L ^ (k + 2) := by ring
    have hnn : 0 ≤ Qm / s + 4 * (L ^ 2 / s) := by positivity
    calc 8 * (Qm / s + 4 * (L ^ 2 / s)) / L ≤ 8 * (Qm / s + 4 * (L ^ 2 / s)) :=
          div_le_self (by positivity) hL1
      _ ≤ 8 * (5 / L ^ (k + 2)) := by linarith
      _ = 40 / L ^ (k + 2) := by ring
  calc T * w ≤ _ := h1
    _ ≤ _ := hTn
    _ ≤ 20 * M * 2 ^ (k + 2) / L ^ (k + 2) + 40 / L ^ (k + 2) := by linarith
    _ = _ := by ring

/-- **High range, weighted.** -/
theorem wT_high {k K : ℕ} {M b x₀ : ℝ} (hM : 0 < M) (hb : 0 < b) (hK : ⌈b⌉₊ + 2 * k + 4 ≤ K)
    (hbv : ∀ x : ℝ, x₀ ≤ x →
      ∑ q ∈ Icc 1 ⌊x^(1/2:ℝ) * (Real.log x)^(-b)⌋₊, (endpointError x q : ℝ) ≤
        M * x * (Real.log x)^(-((k:ℝ) + 2)))
    {N n : ℕ} (hN3 : 3 ≤ N) (hLN : Real.log N ^ (2 * k + 8) ≤ Real.sqrt N)
    (hx₀ : x₀ ≤ Real.sqrt N) (hn2 : 2 ≤ n) (hnN : n ≤ N)
    (hY : (N:ℝ) / Real.log N ^ (2 * k + 4) ≤ n)
    (hQm : 1 ≤ ⌊Real.sqrt N / Real.log N ^ K⌋₊) (r : ℕ → ℕ) (hr : ∀ Q, Nat.Coprime (r Q) Q) :
    (∑ Q ∈ Icc 1 ⌊Real.sqrt N / Real.log N ^ K⌋₊, |Gfun Q (r Q) n|) * sbpW n ≤
      (20 * M * 2 ^ (k + 2) + 40) / Real.log N ^ (k + 2) := by
  have hT := T_high hM hb hK hbv hN3 hLN hx₀ hnN hY hQm r hr
  set L := Real.log N with hLdef
  have hL1 : 1 ≤ L := logN_facts hN3
  have hL0 : 0 < L := by linarith
  have hNr : (3:ℝ) ≤ N := by exact_mod_cast hN3
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
  have hpow_le : L ^ (2 * k + 4) ≤ Real.sqrt N :=
    le_trans (pow_le_pow_right₀ hL1 (by omega)) hLN
  have hY_ge : Real.sqrt N ≤ (N:ℝ) / L ^ (2 * k + 4) := by
    rw [le_div_iff₀ (by positivity)]
    calc Real.sqrt N * L ^ (2 * k + 4) ≤ Real.sqrt N * Real.sqrt N :=
          mul_le_mul_of_nonneg_left hpow_le hsN.le
      _ = N := Real.mul_self_sqrt (by linarith)
  have hn_ge : Real.sqrt N ≤ n := hY_ge.trans hY
  have hn_pos : (0:ℝ) < n := lt_of_lt_of_le hsN hn_ge
  have hlogn_ge : L / 2 ≤ Real.log n := by
    have h1 : Real.log (Real.sqrt N) = L / 2 := by rw [Real.log_sqrt (by linarith)]
    rw [← h1]; exact Real.log_le_log hsN hn_ge
  have hsqrt_n : Real.sqrt N / L ^ (k + 2) ≤ Real.sqrt n := by
    have h := Real.sqrt_le_sqrt hY
    rwa [Real.sqrt_div' _ (by positivity), show 2 * k + 4 = 2 * (k + 2) by ring, pow_mul',
      Real.sqrt_sq (by positivity)] at h
  have hlogn_pos : 0 < Real.log n := by linarith
  have hw : sbpW n ≤ 4 / (n * L ^ 2) := by
    refine (sbpW_le hn2).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul hlogn_ge hlogn_ge (by positivity) hlogn_pos.le]
  exact high_arith hL1 hLN hsqrt_n (Real.sq_sqrt hn_pos.le) (Nat.floor_le (by positivity))
    (by omega) (Nat.cast_nonneg _) hM.le hT (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hw

/-- **Low range, weighted** (trivial bound). -/
theorem wT_low {N n Qm : ℕ} (hN3 : 3 ≤ N) (hn2 : 2 ≤ n) (hnN : n ≤ N) (hQ1 : 1 ≤ Qm)
    (hQN : Qm ≤ N) (r : ℕ → ℕ) :
    (∑ Q ∈ Icc 1 Qm, |Gfun Q (r Q) n|) * sbpW n ≤
      40 * Real.log N ^ 2 + 4 * Real.log N * Qm / n := by
  set L := Real.log N with hLdef
  have hL1 : 1 ≤ L := logN_facts hN3
  have hn2r : (2:ℝ) ≤ n := by exact_mod_cast hn2
  have hn0 : (0:ℝ) < n := by linarith
  have hlogn_le : Real.log n ≤ L := Real.log_le_log hn0 (by exact_mod_cast hnN)
  have hlogn_ge : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2r
  have hlog2 : 1 / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith [Real.log_two_lt_d9]
  have hQr : (1:ℝ) ≤ Qm := by exact_mod_cast hQ1
  have hlQ0 : 0 ≤ Real.log Qm := Real.log_nonneg hQr
  have hlQ : Real.log Qm ≤ L := Real.log_le_log (by linarith) (by exact_mod_cast hQN)
  have hT := T_le_triv Qm n r
  have hT' : ∑ Q ∈ Icc 1 Qm, |Gfun Q (r Q) n| ≤ 10 * L ^ 2 * n + L * Qm := by
    have hln0 : 0 ≤ Real.log n := by linarith
    have a1 : Real.log n * (n * (1 + Real.log Qm) + Qm) ≤ L * (n * (2 * L) + Qm) :=
      mul_le_mul hlogn_le (by nlinarith) (by positivity) (by linarith)
    have a2 : Real.log 4 * n * (1 + Real.log Qm) ^ 2 ≤ 2 * n * (2 * L) ^ 2 := by
      have : (1 + Real.log Qm) ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      calc Real.log 4 * n * (1 + Real.log Qm) ^ 2 ≤ 2 * n * (1 + Real.log Qm) ^ 2 := by
            gcongr
        _ ≤ 2 * n * (2 * L) ^ 2 := by gcongr
    nlinarith
  have hlogn_pos : 0 < Real.log n := by linarith
  have hw : sbpW n ≤ 4 / n := by
    refine (sbpW_le hn2).trans ?_
    rw [div_le_div_iff₀ (by positivity) hn0]
    have hsq : 1 / 4 ≤ Real.log n ^ 2 := by nlinarith
    nlinarith
  have hw0 := sbpW_nonneg hn2
  have hT0 : 0 ≤ ∑ Q ∈ Icc 1 Qm, |Gfun Q (r Q) n| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  calc (∑ Q ∈ Icc 1 Qm, |Gfun Q (r Q) n|) * sbpW n ≤ (10 * L ^ 2 * n + L * Qm) * (4 / n) :=
        mul_le_mul hT' hw hw0 (by positivity)
    _ = 40 * L ^ 2 + 4 * L * Qm / n := by field_simp; ring

/-- Eventual form, with natural exponents. -/
theorem eventual_bv_pi (h : OAIBombieriVinogradov) (k : ℕ) :
    ∃ K : ℕ, ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ r : ℕ → ℕ,
      (∀ Q, Nat.Coprime (r Q) Q) →
        ∑ Q ∈ Icc 1 ⌊Real.sqrt N / Real.log N ^ K⌋₊, |apError N Q (r Q)| ≤
          C₀ * N / Real.log N ^ k := by
  obtain ⟨b, hb, M, hM, x₀, hx₀, hbv⟩ := h ((k:ℝ) + 2) (by positivity)
  obtain ⟨N₀, hN₀⟩ := eventually_nat_cond k x₀
  refine ⟨⌈b⌉₊ + 2 * k + 4, 200 + 25 * M * 2 ^ (k + 2), by positivity, N₀,
    fun N hN r hr => ?_⟩
  obtain ⟨hN3, hLN, hx⟩ := hN₀ N hN
  set K := ⌈b⌉₊ + 2 * k + 4 with hKdef
  set L := Real.log N with hLdef
  set Qm := ⌊Real.sqrt N / L ^ K⌋₊ with hQmdef
  have hL1 : 1 ≤ L := logN_facts hN3
  have hL0 : 0 < L := by linarith
  have hNr : (3:ℝ) ≤ N := by exact_mod_cast hN3
  have hN0 : (0:ℝ) < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hLk : 0 < L ^ k := by positivity
  have htarget0 : 0 ≤ (200 + 25 * M * 2 ^ (k + 2)) * N / L ^ k := by positivity
  rcases Nat.eq_zero_or_pos Qm with hQ0 | hQpos
  · rw [hQ0]; simpa using htarget0
  have hsN_le : Real.sqrt N ≤ N := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hQK : (Qm : ℝ) ≤ Real.sqrt N / L ^ K := Nat.floor_le (by positivity)
  have hQr : (Qm : ℝ) ≤ Real.sqrt N := hQK.trans (div_le_self hsN.le (one_le_pow₀ hL1))
  have hQN : Qm ≤ N := by exact_mod_cast hQr.trans hsN_le
  have hkk : ∀ j, k ≤ j → (N:ℝ) / L ^ j ≤ N / L ^ k := fun j hj =>
    div_le_div_of_nonneg_left hN0.le hLk (pow_le_pow_right₀ hL1 hj)
  have hP1 : L ^ 2 * Real.sqrt N ≤ N / L ^ k := by
    rw [le_div_iff₀ hLk]
    have : L ^ (k + 2) ≤ Real.sqrt N := le_trans (pow_le_pow_right₀ hL1 (by omega)) hLN
    calc L ^ 2 * Real.sqrt N * L ^ k = L ^ (k + 2) * Real.sqrt N := by ring
      _ ≤ Real.sqrt N * Real.sqrt N := mul_le_mul_of_nonneg_right this hsN.le
      _ = N := Real.mul_self_sqrt hN0.le
  set Y := (N:ℝ) / L ^ (2 * k + 4) with hYdef
  have hY0 : 0 ≤ Y := by positivity
  have hP2 : L ^ 2 * Y ≤ N / L ^ k := by
    have : L ^ 2 * Y = N / L ^ (2 * k + 2) := by
      rw [hYdef, show 2 * k + 4 = (2 * k + 2) + 2 by ring, pow_add]; field_simp
    rw [this]; exact hkk _ (by omega)
  have hSQ : Real.sqrt N * Qm ≤ N / L ^ k := by
    calc Real.sqrt N * Qm ≤ Real.sqrt N * (Real.sqrt N / L ^ K) :=
          mul_le_mul_of_nonneg_left hQK hsN.le
      _ = N / L ^ K := by rw [← mul_div_assoc, Real.mul_self_sqrt hN0.le]
      _ ≤ N / L ^ k := hkk _ (by omega)
  -- endpoint term
  have hEnd : (∑ Q ∈ Icc 1 Qm, |Gfun Q (r Q) N|) / L ≤
      (5 * M * 2 ^ (k + 2) + 10) * N / L ^ k := by
    have hT := T_high hM hb le_rfl hbv hN3 hLN hx le_rfl
      (div_le_self hN0.le (one_le_pow₀ hL1)) hQpos r hr
    rw [div_le_iff₀ hL0]
    have a1 : 5 * L ^ 2 * (M * N * 2 ^ (k + 2) / L ^ (k + 2)) =
        5 * M * 2 ^ (k + 2) * N / L ^ k := by
      rw [pow_add]; field_simp; ring
    have a2 : 5 * M * 2 ^ (k + 2) * N / L ^ k ≤ 5 * M * 2 ^ (k + 2) * N / L ^ k * L :=
      le_mul_of_one_le_right (by positivity) hL1
    have a3 : 2 * Real.sqrt N * L * ((Qm : ℝ) + 4 * L ^ 2) =
        2 * L * (Real.sqrt N * Qm) + 8 * L * (L ^ 2 * Real.sqrt N) := by ring
    have a4 : 2 * L * (Real.sqrt N * Qm) ≤ 2 * L * (N / L ^ k) :=
      mul_le_mul_of_nonneg_left hSQ (by positivity)
    have a5 : 8 * L * (L ^ 2 * Real.sqrt N) ≤ 8 * L * (N / L ^ k) :=
      mul_le_mul_of_nonneg_left hP1 (by positivity)
    have e : (5 * M * 2 ^ (k + 2) + 10) * N / L ^ k * L =
        5 * M * 2 ^ (k + 2) * N / L ^ k * L + 2 * L * (N / L ^ k) + 8 * L * (N / L ^ k) := by
      ring
    rw [e]
    linarith
  -- middle sum
  set c₁ := 20 * M * 2 ^ (k + 2) + 40 with hc₁
  have hc₁0 : 0 ≤ c₁ / L ^ (k + 2) := by positivity
  have hpt : ∀ n ∈ Ico 2 N, (∑ Q ∈ Icc 1 Qm, |Gfun Q (r Q) n|) * sbpW n ≤
      40 * L ^ 2 * (if (n:ℝ) < Y then 1 else 0) + 4 * L * Qm * (1 / (n:ℝ)) +
        c₁ / L ^ (k + 2) := by
    intro n hn
    obtain ⟨hn2, hnN⟩ := Finset.mem_Ico.1 hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlast : 0 ≤ 4 * L * Qm * (1 / (n:ℝ)) := by positivity
    by_cases hY : (n:ℝ) < Y
    · have := wT_low hN3 hn2 hnN.le hQpos hQN r
      rw [if_pos hY, mul_one]
      have e : 4 * L * Qm / n = 4 * L * Qm * (1 / (n:ℝ)) := by ring
      linarith
    · have := wT_high hM hb le_rfl hbv hN3 hLN hx hn2 hnN.le (not_lt.1 hY) hQpos r hr
      rw [if_neg hY, mul_zero, zero_add]
      linarith
  have hcard : (((Ico 2 N).filter (fun n : ℕ => (n:ℝ) < Y)).card : ℝ) ≤ 2 * Y := by
    have hsub : (Ico 2 N).filter (fun n : ℕ => (n:ℝ) < Y) ⊆ range ⌈Y⌉₊ := by
      intro n hn
      rw [Finset.mem_filter] at hn
      exact Finset.mem_range.2 (Nat.lt_ceil.2 hn.2)
    have h1 : (((Ico 2 N).filter (fun n : ℕ => (n:ℝ) < Y)).card : ℝ) ≤ ⌈Y⌉₊ := by
      exact_mod_cast (Finset.card_le_card hsub).trans (by simp)
    have h2 : (⌈Y⌉₊ : ℝ) < Y + 1 := Nat.ceil_lt_add_one hY0
    have hY1 : 1 ≤ Y := by
      have h1' : (1:ℝ) ≤ Real.sqrt N := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
      have hpow : L ^ (2 * k + 4) ≤ Real.sqrt N := le_trans (pow_le_pow_right₀ hL1 (by omega)) hLN
      have : Real.sqrt N ≤ Y := by
        rw [hYdef, le_div_iff₀ (by positivity)]
        calc Real.sqrt N * L ^ (2 * k + 4) ≤ Real.sqrt N * Real.sqrt N :=
              mul_le_mul_of_nonneg_left hpow hsN.le
          _ = N := Real.mul_self_sqrt hN0.le
      linarith
    linarith
  have hharm : ∑ n ∈ Ico 2 N, 1 / (n:ℝ) ≤ 1 + L := by
    refine le_trans ?_ (sum_inv_le N)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hn
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hcardN : ((Ico 2 N).card : ℝ) ≤ N := by
    rw [Nat.card_Ico]; exact_mod_cast Nat.sub_le N 2
  have hMid : ∑ n ∈ Ico 2 N, (∑ Q ∈ Icc 1 Qm, |Gfun Q (r Q) n|) * sbpW n ≤
      40 * L ^ 2 * (2 * Y) + 4 * L * Qm * (1 + L) + N * (c₁ / L ^ (k + 2)) := by
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_boole, Finset.sum_const, nsmul_eq_mul]
    have b1 := mul_le_mul_of_nonneg_left hcard (show 0 ≤ 40 * L ^ 2 by positivity)
    have b2 := mul_le_mul_of_nonneg_left hharm (show 0 ≤ 4 * L * Qm by positivity)
    have b3 := mul_le_mul_of_nonneg_right hcardN hc₁0
    linarith
  -- assemble
  have hsum := sum_abs_apError_le N Qm r
  rw [← hLdef] at hsum
  have f1 : 40 * L ^ 2 * (2 * Y) ≤ 80 * (N / L ^ k) := by
    have := mul_le_mul_of_nonneg_left hP2 (by norm_num : (0:ℝ) ≤ 80)
    linarith
  have f2 : 4 * L * Qm * (1 + L) ≤ 8 * (N / L ^ k) := by
    have hQ0' : (0:ℝ) ≤ Qm := Nat.cast_nonneg _
    have g1 : 4 * L * Qm * (1 + L) ≤ 4 * L * Qm * (2 * L) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have g2 : L ^ 2 * Qm ≤ L ^ 2 * Real.sqrt N := mul_le_mul_of_nonneg_left hQr (by positivity)
    have g3 : 4 * L * Qm * (2 * L) = 8 * (L ^ 2 * Qm) := by ring
    linarith
  have f3 : N * (c₁ / L ^ (k + 2)) ≤ c₁ * (N / L ^ k) := by
    rw [show (N:ℝ) * (c₁ / L ^ (k + 2)) = c₁ * (N / L ^ (k + 2)) by ring]
    exact mul_le_mul_of_nonneg_left (hkk _ (by omega)) (by positivity)
  have e : (200 + 25 * M * 2 ^ (k + 2)) * N / L ^ k =
      (200 + 25 * M * 2 ^ (k + 2)) * (N / L ^ k) := by ring
  have e2 : (5 * M * 2 ^ (k + 2) + 10) * N / L ^ k =
      (5 * M * 2 ^ (k + 2) + 10) * (N / L ^ k) := by ring
  have hNL : 0 ≤ (N:ℝ) / L ^ k := by positivity
  rw [e]
  rw [e2] at hEnd
  have hc : 5 * M * 2 ^ (k + 2) + 10 + 80 + 8 + c₁ ≤ 200 + 25 * M * 2 ^ (k + 2) := by
    rw [hc₁]; linarith
  have hfin := mul_le_mul_of_nonneg_right hc hNL
  have hexp : (5 * M * 2 ^ (k + 2) + 10 + 80 + 8 + c₁) * (N / L ^ k) =
      (5 * M * 2 ^ (k + 2) + 10) * (N / L ^ k) + 80 * (N / L ^ k) + 8 * (N / L ^ k) +
        c₁ * (N / L ^ k) := by ring
  linarith

/-- **External BV ⟹ the project's prime-counting `OrdinaryBVProvider`.** -/
theorem ordinaryBVProvider_of_OAI (h : OAIBombieriVinogradov) : OrdinaryBVProvider := by
  refine ⟨fun A hA => ?_⟩
  obtain ⟨K, C₀, hC₀, N₀, hev⟩ := eventual_bv_pi h ⌈A⌉₊
  set N₁ := max N₀ 3 with hN₁
  have hN₁3 : 3 ≤ N₁ := le_max_right _ _
  have hN₁r : (3:ℝ) ≤ N₁ := by exact_mod_cast hN₁3
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLN₁ : 0 < Real.log N₁ := Real.log_pos (by linarith)
  set Bs := 2 * (N₁ : ℝ) * (Real.sqrt N₁ / Real.log 2 ^ K) with hBs
  have hBs0 : 0 ≤ Bs := by positivity
  refine ⟨(K : ℝ), max C₀ (Bs * Real.log N₁ ^ A / 2 + 1), lt_of_lt_of_le hC₀ (le_max_left _ _),
    fun x hx r hr => ?_⟩
  have hxr : (2:ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0:ℝ) < x := by linarith
  have hLx : 0 < Real.log x := Real.log_pos (by linarith)
  have hrange : bvRange x (K : ℝ) = Icc 1 ⌊Real.sqrt x / Real.log x ^ K⌋₊ := by
    unfold bvRange; rw [Real.rpow_natCast]
  rw [hrange]
  by_cases hbig : N₁ ≤ x
  · -- large `x`: the eventual estimate
    have hx3 : 3 ≤ x := hN₁3.trans hbig
    have hL1 : 1 ≤ Real.log x := logN_facts hx3
    have h1 := hev x ((le_max_left _ _).trans hbig) r hr
    have hpowle : Real.log x ^ A ≤ Real.log x ^ ⌈A⌉₊ := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (Nat.le_ceil A)
    have hApos : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hLx _
    calc _ ≤ C₀ * x / Real.log x ^ ⌈A⌉₊ := h1
      _ ≤ C₀ * x / Real.log x ^ A := div_le_div_of_nonneg_left (by positivity) hApos hpowle
      _ ≤ _ := by
          apply div_le_div_of_nonneg_right _ hApos.le
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hx0.le
  · -- small `x`: a uniform crude bound
    push_neg at hbig
    have hxN₁ : (x : ℝ) ≤ N₁ := by exact_mod_cast hbig.le
    have hterm : ∀ Q ∈ Icc 1 ⌊Real.sqrt x / Real.log x ^ K⌋₊, |apError x Q (r Q)| ≤ 2 * N₁ := by
      intro Q hQ
      have hQ1 : 1 ≤ Q := (Finset.mem_Icc.1 hQ).1
      have hφ : (1:ℝ) ≤ Nat.totient Q := by exact_mod_cast Nat.totient_pos.2 hQ1
      have ha : (primeAPCount x Q (r Q) : ℝ) ≤ x := by
        unfold primeAPCount
        exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
      have hb : (primeCount x : ℝ) ≤ x := by
        unfold primeCount
        exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
      have hc : (primeCount x : ℝ) / Nat.totient Q ≤ x :=
        (div_le_self (Nat.cast_nonneg _) hφ).trans hb
      have hc0 : 0 ≤ (primeCount x : ℝ) / Nat.totient Q := by positivity
      unfold apError
      rw [abs_le]; constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (primeAPCount x Q (r Q))]
    have hcardQ : ((Icc 1 ⌊Real.sqrt x / Real.log x ^ K⌋₊).card : ℝ) ≤
        Real.sqrt N₁ / Real.log 2 ^ K := by
      rw [Nat.card_Icc, Nat.add_sub_cancel]
      refine (Nat.floor_le (by positivity)).trans ?_
      apply div_le_div₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hxN₁) (by positivity)
      exact pow_le_pow_left₀ hlog2.le (Real.log_le_log (by norm_num) hxr) K
    have hsum : ∑ Q ∈ Icc 1 ⌊Real.sqrt x / Real.log x ^ K⌋₊, |apError x Q (r Q)| ≤ Bs := by
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul, hBs]
      have : (0:ℝ) ≤ 2 * N₁ := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hcardQ this]
    have hpow : Real.log x ^ A ≤ Real.log N₁ ^ A :=
      Real.rpow_le_rpow hLx.le (Real.log_le_log hx0 hxN₁) hA.le
    have hApos : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hLx _
    have hAN : 0 < Real.log N₁ ^ A := Real.rpow_pos_of_pos hLN₁ _
    set C := max C₀ (Bs * Real.log N₁ ^ A / 2 + 1)
    have hC : Bs * Real.log N₁ ^ A / 2 + 1 ≤ C := le_max_right _ _
    have hC0 : 0 ≤ C := le_trans (by positivity) hC
    calc _ ≤ Bs := hsum
      _ ≤ C * 2 / Real.log N₁ ^ A := by
          rw [le_div_iff₀ hAN]; nlinarith
      _ ≤ C * x / Real.log N₁ ^ A := by
          apply div_le_div_of_nonneg_right _ hAN.le
          exact mul_le_mul_of_nonneg_left hxr hC0
      _ ≤ C * x / Real.log x ^ A := div_le_div_of_nonneg_left (by positivity) hApos hpow

end Erdos287.SourceChain.OAIImport
