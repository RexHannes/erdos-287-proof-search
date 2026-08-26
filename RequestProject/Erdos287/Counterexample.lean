import RequestProject.Erdos287.Defs

/-!
# Erdős Problem #287 — structure of a hypothetical gap-`≤2` counterexample

A hypothetical counterexample is a finite set `A` of positive integers with
`∑_{a∈A} 1/a = 1` in which every element `a ≠ M` has `a+1 ∈ A` or `a+2 ∈ A`
("all gaps `≤ 2`").  Writing `N = min A`, `M = max A`, we prove:

* holes are isolated (no two consecutive integers of `[N,M]` are both missing);
* `N, M ∈ A`;
* the analytic size bounds `e·(N-1) < M ≤ e²·(N+1)` (with `e = Real.exp 1`);
* the explicit consequence `M < 8·N` (i.e. `N > M/8`) whenever `M ≥ 97`.
-/

open scoped BigOperators

set_option maxHeartbeats 4000000

namespace Erdos287

/-- A hypothetical gap-`≤2` counterexample to Erdős #287. -/
structure Gap2CE where
  /-- The set of denominators. -/
  A : Finset ℕ
  /-- It is nonempty. -/
  hne : A.Nonempty
  /-- Every element is positive. -/
  hpos : ∀ a ∈ A, 0 < a
  /-- The reciprocals sum to `1`. -/
  hsum : ∑ a ∈ A, (1 : ℚ) / a = 1
  /-- Every non-maximal element is followed within distance `2`. -/
  hgap : ∀ a ∈ A, a ≠ A.max' hne → (a + 1 ∈ A ∨ a + 2 ∈ A)

namespace Gap2CE

variable (ce : Gap2CE)

/-- The smallest denominator. -/
def N : ℕ := ce.A.min' ce.hne

/-- The largest denominator. -/
def M : ℕ := ce.A.max' ce.hne

/-- `N ∈ A`. -/
theorem N_mem : ce.N ∈ ce.A := Finset.min'_mem _ _

/-- `M ∈ A`. -/
theorem M_mem : ce.M ∈ ce.A := Finset.max'_mem _ _

/-- Every element lies in the window `[N, M]`. -/
theorem mem_Icc {a : ℕ} (ha : a ∈ ce.A) : a ∈ Finset.Icc ce.N ce.M :=
  Finset.mem_Icc.2 ⟨Finset.min'_le _ _ ha, Finset.le_max' _ _ ha⟩

/-
**Holes are isolated**: no two consecutive integers of `[N, M]` are both absent.
-/
theorem holes_isolated :
    ∀ n : ℕ, ce.N ≤ n → n + 1 ≤ ce.M → (n ∈ ce.A ∨ n + 1 ∈ ce.A) := by
  intro n hn hn';
  by_contra h_contra;
  -- Consider the set of elements of `ce.A` that are `< n`. It is nonempty because `N = min' ∈ ce.A` and `N ≤ n`, and actually `N < n` (if `N = n` then `n = N ∈ ce.A`, contradicting `n ∉ ce.A`), so `N` is such an element.
  obtain ⟨a, ha₁, ha₂⟩ : ∃ a ∈ ce.A, a < n ∧ ∀ b ∈ ce.A, b < n → b ≤ a := by
    obtain ⟨a, ha₁, ha₂⟩ : ∃ a ∈ ce.A, a < n := by
      exact ⟨ _, ce.N_mem, lt_of_le_of_ne hn fun h => h_contra <| Or.inl <| h ▸ ce.N_mem ⟩;
    exact ⟨ Finset.max' ( Finset.filter ( fun x => x < n ) ce.A ) ⟨ a, by aesop ⟩, Finset.mem_filter.mp ( Finset.max'_mem ( Finset.filter ( fun x => x < n ) ce.A ) ⟨ a, by aesop ⟩ ) |>.1, Finset.mem_filter.mp ( Finset.max'_mem ( Finset.filter ( fun x => x < n ) ce.A ) ⟨ a, by aesop ⟩ ) |>.2, fun b hb hb' => Finset.le_max' _ _ ( by aesop ) ⟩;
  -- Now `a ≤ n - 1 < n ≤ M`, so `a ≠ M` (since `a < M`). Apply `ce.hgap a (a ∈ ce.A) (a ≠ M)` to get `a+1 ∈ ce.A ∨ a+2 ∈ ce.A`.
  have h_gap : a + 1 ∈ ce.A ∨ a + 2 ∈ ce.A := by
    exact ce.hgap a ha₁ ( ne_of_lt ( lt_of_lt_of_le ha₂.1 ( Nat.le_of_succ_le hn' ) ) );
  grind

/-
**Lower size bound** `e·(N-1) < M`.
-/
theorem exp_lower : Real.exp 1 * ((ce.N : ℝ) - 1) < (ce.M : ℝ) := by
  by_cases hN : ce.N = 1;
  · have := ce.hpos _ ( ce.M_mem ) ; aesop;
  · -- For each integer `n ≥ 2`, `(1:ℝ)/n < Real.log n - Real.log (n-1)`.
    have h_ineq (n : ℕ) (hn : 2 ≤ n) : (1 : ℝ) / n < Real.log n - Real.log (n - 1) := by
      have := exists_deriv_eq_slope Real.log ( show ( n : ℝ ) - 1 < n by norm_num ) ; norm_num at *;
      exact this ( continuousOn_of_forall_continuousAt fun x hx => Real.continuousAt_log <| by linarith [ hx.1, show ( n : ℝ ) ≥ 2 by norm_cast ] ) ( fun x hx => DifferentiableAt.differentiableWithinAt <| Real.differentiableAt_log <| by linarith [ hx.1, show ( n : ℝ ) ≥ 2 by norm_cast ] ) |> fun ⟨ c, hc₁, hc₂ ⟩ => hc₂ ▸ inv_strictAnti₀ ( by linarith [ show ( n : ℝ ) ≥ 2 by norm_cast ] ) ( by linarith );
    -- Summing these inequalities from `N` to `M`, we get `∑ n ∈ Finset.Icc N M, (1:ℝ)/n < Real.log M - Real.log (N-1)`.
    have h_sum_ineq : (∑ n ∈ Finset.Icc ce.N ce.M, (1 : ℝ) / n) < Real.log ce.M - Real.log (ce.N - 1) := by
      have h_sum_ineq : ∀ {a b : ℕ}, 2 ≤ a → a ≤ b → (∑ n ∈ Finset.Icc a b, (1 : ℝ) / n) < Real.log b - Real.log (a - 1) := by
        intros a b ha hb
        induction' hb with b hb ih;
        · simpa using h_ineq a ha;
        · erw [ Finset.sum_Ico_succ_top ( by linarith [ Nat.succ_le_succ hb ] ) ];
          have := h_ineq ( b + 1 ) ( by linarith [ Nat.succ_le_succ hb ] ) ; norm_num at * ; linarith!;
      exact h_sum_ineq ( Nat.lt_of_le_of_ne ( Nat.succ_le_of_lt ( ce.hpos _ ( ce.N_mem ) ) ) ( Ne.symm hN ) ) ( Finset.min'_le _ _ ( ce.M_mem ) );
    -- Since `ce.A ⊆ Finset.Icc N M`, we have `∑ a ∈ ce.A, (1:ℝ)/a ≤ ∑ n ∈ Finset.Icc N M, (1:ℝ)/n`.
    have h_subset : (∑ a ∈ ce.A, (1 : ℝ) / a) ≤ (∑ n ∈ Finset.Icc ce.N ce.M, (1 : ℝ) / n) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg ( fun x hx => Finset.mem_Icc.mpr ⟨ Finset.min'_le _ _ hx, Finset.le_max' _ _ hx ⟩ ) fun _ _ _ => by positivity;
    -- Combining the inequalities, we get `1 < Real.log M - Real.log (N-1)`.
    have h_combined : 1 < Real.log ce.M - Real.log (ce.N - 1) := by
      convert h_subset.trans_lt h_sum_ineq using 1;
      convert ce.hsum.symm using 1;
      norm_num [ ← @Rat.cast_inj ℝ ];
    rw [ ← Real.log_lt_log_iff ( mul_pos ( Real.exp_pos _ ) ( sub_pos.mpr ( mod_cast lt_of_le_of_ne ( Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( by linarith [ ce.hpos _ ( ce.N_mem ) ] ) ) ) ( Ne.symm hN ) ) ) ) ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by linarith [ ce.hpos _ ( ce.M_mem ) ] ) ) ), Real.log_mul ( by positivity ) ( by exact ne_of_gt ( sub_pos.mpr ( mod_cast lt_of_le_of_ne ( Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( by linarith [ ce.hpos _ ( ce.N_mem ) ] ) ) ) ( Ne.symm hN ) ) ) ), Real.log_exp ];
    linarith

/-
**Upper size bound** `M ≤ e²·(N+1)`.
-/
theorem exp_upper : (ce.M : ℝ) ≤ Real.exp 1 ^ 2 * ((ce.N : ℝ) + 1) := by
  -- By definition of $ce.M$ and $ce.N$, we know that $ce.M \leq e^2 \cdot (ce.N + 1)$.
  have h_M_le : (ce.M + 1 : ℝ) ≤ Real.exp 1 ^ 2 * (ce.N + 1) := by
    -- Use the sum estimate and the log bound to get the final inequality.
    have h_sum : (∑ n ∈ Finset.Icc ce.N ce.M, (1 : ℝ) / n) < 2 := by
      -- By definition of $ce.M$ and $ce.N$, we know that $ce.A \subseteq [ce.N, ce.M]$.
      have h_subset : Finset.Icc (ce.N : ℕ) (ce.M : ℕ) \ ce.A ⊆ Finset.image (fun a => a + 1) ce.A := by
        intro m hm;
        by_cases hmN : m = ce.N;
        · simp_all +decide [ Gap2CE.N ];
          exact False.elim <| hm.2 <| Finset.min'_mem _ _;
        · have := ce.holes_isolated ( m - 1 ) ?_ ?_ <;> rcases m with ( _ | _ | m ) <;> simp_all +decide;
          · grind;
          · omega;
      -- Therefore, $\sum_{n \in \text{missing}} \frac{1}{n} \leq \sum_{a \in A} \frac{1}{a+1}$.
      have h_sum_missing : ∑ n ∈ Finset.Icc (ce.N : ℕ) (ce.M : ℕ) \ ce.A, (1 : ℝ) / n ≤ ∑ a ∈ ce.A, (1 : ℝ) / (a + 1) := by
        refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_subset fun _ _ _ => by positivity ) _;
        rw [ Finset.sum_image ] <;> aesop;
      -- Since $\sum_{a \in A} \frac{1}{a+1} < \sum_{a \in A} \frac{1}{a} = 1$, we have $\sum_{n \in \text{missing}} \frac{1}{n} < 1$.
      have h_sum_missing_lt_1 : ∑ a ∈ ce.A, (1 : ℝ) / (a + 1) < ∑ a ∈ ce.A, (1 : ℝ) / a := by
        exact Finset.sum_lt_sum_of_nonempty ce.hne fun x hx => by rw [ div_lt_div_iff₀ ] <;> norm_cast <;> linarith [ ce.hpos x hx ] ;
      rw [ ← Finset.sum_sdiff ( show ce.A ⊆ Finset.Icc ce.N ce.M from fun x hx => Finset.mem_Icc.mpr ⟨ Finset.min'_le _ _ hx, Finset.le_max' _ _ hx ⟩ ) ];
      linarith [ show ( ∑ a ∈ ce.A, ( 1 : ℚ ) / a : ℝ ) = 1 by exact_mod_cast ce.hsum ];
    -- Use the logarithmic bound to get the final inequality.
    have h_log : Real.log (ce.M + 1) - Real.log (ce.N) ≤ ∑ n ∈ Finset.Icc ce.N ce.M, (1 : ℝ) / n := by
      -- Use the fact that $\log(1 + 1/n) \leq 1/n$ to bound the sum.
      have h_log_bound : ∑ n ∈ Finset.Icc ce.N ce.M, (Real.log (n + 1) - Real.log n) ≤ ∑ n ∈ Finset.Icc ce.N ce.M, (1 : ℝ) / n := by
        gcongr;
        rw [ ← Real.log_div ] <;> norm_num;
        · exact le_trans ( Real.log_le_sub_one_of_pos ( div_pos ( by positivity ) ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; exact absurd ( Finset.mem_Icc.mp ‹_› ) ( by norm_num; linarith [ show 0 < ce.N from ce.hpos _ ( ce.N_mem ) ] ) ) ) ) ) ) ( by ring_nf; norm_num [ show ( ‹_› : ℕ ) ≠ 0 from by rintro rfl; exact absurd ( Finset.mem_Icc.mp ‹_› ) ( by norm_num; linarith [ show 0 < ce.N from ce.hpos _ ( ce.N_mem ) ] ) ] );
        · linarith;
        · linarith [ Finset.mem_Icc.mp ‹_›, show ce.N > 0 from ce.hpos _ ( Finset.min'_mem _ ce.hne ) ];
      have h_telescope : ∀ {a b : ℕ}, a ≤ b → ∑ n ∈ Finset.Icc a b, (Real.log (n + 1) - Real.log n) = Real.log (b + 1) - Real.log a := by
        intros a b hab; erw [ Finset.sum_Ico_eq_sum_range ] ;
        convert Finset.sum_range_sub _ _ using 3 <;> push_cast [ Nat.sub_add_comm hab ] <;> ring;
        rw [ Nat.cast_sub hab ] ; ring;
      exact h_telescope ( Finset.min'_le _ _ ( ce.M_mem ) ) ▸ h_log_bound;
    rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow ];
    norm_num at *;
    exact le_trans h_log ( add_le_add h_sum.le ( Real.log_le_log ( Nat.cast_pos.mpr ( ce.hpos _ ( ce.N_mem ) ) ) ( by linarith ) ) );
  linarith

/-
**Explicit consequence**: for `M ≥ 97`, `M < 8·N`, i.e. `N > M/8`.
-/
theorem N_gt_M_div_eight (hM : 97 ≤ ce.M) : ce.M < 8 * ce.N := by
  -- From `ce.exp_upper : (M:ℝ) ≤ Real.exp 1 ^ 2 * ((N:ℝ) + 1)` and `hM : 97 ≤ M`, we derive $(N:ℝ) > 12.12$.
  have hN_gt_12 : (ce.N : ℝ) > 12 := by
    have hN_gt_12 : (ce.M : ℝ) ≤ Real.exp 1 ^ 2 * ((ce.N : ℝ) + 1) := by
      convert ce.exp_upper using 1;
    have := Real.exp_one_lt_d9.le ; norm_num1 at * ; nlinarith [ ( by norm_cast : ( 97:ℝ ) ≤ ce.M ), Real.exp_pos 1 ];
  -- Since `Real.exp 1 < 2.7182818286`, we have `Real.exp 1 ^ 2 < 7.39`.
  have h_exp_sq_lt_7_39 : Real.exp 1 ^ 2 < 7.39 := by
    exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) ( Real.exp_one_lt_d9.le ) 2 ) ( by norm_num );
  exact_mod_cast ( by nlinarith [ show ( ce.M : ℝ ) ≤ Real.exp 1 ^ 2 * ( ce.N + 1 ) by exact_mod_cast ce.exp_upper, show ( ce.N : ℝ ) ≥ 13 by exact_mod_cast Nat.succ_le_of_lt ( Nat.cast_lt.mp hN_gt_12 ) ] : ( ce.M : ℝ ) < 8 * ce.N )

end Gap2CE

end Erdos287