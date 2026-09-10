import RequestProject.Defs

/-!
# The harmonic blocker

The bridge `Erdos287.not_counterexample_of_windowPairSupply` uses only the crude counting bound
`#A ≤ x`, and therefore needs `M ≤ 2 * x`.  Here we prove a sharper consumer of a pair of
forbidden consecutive positions `x`, `x + 1`, which reaches all the way to
`M ≤ ⌊8 * (x + 1) / 3⌋`.

The mathematical content is the harmonic estimate

`∑_{n = a+1}^{M} 1/n ≤ log M - log a < 1` whenever `3 * M ≤ 8 * a`,

which holds because `8 / 3 < e`.
-/

namespace Erdos287

open Finset

/-- The basic step of the integral comparison: `1 / (m + 1) ≤ log (m + 1) - log m`. -/
theorem one_div_succ_le_log_sub_log {m : ℕ} (hm : 1 ≤ m) :
    (1 : ℝ) / ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) + 1) - Real.log m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hlog := Real.log_le_sub_one_of_pos (x := (m : ℝ) / ((m : ℝ) + 1)) (by positivity)
  rw [Real.log_div (ne_of_gt hm0) (ne_of_gt h1)] at hlog
  have hh : (m : ℝ) / ((m : ℝ) + 1) - 1 = -(1 / ((m : ℝ) + 1)) := by
    field_simp
    ring
  rw [hh] at hlog
  linarith

/-- Comparison of the harmonic tail with the logarithm. -/
theorem sum_one_div_Icc_le_log_sub_log {a : ℕ} (ha : 1 ≤ a) :
    ∀ M : ℕ, a ≤ M → ∑ n ∈ Finset.Icc (a + 1) M, (1 : ℝ) / n ≤ Real.log M - Real.log a := by
  intro M
  induction M with
  | zero => intro h; omega
  | succ M ih =>
    intro _
    rcases Nat.lt_or_ge M a with hlt | hge
    · have haM : a = M + 1 := by omega
      subst haM
      simp
    · have hstep := Finset.sum_Icc_succ_top (a := a + 1) (b := M) (by omega)
        (fun n => (1 : ℝ) / n)
      rw [hstep]
      have h1 := ih hge
      have h2 : (1 : ℝ) / ((M : ℝ) + 1) ≤ Real.log ((M : ℝ) + 1) - Real.log M :=
        one_div_succ_le_log_sub_log (m := M) (by omega)
      push_cast
      linarith

/-- The harmonic tail from `a + 1` to `M` is `< 1` as soon as `3 * M ≤ 8 * a`, because
`8 / 3 < e`. -/
theorem sum_one_div_Icc_lt_one {a M : ℕ} (ha : 1 ≤ a) (h : 3 * M ≤ 8 * a) :
    ∑ n ∈ Finset.Icc (a + 1) M, (1 : ℝ) / n < 1 := by
  rcases Nat.lt_or_ge M a with hlt | hge
  · have : Finset.Icc (a + 1) M = ∅ := by
      rw [Finset.Icc_eq_empty]; omega
    rw [this]
    simp
  · have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hMR : (0 : ℝ) < M := by
      have : (0:ℝ) < a := haR
      have : (a : ℝ) ≤ M := by exact_mod_cast hge
      linarith
    have hkey := sum_one_div_Icc_le_log_sub_log ha M hge
    have h83 : (3 : ℝ) * M ≤ 8 * a := by exact_mod_cast h
    have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hlt : (M : ℝ) < Real.exp 1 * a := by nlinarith
    have hlog : Real.log M < Real.log (Real.exp 1 * a) := Real.log_lt_log hMR hlt
    rw [Real.log_mul (by positivity) (ne_of_gt haR), Real.log_exp] at hlog
    linarith

/--
**The harmonic blocker.**  If `x` and `x + 1` are both absent from a counterexample `A` whose
maximum `M` exceeds `x + 1`, and `3 * M ≤ 8 * (x + 1)`, then no such `A` exists.

Indeed the gap-at-most-two condition forces every element of `A` to exceed `x + 1`, so the sum
of the reciprocals of `A` is at most the harmonic tail `∑_{n = x+2}^{M} 1/n`, which is `< 1`.
-/
theorem not_counterexample_of_harmonic_forbidden_pair {A : Finset ℕ}
    (h : Erdos287Counterexample A) {x : ℕ}
    (hx : x ∉ A) (hx1 : x + 1 ∉ A)
    (hlt : x + 1 < A.max' h.nonempty)
    (hM : 3 * A.max' h.nonempty ≤ 8 * (x + 1)) : False := by
  classical
  obtain ⟨hgt1, hcard, hsum, hgap⟩ := id h
  set M := A.max' h.nonempty with hMdef
  have hMmem : M ∈ A := Finset.max'_mem _ _
  have hAM : ∀ n ∈ A, n ≤ M := fun n hn => Finset.le_max' _ n hn
  -- no element of `A` is `≤ x`
  have hno : ∀ n ∈ A, x + 1 < n := by
    by_contra hc
    push_neg at hc
    obtain ⟨n₁, hn₁A, hn₁x⟩ := hc
    have hn₁x' : n₁ ≤ x := by
      rcases Nat.lt_or_ge n₁ (x + 1) with hh | hh
      · omega
      · exfalso; have : n₁ = x + 1 := by omega
        exact hx1 (this ▸ hn₁A)
    obtain ⟨y, hyA, hyx, hymax⟩ : ∃ y ∈ A, y ≤ x ∧ ∀ n ∈ A, n ≤ x → n ≤ y := by
      obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image (A.filter (fun n => n ≤ x)) id
        ⟨n₁, by simp [hn₁A, hn₁x']⟩
      simp only [Finset.mem_filter] at hy
      exact ⟨y, hy.1, hy.2, fun n hn hnx => hmax n (by simp [hn, hnx])⟩
    have hyltx : y < x := lt_of_le_of_ne hyx (by rintro rfl; exact hx hyA)
    have hyltM : y < M := by omega
    rcases hgap y hyA ⟨M, hMmem, hyltM⟩ with h1 | h2
    · have hne : y + 1 ≠ x + 1 := by rintro hh; rw [hh] at h1; exact hx1 h1
      have := hymax (y + 1) h1 (by omega)
      omega
    · have hne1 : y + 2 ≠ x := by rintro hh; rw [hh] at h2; exact hx h2
      have hne2 : y + 2 ≠ x + 1 := by rintro hh; rw [hh] at h2; exact hx1 h2
      have := hymax (y + 2) h2 (by omega)
      omega
  -- hence `A ⊆ Icc (x + 2) M`
  have hsub : A ⊆ Finset.Icc (x + 2) M := fun n hn =>
    Finset.mem_Icc.2 ⟨by have := hno n hn; omega, hAM n hn⟩
  -- pass to the reals
  have hsumR : ∑ n ∈ A, (1 : ℝ) / n = 1 := by
    have := congrArg (fun r : ℚ => (r : ℝ)) hsum
    push_cast at this
    simpa using this
  have hle : ∑ n ∈ A, (1 : ℝ) / n ≤ ∑ n ∈ Finset.Icc (x + 2) M, (1 : ℝ) / n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro i _ _; positivity)
  have hlt1 : ∑ n ∈ Finset.Icc ((x + 1) + 1) M, (1 : ℝ) / n < 1 :=
    sum_one_div_Icc_lt_one (a := x + 1) (M := M) (by omega) (by omega)
  have : (1 : ℝ) < 1 := by
    calc (1:ℝ) = ∑ n ∈ A, (1 : ℝ) / n := hsumR.symm
      _ ≤ ∑ n ∈ Finset.Icc (x + 2) M, (1 : ℝ) / n := hle
      _ < 1 := by simpa using hlt1
  exact lt_irrefl _ this

end Erdos287
