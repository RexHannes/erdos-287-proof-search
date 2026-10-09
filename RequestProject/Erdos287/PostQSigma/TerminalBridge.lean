import RequestProject.Erdos287.PostQSigma.PG287
import RequestProject.Erdos287.QSigma.Splice
import RequestProject.Erdos287.Counterexample

/-!
# Erdős #287 — post-`Q_Σ` bank, §15, §39, §44: finite exclusion interface and terminal splice

**ERDŐS #287 REMAINS OPEN.**  Every terminal theorem here is an implication whose hypotheses
include the **OPEN** proposition `PG287` (for all large `M`) and the external input
`PsiLowerBound`; the full-range splice additionally assumes a finite exclusion
`FiniteExclusionUpTo U` with `2^1500 ≤ U + 1` that is **not** formalised here (no Huang
certificate bundle is present in the repository).

* `FiniteExclusionUpTo U` — no counterexample has maximum `≤ U` (provider, not asserted);
* `finiteExclusionUpTo_4e9` — the **repository-native** finite bank: `U = 4·10⁹` is proved;
* `original_erdos287_iff_exact_source` — the original statement ⇔ no raw exact source;
* `counterexample_corridor` — a counterexample with `M ≥ 400` has `16M < 121a` and `2a ≤ M`;
* `no_large_counterexample_of_PG287` — PG-287 tail theorem for literal counterexamples;
* `finite_exclusion_and_PG287_imply_erdos287` — **Theorem B** (full intended splice, conditional);
* `erdos287_of_PG287_repository_native` — **Theorem A** (uses the proved `4·10⁹` bank and leaves
  the intermediate range `(4·10⁹, 2^1500)` as an explicit hypothesis).

Both terminal theorems conclude the *original ordered-sequence statement*
(`Erdos287.erdos287_seq_of_no_counterexample` form), not a private reformulation.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

open Erdos287 Erdos287.ExactSource

/-- **Finite exclusion provider**: no Erdős #287 counterexample has maximum `≤ U`. -/
def FiniteExclusionUpTo (U : ℕ) : Prop :=
  ∀ A : Finset ℕ, ∀ h : Erdos287Counterexample A, U < A.max' h.nonempty

/-- The repository-native finite bank: `FiniteExclusionUpTo (4·10⁹)` is **proved**. -/
theorem finiteExclusionUpTo_4e9 : FiniteExclusionUpTo 4000000000 := by
  intro A h
  by_contra hc
  push_neg at hc
  exact no_Erdos287Counterexample_of_max_le_4e9 h hc

/-- Finite exclusion is monotone. -/
theorem FiniteExclusionUpTo.mono {U V : ℕ} (h : FiniteExclusionUpTo U) (hVU : V ≤ U) :
    FiniteExclusionUpTo V := fun A hA => lt_of_le_of_lt hVU (h A hA)

/-- **Adapter A**: the original statement ⇔ no raw exact source `(a, M, R = ∅)`, `1 < a < M`. -/
theorem original_erdos287_iff_exact_source :
    (∀ A : Finset ℕ, ¬ Erdos287Counterexample A) ↔
      ∀ a M : ℕ, 1 < a → a < M → ∀ E : Finset ℕ, ¬ SourceSol a M ∅ E :=
  erdos287_iff_no_source

/-- The exact source of a counterexample is a raw source solution counted by `N_T`. -/
theorem NT_pos_of_counterexample {A : Finset ℕ} (h : Erdos287Counterexample A) :
    NT (A.min' h.nonempty) (A.max' h.nonempty) ≠ 0 := by
  intro h0
  exact NT_eq_zero_iff.1 h0 _ (sourceSol_of_counterexample h (Finset.disjoint_empty_left A))

/-- **Corridor for counterexamples**: if `M ≥ 400` then `16M < 121a` and `2a ≤ M`
(`a = min A`, `M = max A`). -/
theorem counterexample_corridor {A : Finset ℕ} (h : Erdos287Counterexample A)
    (hM : 400 ≤ A.max' h.nonempty) :
    16 * A.max' h.nonempty < 121 * A.min' h.nonempty ∧
      2 * A.min' h.nonempty ≤ A.max' h.nonempty := by
  set ce := h.toGap2CE
  have hN : ce.N = A.min' h.nonempty := rfl
  have hMM : ce.M = A.max' h.nonempty := rfl
  have hup := ce.exp_upper
  have hlo := ce.exp_lower
  rw [hN, hMM] at hup hlo
  set a := A.min' h.nonempty
  set M := A.max' h.nonempty
  have he1 := Real.exp_one_lt_d9
  have he2 := Real.exp_one_gt_d9
  have hMr : (400 : ℝ) ≤ M := by exact_mod_cast hM
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have he_sq : Real.exp 1 ^ 2 < 7.3891 := by nlinarith
  have hup' : (M : ℝ) < 7.3891 * ((a : ℝ) + 1) := by
    have : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    nlinarith
  constructor
  · have : (16 : ℝ) * M < 121 * a := by nlinarith
    exact_mod_cast this
  · have : (2 : ℝ) * a ≤ M := by nlinarith
    exact_mod_cast this

/-- **PG-287 tail theorem for literal counterexamples**: under the external input
`PsiLowerBound` and the OPEN hypothesis that `PG287 a M` holds for every raw source with
`M ≥ 2^1500` in the counterexample corridor, no counterexample has `M ≥ 2^1500`. -/
theorem no_large_counterexample_of_PG287 (hpsi : PsiLowerBound)
    (hPG : ∀ a M : ℕ, 2 ^ 1500 ≤ M → 16 * M < 121 * a → 2 * a ≤ M → PG287 a M)
    {A : Finset ℕ} (h : Erdos287Counterexample A) (hM : 2 ^ 1500 ≤ A.max' h.nonempty) :
    False := by
  have h12 : ∀ k, 12 ≤ k → (2 : ℕ) ^ 12 ≤ 2 ^ k := fun k hk => Nat.pow_le_pow_right (by norm_num) hk
  have h400 : 400 ≤ A.max' h.nonempty :=
    le_trans (show (400 : ℕ) ≤ 2 ^ 12 by norm_num) (le_trans (h12 1500 (by norm_num)) hM)
  obtain ⟨h16, h2a⟩ := counterexample_corridor h h400
  exact PG287_implies_no_tail_source hpsi hM h16 h2a (hPG _ _ hM h16 h2a) _
    (sourceSol_of_counterexample h (Finset.disjoint_empty_left A))

/-- **Theorem B (full intended splice; CONDITIONAL).**  A finite exclusion up to some
`U ≥ 2^1500 - 1`, the external input `PsiLowerBound`, and PG-287 on the tail together imply the
original Erdős #287 statement (ordered-sequence form).  None of the three hypotheses is proved
here; `PG287` is OPEN. -/
theorem finite_exclusion_and_PG287_imply_erdos287 {U : ℕ} (hfin : FiniteExclusionUpTo U)
    (hU : 2 ^ 1500 ≤ U + 1) (hpsi : PsiLowerBound)
    (hPG : ∀ a M : ℕ, 2 ^ 1500 ≤ M → 16 * M < 121 * a → 2 * a ≤ M → PG287 a M)
    (k : ℕ) (n : ℕ → ℕ) (hmono : ∀ i j, i < j → j < k → n i < n j)
    (hone : ∀ i, i < k → 1 < n i) (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / (n i) = 1) :
    ∃ i, i + 1 < k ∧ n i + 3 ≤ n (i + 1) := by
  refine erdos287_seq_of_no_counterexample (fun A hA => ?_) k n hmono hone hsum
  have := hfin A hA
  exact no_large_counterexample_of_PG287 hpsi hPG hA (by omega)

/-- **Theorem A (repository-native splice; CONDITIONAL).**  Uses the *proved* finite bank
`M ≤ 4·10⁹`; the intermediate range `4·10⁹ < M < 2^1500` remains an explicit hypothesis, and
the tail needs `PsiLowerBound` and the OPEN PG-287. -/
theorem erdos287_of_PG287_repository_native
    (hmid : ∀ A : Finset ℕ, ∀ h : Erdos287Counterexample A,
      4000000000 < A.max' h.nonempty → A.max' h.nonempty < 2 ^ 1500 → False)
    (hpsi : PsiLowerBound)
    (hPG : ∀ a M : ℕ, 2 ^ 1500 ≤ M → 16 * M < 121 * a → 2 * a ≤ M → PG287 a M) :
    ∀ A : Finset ℕ, ¬ Erdos287Counterexample A := by
  intro A hA
  have h1 := finiteExclusionUpTo_4e9 A hA
  by_cases hM : A.max' hA.nonempty < 2 ^ 1500
  · exact hmid A hA h1 hM
  · exact no_large_counterexample_of_PG287 hpsi hPG hA (by omega)

end Erdos287.PostQSigma
