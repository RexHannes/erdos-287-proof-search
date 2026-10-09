import RequestProject.Erdos287.QSigma.Bridge
import RequestProject.Erdos287.FiniteRangeExtension

/-!
# Erdős #287 — splicing the exact source with the kernel-checked finite range

The project already proves `no_Erdos287Counterexample_of_max_le_4e9`: no counterexample has
maximum `≤ 4·10⁹`.  Through the exact source equivalence this gives:

* `no_sourceSol_of_M_le_4e9` — no exact source with `1 < a < M ≤ 4·10⁹`, endpoints
  retained and `R` independent has a solution;
* `erdos287_of_universal_certificate_above_4e9` — **conditional terminal theorem with the
  finite range already spliced in**: the GOAL `Q_Σ > P_max(V, R_T)` is needed only for
  `M > 4·10⁹`.  Its hypothesis is open.
-/

open scoped BigOperators

namespace Erdos287.ExactSource

open Erdos287

/-- No exact source with `1 < a < M ≤ 4·10⁹` (endpoints retained, `R` independent) has a
solution. -/
theorem no_sourceSol_of_M_le_4e9 {a M : ℕ} {R E : Finset ℕ} (ha : 1 < a) (haM : a < M)
    (haR : a ∉ R) (hMR : M ∉ R) (hRind : Indep R) (hM : M ≤ 4000000000) :
    ¬ SourceSol a M R E := by
  intro h
  obtain ⟨hce, -, -, hMA, hsub⟩ := counterexample_of_sourceSol ha haM haR hMR hRind h
  have hmax : (B a M R \ E).max' hce.nonempty = M := by
    apply le_antisymm
    · exact (Finset.mem_Icc.1 (hsub (Finset.max'_mem _ _))).2
    · exact Finset.le_max' _ _ hMA
  exact no_Erdos287Counterexample_of_max_le_4e9 hce (by rw [hmax]; exact hM)

/-- **Conditional terminal theorem, finite range spliced.**  If every source with
`1 < a < M` and `M > 4·10⁹` admits an omission set `R`, compulsory for every
counterexample with minimum `a` and maximum `M`, with `Q_Σ > P_max(V, R_T)`, then
Erdős #287 holds.  The hypothesis is the open interior GOAL; it is not proved here. -/
theorem erdos287_of_universal_certificate_above_4e9
    (H : ∀ a M : ℕ, 1 < a → a < M → 4000000000 < M → ∃ R : Finset ℕ,
      (∀ A (h : Erdos287Counterexample A), A.min' h.nonempty = a →
        A.max' h.nonempty = M → Disjoint R A) ∧
      Pmax a M R (RT a M R) < QSigma a M R) :
    ∀ A : Finset ℕ, ¬ Erdos287Counterexample A := by
  intro A hA
  by_cases hM : A.max' hA.nonempty ≤ 4000000000
  · exact no_Erdos287Counterexample_of_max_le_4e9 hA hM
  · have haA := Finset.min'_mem A hA.nonempty
    have ha1 := hA.one_lt _ haA
    have haM : A.min' hA.nonempty < A.max' hA.nonempty := by
      apply Finset.min'_lt_max'_of_card
      have := hA.card_ge; omega
    obtain ⟨R, hRc, hQ⟩ := H _ _ ha1 haM (by omega)
    exact no_solution_of_QSigma_gt_Pmax (by omega) hQ _
      (sourceSol_of_counterexample hA (hRc A hA rfl rfl))

end Erdos287.ExactSource
