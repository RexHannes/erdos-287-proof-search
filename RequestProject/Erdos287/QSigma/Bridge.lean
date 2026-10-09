import RequestProject.Erdos287.QSigma.Certificate
import RequestProject.Erdos287.ProblemStatement
import RequestProject.Erdos287.Window

/-!
# Erdős #287 — the exact source is literally equivalent to a counterexample

* `sourceSol_of_counterexample` — every literal counterexample `A` (min `a`, max `M`) and
  every compulsory omission set `R` (i.e. `R ∩ A = ∅`) give a source solution
  `E = B \ A`; no omission is lost or double-charged.
* `counterexample_of_sourceSol` — conversely, for `1 < a < M`, endpoints retained and
  `R` independent, every source solution `E` gives the counterexample `B \ E`.
* `erdos287_iff_no_source` — the original statement is equivalent to: no source
  `(a, M, R = ∅)` with `1 < a < M` has a solution.
* `windowBaseline_compulsory` — the prime-power window exclusion already in this project
  supplies a genuinely compulsory baseline.
* `erdos287_of_universal_certificate` — **conditional terminal theorem**: if every source
  `1 < a < M` admits *some* compulsory baseline `R` with `Q_Σ > P_max(V, R_T)`, then no
  counterexample exists.  The hypothesis is the open GOAL; nothing here proves it.
-/

open scoped BigOperators

namespace Erdos287.ExactSource

open Erdos287

/-- Holes of a counterexample are isolated. -/
theorem holes_isolated {A : Finset ℕ} (h : Erdos287Counterexample A) {x : ℕ}
    (hx : A.min' h.nonempty ≤ x) (hx1 : x + 1 ≤ A.max' h.nonempty)
    (hxA : x ∉ A) (hx1A : x + 1 ∉ A) : False := by
  classical
  have hminA := Finset.min'_mem A h.nonempty
  have hlt : A.min' h.nonempty < x := lt_of_le_of_ne hx (fun e => hxA (e ▸ hminA))
  have hne : (A.filter (· < x)).Nonempty := ⟨_, Finset.mem_filter.2 ⟨hminA, hlt⟩⟩
  set y := (A.filter (· < x)).max' hne with hy
  have hyA : y ∈ A ∧ y < x := Finset.mem_filter.1 (Finset.max'_mem _ hne)
  have hmax : ∀ z ∈ A, z < x → z ≤ y := fun z hz hzx =>
    Finset.le_max' _ z (Finset.mem_filter.2 ⟨hz, hzx⟩)
  have hgap := h.gap_le_two y hyA.1 ⟨A.max' h.nonempty, Finset.max'_mem _ _, by omega⟩
  rcases hgap with h1 | h2
  · by_cases hc : y + 1 < x
    · have := hmax _ h1 hc; omega
    · have : y + 1 = x := by omega
      exact hxA (this ▸ h1)
  · by_cases hc : y + 2 < x
    · have := hmax _ h2 hc; omega
    · have : y + 2 = x ∨ y + 2 = x + 1 := by omega
      rcases this with e | e
      · exact hxA (e ▸ h2)
      · exact hx1A (e ▸ h2)

/-- **Source adapter.**  A literal counterexample with min `a`, max `M`, together with any
compulsory omission set `R` (`R ∩ A = ∅`), yields the source solution `E = B \ A`. -/
theorem sourceSol_of_counterexample {A : Finset ℕ} (h : Erdos287Counterexample A)
    {R : Finset ℕ} (hRA : Disjoint R A) :
    SourceSol (A.min' h.nonempty) (A.max' h.nonempty) R
      (B (A.min' h.nonempty) (A.max' h.nonempty) R \ A) := by
  classical
  set a := A.min' h.nonempty with ha_def
  set M := A.max' h.nonempty with hM_def
  have haA : a ∈ A := Finset.min'_mem A h.nonempty
  have hMA : M ∈ A := Finset.max'_mem A h.nonempty
  have ha1 : 1 < a := h.one_lt a haA
  have ha0 : 0 < a := by omega
  have hAB : A ⊆ B a M R := by
    intro n hn
    rw [mem_B]
    exact ⟨Finset.min'_le A n hn, Finset.le_max' A n hn, fun hr =>
      Finset.disjoint_left.1 hRA hr hn⟩
  have hEV : B a M R \ A ⊆ V a M R := by
    intro n hn
    rw [Finset.mem_sdiff] at hn
    obtain ⟨hnB, hnA⟩ := hn
    have hb := mem_B.1 hnB
    refine mem_V.2 ⟨hnB, fun e => hnA (e ▸ haA), fun e => hnA (e ▸ hMA), fun r hr => ⟨?_, ?_⟩⟩
    · intro e
      have hrA : r ∉ A := Finset.disjoint_left.1 hRA hr
      have hnM : n ≠ M := fun e' => hnA (e' ▸ hMA)
      exact holes_isolated h hb.1 (by omega) hnA (e ▸ hrA)
    · intro e
      have hrA : r ∉ A := Finset.disjoint_left.1 hRA hr
      have hna : n ≠ a := fun e' => hnA (e' ▸ haA)
      exact holes_isolated h (x := r) (by omega) (by omega) hrA (e ▸ hnA)
  refine ⟨hEV, ?_, ?_⟩
  · intro x hx hx1
    rw [Finset.mem_sdiff] at hx hx1
    have hb := mem_B.1 hx.1
    have hb1 := mem_B.1 hx1.1
    exact holes_isolated h hb.1 hb1.2.1 hx.2 hx1.2
  · -- reciprocal identity
    have hrec : (∑ n ∈ B a M R \ A, (1 : ℚ) / n) = tau a M R := by
      rw [tau_eq ha0, ← Finset.sum_sdiff hAB, h.sum_one]
      ring
    have hW : (W a M R : ℚ) ≠ 0 := by exact_mod_cast W_ne_zero ha0
    have key := sum_W_div_cast (R := R) (M := M) ha0 (E := B a M R \ A) Finset.sdiff_subset
    rw [hrec, tau, mul_div_cancel₀ _ hW] at key
    exact_mod_cast key

/-- **Converse adapter.**  For `1 < a < M`, endpoints retained and `R` independent, every
source solution `E` gives a literal counterexample `B \ E` that avoids `R` and has
`a`, `M` as members inside `[a, M]`. -/
theorem counterexample_of_sourceSol {a M : ℕ} {R E : Finset ℕ} (ha : 1 < a) (haM : a < M)
    (haR : a ∉ R) (hMR : M ∉ R) (hRind : Indep R) (h : SourceSol a M R E) :
    Erdos287Counterexample (B a M R \ E) ∧ Disjoint R (B a M R \ E) ∧
      a ∈ B a M R \ E ∧ M ∈ B a M R \ E ∧ B a M R \ E ⊆ Finset.Icc a M := by
  classical
  have ha0 : 0 < a := by omega
  have hEV := h.1
  have haA : a ∈ B a M R \ E := by
    refine Finset.mem_sdiff.2 ⟨mem_B.2 ⟨le_rfl, haM.le, haR⟩, fun hE => ?_⟩
    exact (mem_V.1 (hEV hE)).2.1 rfl
  have hMA : M ∈ B a M R \ E := by
    refine Finset.mem_sdiff.2 ⟨mem_B.2 ⟨haM.le, le_rfl, hMR⟩, fun hE => ?_⟩
    exact (mem_V.1 (hEV hE)).2.2.1 rfl
  have hsub : B a M R \ E ⊆ Finset.Icc a M := by
    intro n hn
    have := mem_B.1 (Finset.mem_sdiff.1 hn).1
    exact Finset.mem_Icc.2 ⟨this.1, this.2.1⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, haA, hMA, hsub⟩
  · have : ({a, M} : Finset ℕ) ⊆ B a M R \ E := by
      intro n hn; simp at hn; rcases hn with rfl | rfl <;> assumption
    have h2 := Finset.card_le_card this
    rw [Finset.card_pair haM.ne] at h2
    exact h2
  · intro n hn
    have := (Finset.mem_Icc.1 (hsub hn)).1
    omega
  · have hEB : E ⊆ B a M R := hEV.trans V_subset_B
    have h1 : (∑ n ∈ B a M R \ E, (1 : ℚ) / n) + ∑ n ∈ E, (1 : ℚ) / n =
        ∑ n ∈ B a M R, (1 : ℚ) / n := Finset.sum_sdiff hEB
    rw [h.recip_eq_tau ha0, tau_eq ha0] at h1
    linarith
  · intro x hx ⟨b, hb, hxb⟩
    have hxI := Finset.mem_Icc.1 (hsub hx)
    have hbI := Finset.mem_Icc.1 (hsub hb)
    by_cases h1 : x + 1 ∈ B a M R \ E
    · exact Or.inl h1
    · right
      have hx1M : x + 1 ≠ M := fun e => h1 (e ▸ hMA)
      have hx1 : x + 1 ∈ R ∨ x + 1 ∈ E := by
        by_contra hc
        push_neg at hc
        exact h1 (Finset.mem_sdiff.2 ⟨mem_B.2 ⟨by omega, by omega, hc.1⟩, hc.2⟩)
      refine Finset.mem_sdiff.2 ⟨mem_B.2 ⟨by omega, by omega, fun hR2 => ?_⟩, fun hE2 => ?_⟩
      · rcases hx1 with hR1 | hE1
        · exact hRind _ hR1 hR2
        · exact (((mem_V.1 (hEV hE1)).2.2.2 _ hR2).1) rfl
      · rcases hx1 with hR1 | hE1
        · exact (((mem_V.1 (hEV hE2)).2.2.2 _ hR1).2) rfl
        · exact h.2.1 _ hE1 hE2
  · rw [Finset.disjoint_left]
    intro r hr hrA
    exact (mem_B.1 (Finset.mem_sdiff.1 hrA).1).2.2 hr

/-- **Exact equivalence with the original statement.**  Erdős #287 holds iff no source
`(a, M, R = ∅)` with `1 < a < M` has a solution. -/
theorem erdos287_iff_no_source :
    (∀ A : Finset ℕ, ¬ Erdos287Counterexample A) ↔
      ∀ a M : ℕ, 1 < a → a < M → ∀ E : Finset ℕ, ¬ SourceSol a M ∅ E := by
  constructor
  · intro hno a M ha haM E hE
    exact hno _ (counterexample_of_sourceSol ha haM (by simp) (by simp)
      (fun x hx => by simp at hx) hE).1
  · intro hsrc A hA
    have haA := Finset.min'_mem A hA.nonempty
    have hMA := Finset.max'_mem A hA.nonempty
    have ha1 := hA.one_lt _ haA
    have haM : A.min' hA.nonempty < A.max' hA.nonempty := by
      apply Finset.min'_lt_max'_of_card
      have := hA.card_ge; omega
    exact hsrc _ _ ha1 haM _ (sourceSol_of_counterexample hA (Finset.disjoint_empty_left A))

/-! ## A genuinely compulsory baseline already proved in this project -/

open Classical in
/-- The **window baseline**: positions of `[a, M]` divisible by a prime power `p^e ≤ M`
whose base beats the certified numerator bound `C ⌊M/p^e⌋`. -/
noncomputable def windowBaseline (a M : ℕ) : Finset ℕ :=
  (Finset.Icc a M).filter (fun n => ∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ p ^ e ≤ M ∧
    C (M / p ^ e) < (p : ℤ) ∧ p ^ e ∣ n)

/-- The window baseline is compulsory: it meets no counterexample with maximum `M`. -/
theorem windowBaseline_compulsory {A : Finset ℕ} (h : Erdos287Counterexample A) (a : ℕ) :
    Disjoint (windowBaseline a (A.max' h.nonempty)) A := by
  classical
  rw [Finset.disjoint_left]
  intro n hn hnA
  rw [windowBaseline, Finset.mem_filter] at hn
  obtain ⟨-, p, e, hp, he, hpe, hC, hdvd⟩ := hn
  exact primePower_window_exclusion A (A.max' h.nonempty) p e hp
    (fun x hx => by have := h.one_lt x hx; omega)
    (fun x hx => Finset.le_max' A x hx) h.sum_one he hpe hC n hnA hdvd

/-- **Conditional terminal theorem (the open GOAL as hypothesis).**  Suppose that for every
`1 < a < M` there is an omission set `R` that is compulsory for every counterexample with
minimum `a` and maximum `M`, and for which `Q_Σ > P_max(V, R_T)`.  Then Erdős #287 holds.
The hypothesis is *not* proved anywhere in this project. -/
theorem erdos287_of_universal_certificate
    (H : ∀ a M : ℕ, 1 < a → a < M → ∃ R : Finset ℕ,
      (∀ A (h : Erdos287Counterexample A), A.min' h.nonempty = a →
        A.max' h.nonempty = M → Disjoint R A) ∧
      Pmax a M R (RT a M R) < QSigma a M R) :
    ∀ A : Finset ℕ, ¬ Erdos287Counterexample A := by
  intro A hA
  have haA := Finset.min'_mem A hA.nonempty
  have ha1 := hA.one_lt _ haA
  have haM : A.min' hA.nonempty < A.max' hA.nonempty := by
    apply Finset.min'_lt_max'_of_card
    have := hA.card_ge; omega
  obtain ⟨R, hRc, hQ⟩ := H _ _ ha1 haM
  exact no_solution_of_QSigma_gt_Pmax (by omega) hQ _
    (sourceSol_of_counterexample hA (hRc A hA rfl rfl))

end Erdos287.ExactSource
