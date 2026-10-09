import RequestProject.Erdos287.SourceChain.Physical.Factorization.Additive

/-!
# Erdős #287 — Pascadi's Proposition 5.2 (additive form): the full greedy proof

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

`prop52_additive` formalizes the proof of Pascadi, arXiv:2505.00653v2, Proposition 5.2:

* the first six positions are placed by Lemma 5.3 (`lemma53`);
* positions `j ≥ 7` (`0`-indexed `≥ 6`) are placed greedily; the greedy choice is made
  deterministic: they go into `d₂` (Pascadi's Case 2 shows `d₂` always has room, because
  `p_j ≤ D^{1/9} < x^{1/15}` — `AddHyp.tail_small`);
* the process is monitored with the lower thresholds `d₂ > x^{1/5-5δ}`, `d₃ > x^{1/3+2δ}/N`;
  the first time one of them is exceeded (`Nat.find`) the remaining positions are placed by the
  two-slot greedy of Case 3.1 (into `d₁, d₃`, with `D₃ = x^{3/5-3δ}/(N d₂)`) or Case 3.2 (into
  `d₁, d₂`, with `D₂ = x^{3/5-3δ}/(N d₃)`); if never exceeded we are in Case 1.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.Factor

lemma csumS_range_succ (t : ℕ → ℝ) (c : ℕ → Fin 3) (k : Fin 3) (m : ℕ) :
    csumS t c k (range (m + 1)) = csumS t c k (range m) + if c m = k then t m else 0 := by
  have := csumS_update_insert t c (c m) k (range m) m (by simp)
  rwa [Function.update_eq_self, ← range_add_one] at this

/-- **Pascadi, Proposition 5.2 (additive form).**  Under `0 < δ < 10⁻⁵`, `x^{2δ} ≤ N ≤
x^{1/3+δ}` and `d ∈ 𝒟⁺(x^{3/5-50δ})` (with the primes in decreasing order, padded by `1`'s),
the greedy placement produces a colouring of every initial segment of positions satisfying
Pascadi's system (5.3). -/
theorem prop52_additive {δ n : ℝ} {t : ℕ → ℝ} (h : AddHyp δ n t) (R : ℕ) :
    ∃ c : ℕ → Fin 3, Good53 δ n (csumS t c 0 (range R)) (csumS t c 1 (range R))
      (csumS t c 2 (range R)) := by
  classical
  have hδ := h.δ_pos; have hδ' := h.δ_small; have hn1 := h.n_lo; have hn2 := h.n_hi
  have ht := h.nonneg
  obtain ⟨c6, h60, h61, h62⟩ := lemma53 h
  set c0 : ℕ → Fin 3 := fun i => if i < 6 then c6 i else 1 with hc0
  have agree6 : ∀ k, csumS t c0 k (range 6) = csumS t c6 k (range 6) := by
    intro k; unfold csumS
    rw [Finset.filter_congr (p := fun i => c0 i = k) (q := fun i => c6 i = k)
      (fun i hi => by simp [hc0, mem_range.1 hi])]
  have frozen : ∀ k : Fin 3, k ≠ 1 → ∀ j, csumS t c0 k (range j) ≤ csumS t c0 k (range 6) := by
    intro k hk j
    unfold csumS
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun i _ _ => ht i)
    intro i
    simp only [mem_filter, mem_range]
    rintro ⟨-, hci⟩
    refine ⟨?_, hci⟩
    by_contra hge
    simp only [hc0, if_neg hge] at hci
    exact hk hci.symm
  have b1 : ∀ j, csumS t c0 0 (range j) ≤ n - δ := fun j =>
    (frozen 0 (by decide) j).trans (by rw [agree6]; exact h60)
  have b3 : ∀ j, csumS t c0 2 (range j) ≤ 2 / 5 + 2 * δ - n := fun j =>
    (frozen 2 (by decide) j).trans (by rw [agree6]; exact h62)
  have b2 : ∀ j ≤ 6, csumS t c0 1 (range j) ≤ 4 / 15 - 5 * δ := fun j hj =>
    (csumS_mono t ht c0 1 (Finset.range_mono hj)).trans (by rw [agree6]; exact h61)
  have nn := csumS_nonneg t ht
  by_cases hex : ∃ j, j ≤ R ∧ (1 / 5 - 5 * δ < csumS t c0 1 (range j) ∨
      1 / 3 + 2 * δ - n < csumS t c0 2 (range j))
  swap
  · -- Case 1: the process terminates successfully.
    push_neg at hex
    obtain ⟨hA, hB⟩ := hex R le_rfl
    refine ⟨c0, b1 R, ?_, ?_⟩ <;> linarith
  -- Case 3: the first time a lower threshold is exceeded.
  obtain ⟨hjR, hj⟩ := Nat.find_spec hex
  have hmin : ∀ i < Nat.find hex, ¬ (i ≤ R ∧ (1 / 5 - 5 * δ < csumS t c0 1 (range i) ∨
      1 / 3 + 2 * δ - n < csumS t c0 2 (range i))) := fun i hi => Nat.find_min hex hi
  have j0 : Nat.find hex ≠ 0 := by
    intro h0; rw [h0] at hj; simp [csumS] at hj; rcases hj with hj | hj <;> linarith
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := Nat.exists_eq_succ_of_ne_zero j0
  have hprev := hmin m (by omega)
  rw [hm] at hj hjR
  have hp : csumS t c0 1 (range m) ≤ 1 / 5 - 5 * δ ∧
      csumS t c0 2 (range m) ≤ 1 / 3 + 2 * δ - n := by
    by_contra hc
    exact hprev ⟨by omega, by
      rcases not_and_or.1 hc with hc | hc
      · exact Or.inl (lt_of_not_ge hc)
      · exact Or.inr (lt_of_not_ge hc)⟩
  obtain ⟨hp2, hp3⟩ := hp
  have tot := csumS_total t c0 (range (m + 1))
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  obtain hcm | hcm | hcm : c0 m = 0 ∨ c0 m = 1 ∨ c0 m = 2 := by
    generalize c0 m = a; fin_cases a <;> simp
  · -- placing into `d₁` cannot trigger a threshold
    rw [csumS_range_succ, csumS_range_succ, hcm] at hj
    simp at hj
    rcases hj with hj | hj <;> linarith
  · -- Case 3.1: `d₂ > x^{1/5-5δ}`, `d₃ ≤ x^{1/3+2δ}/N`.
    have e2 : csumS t c0 1 (range (m + 1)) = csumS t c0 1 (range m) + t m := by
      rw [csumS_range_succ, hcm]; simp
    have e3 : csumS t c0 2 (range (m + 1)) = csumS t c0 2 (range m) := by
      rw [csumS_range_succ, hcm]; simp
    have hlow : 1 / 5 - 5 * δ < csumS t c0 1 (range (m + 1)) := by
      rcases hj with hj | hj
      · exact hj
      · rw [e3] at hj; linarith
    have hup : csumS t c0 1 (range (m + 1)) ≤ 4 / 15 - 5 * δ := by
      by_cases hm6 : m < 6
      · exact b2 _ (by omega)
      · have := h.tail_small m (by omega); rw [e2]; linarith
    set a2 := csumS t c0 1 (range (m + 1)) with ha2
    obtain ⟨c', g1, g3, g4⟩ := twoSlot t c0 (m + 1) R hjR 0 2 h02 (n - δ)
      (3 / 5 - 3 * δ - n - a2) (b1 _) (by rw [e3]; linarith)
      (fun k _ _ => by linarith [h.sq k])
    have g2 := g4 1 (by decide) (by decide)
    refine ⟨c', g1, ?_, ?_⟩ <;> rw [g2] <;> nlinarith
  · -- Case 3.2: `d₂ ≤ x^{1/5-5δ}`, `d₃ > x^{1/3+2δ}/N`.
    have e2 : csumS t c0 1 (range (m + 1)) = csumS t c0 1 (range m) := by
      rw [csumS_range_succ, hcm]; simp
    have hlow : 1 / 3 + 2 * δ - n < csumS t c0 2 (range (m + 1)) := by
      rcases hj with hj | hj
      · rw [e2] at hj; linarith
      · exact hj
    have hup := b3 (m + 1)
    set a3 := csumS t c0 2 (range (m + 1)) with ha3
    obtain ⟨c', g1, g2, g4⟩ := twoSlot t c0 (m + 1) R hjR 0 1 h01 (n - δ)
      (3 / 5 - 3 * δ - n - a3) (b1 _) (by rw [e2]; linarith)
      (fun k _ _ => by linarith [h.sq k])
    have g3 := g4 2 (by decide) (by decide)
    refine ⟨c', g1, ?_, ?_⟩ <;> rw [g3] <;> nlinarith

end Erdos287.Physical.Factor
