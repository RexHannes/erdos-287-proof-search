import Mathlib
import RequestProject.Erdos287.ProblemStatement

/-!
# Erdős #287 — Route D (Direct Reciprocal programme), core definitions

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This namespace (`Erdos287.Direct`) is a *new, append-only* development.  It is a second,
alternative proof route ("Route D"), and it is deliberately kept disjoint from the existing
Source / FivePrime / Directed-Selberg / Physical-`k=1` programme ("Route S").  No node of
one route discharges a node of the other unless an explicit bridge theorem is proved; see
`Direct/Reconciliation.lean`.

This file fixes the combinatorial source of Route D:

* the ambient interval `I = [a, M]` and a Boolean selection `eps`;
* the selected set `A = selected a M eps` and its reciprocal sum;
* the endpoint-selected predicate and the no-two-consecutive-omissions predicate;
* the exact Route-D counterexample predicate `DirectCounterexample`;
* the two bridges to the project's exact predicate `Erdos287Counterexample`, proved in both
  directions (no equivalence is asserted by comment only).

All conventions are explicit: positions are natural numbers, reciprocal sums are rational.
-/

open scoped BigOperators

namespace Erdos287
namespace Direct

/-! ## D.1  The ambient interval, the selection and the selected set -/

/-- The ambient interval `I = [a, M]` of Route D. -/
def ambient (a M : ℕ) : Finset ℕ := Finset.Icc a M

/-- The set selected by the Boolean mask `eps` inside `[a, M]`. -/
def selected (a M : ℕ) (eps : ℕ → Bool) : Finset ℕ :=
  (ambient a M).filter (fun n => eps n = true)

@[simp] theorem mem_selected {a M : ℕ} {eps : ℕ → Bool} {n : ℕ} :
    n ∈ selected a M eps ↔ (a ≤ n ∧ n ≤ M) ∧ eps n = true := by
  simp [selected, ambient, Finset.mem_filter, Finset.mem_Icc, and_assoc]

theorem selected_subset_ambient (a M : ℕ) (eps : ℕ → Bool) :
    selected a M eps ⊆ ambient a M := Finset.filter_subset _ _

/-- The reciprocal sum of a finite set of positions. -/
def recipSum (A : Finset ℕ) : ℚ := ∑ n ∈ A, (1 : ℚ) / n

@[simp] theorem recipSum_empty : recipSum ∅ = 0 := by simp [recipSum]

theorem recipSum_insert {A : Finset ℕ} {n : ℕ} (h : n ∉ A) :
    recipSum (insert n A) = (1 : ℚ) / n + recipSum A := by
  simp [recipSum, Finset.sum_insert h]

/-! ## D.2  The two structural predicates -/

/-- Both endpoints of the ambient interval are selected. -/
def EndpointSelected (a M : ℕ) (eps : ℕ → Bool) : Prop := eps a = true ∧ eps M = true

/-- No two consecutive positions of `[a, M]` are simultaneously omitted. -/
def NoTwoConsecutiveOmissions (a M : ℕ) (eps : ℕ → Bool) : Prop :=
  ∀ n : ℕ, a ≤ n → n + 1 ≤ M → eps n = true ∨ eps (n + 1) = true

/-- **The exact Route-D counterexample predicate.** -/
structure DirectCounterexample (a M : ℕ) (eps : ℕ → Bool) : Prop where
  /-- the least position exceeds `1` -/
  one_lt : 1 < a
  /-- the interval is nondegenerate -/
  lt : a < M
  /-- both endpoints are selected -/
  endpoints : EndpointSelected a M eps
  /-- omissions are isolated -/
  isolated : NoTwoConsecutiveOmissions a M eps
  /-- the selected reciprocals sum to `1` -/
  sum_one : recipSum (selected a M eps) = 1

/-! ## D.3  Elementary consequences of the two structural predicates -/

theorem left_mem_selected {a M : ℕ} {eps : ℕ → Bool} (hle : a ≤ M)
    (h : EndpointSelected a M eps) : a ∈ selected a M eps := by
  simp [mem_selected, hle, h.1]

theorem right_mem_selected {a M : ℕ} {eps : ℕ → Bool} (hle : a ≤ M)
    (h : EndpointSelected a M eps) : M ∈ selected a M eps := by
  simp [mem_selected, hle, h.2]

/-- An omitted position strictly inside the interval has both neighbours selected. -/
theorem neighbours_selected_of_omitted {a M : ℕ} {eps : ℕ → Bool}
    (hiso : NoTwoConsecutiveOmissions a M eps) {n : ℕ}
    (hlo : a < n) (hhi : n < M) (hn : eps n = false) :
    eps (n - 1) = true ∧ eps (n + 1) = true := by
  constructor
  · have := hiso (n - 1) (by omega) (by omega)
    rcases this with h | h
    · exact h
    · rw [show n - 1 + 1 = n by omega] at h; rw [hn] at h; exact absurd h (by simp)
  · have := hiso n (by omega) (by omega)
    rcases this with h | h
    · rw [hn] at h; exact absurd h (by simp)
    · exact h

/-- Every gap of the selected set is at most `2`. -/
theorem gap_le_two_of_isolated {a M : ℕ} {eps : ℕ → Bool}
    (hend : EndpointSelected a M eps) (hiso : NoTwoConsecutiveOmissions a M eps)
    {n : ℕ} (hn : n ∈ selected a M eps) (hlt : n < M) :
    n + 1 ∈ selected a M eps ∨ n + 2 ∈ selected a M eps := by
  rw [mem_selected] at hn
  obtain ⟨⟨hna, hnM⟩, _⟩ := hn
  by_cases hM : n + 1 = M
  · left; rw [mem_selected]; exact ⟨⟨by omega, by omega⟩, by rw [hM]; exact hend.2⟩
  · have h := hiso (n + 1) (by omega) (by omega)
    rcases h with h | h
    · left; exact mem_selected.2 ⟨⟨by omega, by omega⟩, h⟩
    · right; exact mem_selected.2 ⟨⟨by omega, by omega⟩, by simpa [Nat.add_assoc] using h⟩

/-! ## D.4  Bridges to the project's exact `Erdos287Counterexample` predicate

These are proved, not asserted.  The forward bridge shows Route D's source really is a
source of counterexamples to #287; the backward bridge shows nothing is lost by working
with masks. -/

/-- **`directCounterexample_to_exact`.**  `KERNEL-PROVED`.  A Route-D counterexample yields
an exact `Erdos287Counterexample`. -/
theorem directCounterexample_to_exact {a M : ℕ} {eps : ℕ → Bool}
    (h : DirectCounterexample a M eps) : Erdos287Counterexample (selected a M eps) := by
  have hle : a ≤ M := le_of_lt h.lt
  have ha : a ∈ selected a M eps := left_mem_selected hle h.endpoints
  have hM : M ∈ selected a M eps := right_mem_selected hle h.endpoints
  refine ⟨?_, ?_, h.sum_one, ?_⟩
  · have hsub : ({a, M} : Finset ℕ) ⊆ selected a M eps := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ha
      · rw [Finset.mem_singleton] at hx; subst hx; exact hM
    have hcard : ({a, M} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [Nat.ne_of_lt h.lt]), Finset.card_singleton]
    calc (2 : ℕ) = ({a, M} : Finset ℕ).card := hcard.symm
      _ ≤ (selected a M eps).card := Finset.card_le_card hsub
  · intro x hx
    rw [mem_selected] at hx
    exact lt_of_lt_of_le h.one_lt hx.1.1
  · intro x hx hex
    obtain ⟨b, hb, hxb⟩ := hex
    have hbM : b ≤ M := (mem_selected.1 hb).1.2
    exact gap_le_two_of_isolated h.endpoints h.isolated hx (by omega)

/-- **`exact_to_directCounterexample`.**  `KERNEL-PROVED`.  Conversely, every exact
`Erdos287Counterexample` is the selected set of a Route-D counterexample on its own
min/max window, with `eps` the membership mask. -/
theorem exact_to_directCounterexample {A : Finset ℕ} (h : Erdos287Counterexample A) :
    DirectCounterexample (A.min' h.nonempty) (A.max' h.nonempty)
      (fun n => decide (n ∈ A)) ∧
      selected (A.min' h.nonempty) (A.max' h.nonempty) (fun n => decide (n ∈ A)) = A := by
  set N := A.min' h.nonempty with hN
  set M := A.max' h.nonempty with hMdef
  have hNmem : N ∈ A := Finset.min'_mem _ _
  have hMmem : M ∈ A := Finset.max'_mem _ _
  have hsel : selected N M (fun n => decide (n ∈ A)) = A := by
    ext x
    simp only [mem_selected, decide_eq_true_eq]
    constructor
    · exact fun hx => hx.2
    · intro hx
      exact ⟨⟨Finset.min'_le _ _ hx, Finset.le_max' _ _ hx⟩, hx⟩
  have hNM : N < M := by
    rcases lt_trichotomy N M with hlt | heq | hgt
    · exact hlt
    · exfalso
      have hcard := h.card_ge
      have : A ⊆ {N} := by
        intro x hx
        have h1 : N ≤ x := Finset.min'_le _ _ hx
        have h2 : x ≤ M := Finset.le_max' _ _ hx
        rw [← heq] at h2
        simp [Finset.mem_singleton]; omega
      have := Finset.card_le_card this
      simp at this; omega
    · exact absurd (Finset.min'_le _ _ hMmem) (by omega)
  refine ⟨⟨h.one_lt N hNmem, hNM, ⟨by simpa using hNmem, by simpa using hMmem⟩, ?_, ?_⟩, hsel⟩
  · intro n hn hn'
    have := (h.toGap2CE).holes_isolated n (by simpa [Gap2CE.N, hN] using hn)
      (by simpa [Gap2CE.M, hMdef] using hn')
    simpa using this
  · rw [hsel]; exact h.sum_one

end Direct
end Erdos287
