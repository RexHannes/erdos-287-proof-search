import RequestProject.Erdos287.AnchoredV4.Reconciliation

/-!
# Anchored V4 — bridge from the internal word model to the original Erdős #287 statement

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The internal objects of this programme are words on an interval: an interval `[aM, M]`, a set `Zf`
of omitted positions, and the reciprocal sum of the selected positions.  The original Erdős #287
question is about a finite set of integers `1 < n₁ < ⋯ < n_k` with `∑ 1/nᵢ = 1` and maximum
consecutive gap `≤ 2`.

This module proves the exact translation `final_configuration_is_counterexample`: **any** final
configuration of the V4 endgame — an interval word with non-adjacent omissions, selected
endpoints, and exact value `1` — *is* a #287 counterexample in the original sense.

This is a bridge theorem, not a counterexample: no such configuration is constructed anywhere in
this project, and the existence of one (via `ENTRY_EXISTENCE` and the two supply owners) remains
open.  Contrapositively, the bridge shows that if Erdős #287 is true then no ENTRY can be completed
by the V4 endgame — which is why the ENTRY question is the live owner.
-/

namespace Erdos287
namespace AnchoredV4

/-- The maximal consecutive gap of a finite set of integers is at most `2`. -/
def GapAtMostTwo (A : Finset ℕ) : Prop :=
  ∀ n ∈ A, (∀ m ∈ A, m ≤ n) ∨ ∃ m ∈ A, n < m ∧ m ≤ n + 2

/-- The original Erdős #287 counterexample statement: distinct integers `> 1` with reciprocal sum
exactly `1` and all consecutive gaps at most `2`. -/
def Erdos287Counterexample : Prop :=
  ∃ A : Finset ℕ, (∀ n ∈ A, 1 < n) ∧ recipSum A = 1 ∧ GapAtMostTwo A

/-- **Bridge theorem.**  A final V4 configuration is literally a #287 counterexample: the selected
positions of an interval word with non-adjacent omissions, selected endpoints and exact value `1`
form a set of distinct integers `> 1` with reciprocal sum `1` and all gaps `≤ 2`. -/
theorem final_configuration_is_counterexample {aM M : ℕ} {Zf : Finset ℕ}
    (haM : 1 < aM) (hZ : Zf ⊆ Finset.Ioo aM M) (hna : NoAdjacent Zf)
    (hval : wordSum (Finset.Icc aM M) Zf = 1) : Erdos287Counterexample := by
  classical
  refine ⟨Finset.Icc aM M \ Zf, ?_, hval, ?_⟩
  · intro n hn
    have := (Finset.mem_sdiff.1 hn).1
    simp only [Finset.mem_Icc] at this
    omega
  · intro n hn
    obtain ⟨hnI, hnZ⟩ := Finset.mem_sdiff.1 hn
    simp only [Finset.mem_Icc] at hnI
    by_cases hnM : n = M
    · left
      intro m hm
      have := (Finset.mem_sdiff.1 hm).1
      simp only [Finset.mem_Icc] at this
      omega
    · right
      have hlt : n < M := by omega
      by_cases h1 : n + 1 ∈ Zf
      · have h1I := hZ h1
        simp only [Finset.mem_Ioo] at h1I
        have h2 : n + 2 ∉ Zf := hna (n + 1) h1
        refine ⟨n + 2, Finset.mem_sdiff.2 ⟨?_, h2⟩, by omega, by omega⟩
        simp only [Finset.mem_Icc]
        omega
      · refine ⟨n + 1, Finset.mem_sdiff.2 ⟨?_, h1⟩, by omega, by omega⟩
        simp only [Finset.mem_Icc]
        omega

/-- **The bridge applied to the conditional endgame.**  ENTRY together with the two supply
hypotheses would produce an actual #287 counterexample.  Both supplies are open, so nothing is
claimed about #287 here; the theorem records exactly what a future proof of the supplies would
buy. -/
theorem conditional_entry_gives_counterexample {M aM Q Y : ℕ} (haM : 1 < aM)
    (e : Entry M aM Q Y) (hdesc : DescentSupply aM M Q Y e.mask)
    (habs : AbsorberSupply aM M Q Y e.mask) : Erdos287Counterexample := by
  obtain ⟨Zf, -, hsub, hna, -, -, hval⟩ := conditional_entry_to_exact_one e hdesc habs
  exact final_configuration_is_counterexample haM hsub hna hval

/-- **Contrapositive reading.**  If Erdős #287 is true (no counterexample exists), then no ENTRY
admits both supplies.  This is the precise sense in which the V4 endgame is a *test* of the
conjecture rather than a proof of it. -/
theorem no_entry_supply_of_no_counterexample (hno : ¬ Erdos287Counterexample)
    {M aM Q Y : ℕ} (haM : 1 < aM) (e : Entry M aM Q Y) :
    ¬ (DescentSupply aM M Q Y e.mask ∧ AbsorberSupply aM M Q Y e.mask) := by
  rintro ⟨hd, ha⟩
  exact hno (conditional_entry_gives_counterexample haM e hd ha)

end AnchoredV4
end Erdos287
