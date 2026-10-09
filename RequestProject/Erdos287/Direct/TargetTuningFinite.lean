import RequestProject.Erdos287.Direct.ProtectedSwitches

/-!
# Route D — the deterministic target-tuning bridge

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The tuning step is split honestly into

* **analytic inputs**, stated as named interface propositions and never proved here:
  `CoarseSwitchSupply` (a chain of admissible masks exists), `FineSwitchSupply` (its steps are
  at most `E`), `HarmonicInterior` (the chain starts at value `≤ 1` and ends at value `≥ 1`),
  `SparseRepairCost` (a uniform size budget along the chain);
* a **deterministic bridge**, kernel-proved: those inputs imply exact straddling
  `1 − E ≤ R₋ ≤ 1 ≤ R₊ ≤ 1 + E` by two admissible masks obeying the cost budget
  (`targetTuning_of`).

The crossing argument itself (`greedy_crossing`) is a self-contained finite lemma.

Nothing here upgrades approximate straddling to exact equality; see
`Direct/Reconciliation.lean` for the explicit refutation of that step.
-/

open scoped BigOperators

namespace Erdos287
namespace Direct

/-! ## D.32  The finite greedy crossing lemma -/

/-- **`greedy_crossing`.**  `KERNEL-PROVED`.  A finite sequence starting at value `≤ 1`, ending
at value `≥ 1`, with upward steps at most `E ≥ 0`, straddles `1` within `E` on both sides. -/
theorem greedy_crossing {K : ℕ} (f : ℕ → ℚ) (E : ℚ) (hE : 0 ≤ E)
    (hstart : f 0 ≤ 1) (hend : 1 ≤ f K) (hstep : ∀ i, i < K → f (i + 1) - f i ≤ E) :
    ∃ i ≤ K, ∃ j ≤ K, 1 - E ≤ f i ∧ f i ≤ 1 ∧ 1 ≤ f j ∧ f j ≤ 1 + E := by
  classical
  have hex : ∃ j, 1 ≤ f j ∧ j ≤ K := ⟨K, hend, le_rfl⟩
  set P : ℕ → Prop := fun j => 1 ≤ f j ∧ j ≤ K with hP
  have hdec : DecidablePred P := Classical.decPred P
  let j₀ := Nat.find (p := P) (by exact hex)
  have hj₀ : P j₀ := Nat.find_spec (p := P) hex
  obtain ⟨hj₀1, hj₀K⟩ := hj₀
  rcases Nat.eq_zero_or_pos j₀ with h0 | hpos
  · -- the sequence already starts at exactly `1`
    have hf0 : f 0 = 1 := by
      have : (1 : ℚ) ≤ f 0 := by rw [← h0]; exact hj₀1
      linarith
    exact ⟨0, Nat.zero_le _, 0, Nat.zero_le _, by rw [hf0]; linarith, by rw [hf0],
      by rw [hf0], by rw [hf0]; linarith⟩
  · have hprev : ¬ P (j₀ - 1) := Nat.find_min (p := P) hex (by omega)
    have hprevle : j₀ - 1 ≤ K := by omega
    have hlt : f (j₀ - 1) < 1 := by
      by_contra hcon
      exact hprev ⟨le_of_not_gt hcon, hprevle⟩
    have hstepj : f (j₀ - 1 + 1) - f (j₀ - 1) ≤ E := hstep (j₀ - 1) (by omega)
    have hsucc : j₀ - 1 + 1 = j₀ := by omega
    rw [hsucc] at hstepj
    exact ⟨j₀ - 1, hprevle, j₀, hj₀K, by linarith, le_of_lt hlt, hj₀1, by linarith⟩

/-! ## D.33  The named analytic interfaces (OPEN, never axioms) -/

/-- A mask is *admissible* on `[a, M]` when it pins both endpoints and never omits two
consecutive positions. -/
def Admissible (a M : ℕ) (eps : ℕ → Bool) : Prop :=
  EndpointSelected a M eps ∧ NoTwoConsecutiveOmissions a M eps

/-- **Interface (open): coarse switch supply.**  A chain of admissible masks of length `K`
exists on the window. -/
def CoarseSwitchSupply (a M K : ℕ) (ch : ℕ → (ℕ → Bool)) : Prop :=
  ∀ i ≤ K, Admissible a M (ch i)

/-- **Interface (open): fine switch supply.**  Consecutive chain members move the reciprocal
value upward by at most `E`. -/
def FineSwitchSupply (a M K : ℕ) (ch : ℕ → (ℕ → Bool)) (E : ℚ) : Prop :=
  ∀ i < K, recipSum (selected a M (ch (i + 1))) - recipSum (selected a M (ch i)) ≤ E

/-- **Interface (open): harmonic interior.**  The chain starts below the target and ends above
it. -/
def HarmonicInterior (a M K : ℕ) (ch : ℕ → (ℕ → Bool)) : Prop :=
  recipSum (selected a M (ch 0)) ≤ 1 ∧ 1 ≤ recipSum (selected a M (ch K))

/-- **Interface (open): sparse repair cost.**  A uniform size budget along the chain. -/
def SparseRepairCost (a M K : ℕ) (ch : ℕ → (ℕ → Bool)) (budget : ℕ) : Prop :=
  ∀ i ≤ K, (selected a M (ch i)).card ≤ budget

/-- The conclusion of the tuning step: two admissible masks straddling the target within `E`,
both inside the cost budget. -/
def TargetStraddling (a M : ℕ) (E : ℚ) (budget : ℕ) : Prop :=
  ∃ epsLo epsHi : ℕ → Bool,
    Admissible a M epsLo ∧ Admissible a M epsHi ∧
      (selected a M epsLo).card ≤ budget ∧ (selected a M epsHi).card ≤ budget ∧
      1 - E ≤ recipSum (selected a M epsLo) ∧ recipSum (selected a M epsLo) ≤ 1 ∧
      1 ≤ recipSum (selected a M epsHi) ∧ recipSum (selected a M epsHi) ≤ 1 + E

/-! ## D.34  The deterministic bridge -/

/-- **`targetTuning_of`.**  `KERNEL-PROVED` bridge, `CONDITIONAL` on the four named interfaces.
Given a chain of admissible masks with bounded steps, harmonic interior and a uniform cost
budget, exact straddling holds.  No analytic statement is proved here: the interfaces are
hypotheses. -/
theorem targetTuning_of {a M K : ℕ} {ch : ℕ → (ℕ → Bool)} {E : ℚ} {budget : ℕ} (hE : 0 ≤ E)
    (hCoarse : CoarseSwitchSupply a M K ch) (hFine : FineSwitchSupply a M K ch E)
    (hHarm : HarmonicInterior a M K ch) (hCost : SparseRepairCost a M K ch budget) :
    TargetStraddling a M E budget := by
  obtain ⟨i, hiK, j, hjK, h1, h2, h3, h4⟩ :=
    greedy_crossing (fun i => recipSum (selected a M (ch i))) E hE hHarm.1 hHarm.2 hFine
  exact ⟨ch i, ch j, hCoarse i hiK, hCoarse j hjK, hCost i hiK, hCost j hjK, h1, h2, h3, h4⟩

/-- **`targetStraddling_is_not_exactness`.**  `KERNEL-PROVED` firewall.  Straddling within `E`
does **not** give an exact hit: for `E = 1/2` the two rational values `1/2` and `3/2` satisfy
every inequality of `TargetStraddling` while neither equals `1`. -/
theorem targetStraddling_is_not_exactness :
    (1 : ℚ) - 1 / 2 ≤ 1 / 2 ∧ (1 : ℚ) / 2 ≤ 1 ∧ (1 : ℚ) ≤ 3 / 2 ∧ (3 : ℚ) / 2 ≤ 1 + 1 / 2 ∧
      (1 : ℚ) / 2 ≠ 1 ∧ (3 : ℚ) / 2 ≠ 1 := by
  norm_num

end Direct
end Erdos287
