import RequestProject.Erdos287.FiniteRangeExtension

/-!
# Erdős Problem #287 — the exact remaining input, and the end-to-end compiler

Everything finite in this development is now packaged behind **one** predicate.

`WindowPairSupply M` says: there is a position `x` with `M/2 ≤ x < M` such that both `x`
and `x + 1` carry a prime power `p^e` whose window `⌊M/p^e⌋` is at most `9` and whose base
exceeds the certified numerator bound `C ⌊M/p^e⌋`.  By `Gap2CE.blocker_window` this single
condition refutes every counterexample with maximum `M`
(`Gap2CE.no_of_windowPairSupply`).

Three facts about this interface:

* it is **implied by** a (sign-sensitive) Sophie witness at `M`
  (`windowPairSupply_of_sophieWitness`), so it is a *weaker* — hence more plausible —
  arithmetic supply statement than the Sophie-Germain-type condition used previously;
* it holds for every `3 ≤ M ≤ 4·10⁹` by the kernel-checked certificate chain of
  `FiniteRangeExtension.lean`;
* it is **not proved here for large `M`**, and nothing in this project asserts it.  In the
  size range that matters, `⌊M/p^e⌋ ≤ 9` forces `p^e > M/10`, so the statement asks for two
  consecutive integers just above `M/2`, each with a prime-power divisor of size `≫ M`.
  Proving that for all large `M` is an analytic problem of Ford–Maynard type; it is *not*
  proved in this repository and is not assumed as an axiom anywhere.

`Erdos287ClosureInputs` bundles exactly the missing item together with an explicit,
effective threshold, and `no_Erdos287Counterexample_of_closure` compiles it into the exact
public statement.  No field of the structure is (or implies by definition) the conclusion:
the single mathematical field is the supply statement above the threshold.
-/

open scoped BigOperators

namespace Erdos287

/-- **The exact public statement of Erdős #287** (set form). -/
def Erdos287Statement : Prop := ∀ A : Finset ℕ, ¬ Erdos287Counterexample A

/-- **The window-pair supply at `M`.**  Two consecutive positions `x`, `x+1` in the top
half of `[1, M]`, each divisible by a prime power whose window at `M` is at most `9` and
whose base beats the certified numerator bound of that window. -/
def WindowPairSupply (M : ℕ) : Prop :=
  ∃ x pu au pv av : ℕ,
    pu.Prime ∧ pv.Prime ∧ 1 ≤ au ∧ 1 ≤ av ∧
    pu ^ au ∣ x ∧ pv ^ av ∣ (x + 1) ∧
    M / pu ^ au ≤ 9 ∧ CVal (M / pu ^ au) < pu ∧
    M / pv ^ av ≤ 9 ∧ CVal (M / pv ^ av) < pv ∧
    M ≤ 2 * x ∧ x + 1 ≤ M

namespace Gap2CE

variable (ce : Gap2CE)

/-- A window-pair supply at the maximum refutes the counterexample. -/
theorem no_of_windowPairSupply (h : WindowPairSupply ce.M) : False := by
  obtain ⟨x, pu, au, pv, av, hpu, hpv, hau, hav, hdu, hdv, hwu, hcu, hwv, hcv, hUx, hxL⟩ := h
  exact ce.blocker_window hpu hpv hau hav hdu hdv hwu hcu hwv hcv hUx hxL le_rfl le_rfl

end Gap2CE

/-- Division bound used below: `M < (c+1)·k` gives `⌊M/k⌋ ≤ c`. -/
theorem div_le_of_lt_mul {M k c : ℕ} (hk : 0 < k) (h : M < (c + 1) * k) : M / k ≤ c := by
  have := (Nat.div_lt_iff_lt_mul hk).2 h
  omega

/-- `CVal` at windows `0, 1` is `1`. -/
theorem CVal_eq_one_of_le_one {j : ℕ} (hj : j ≤ 1) : CVal j = 1 := by
  interval_cases j <;> norm_num [CVal]

/-- `CVal` at windows `≤ 2` is at most `3`. -/
theorem CVal_le_three_of_le_two {j : ℕ} (hj : j ≤ 2) : CVal j ≤ 3 := by
  interval_cases j <;> norm_num [CVal]

/-- **The Sophie interface is stronger than the window-pair interface.**  Every
sign-sensitive Sophie witness at `M` yields a window pair at `M`: for a plus witness take
`x = 2q` (window `2`, and `C 2 = 3 < q`) with `x + 1 = 2q + 1` prime (window `1`); for a
minus witness take `x = 2q - 1` prime (window `1`) with `x + 1 = 2q` (window `2`). -/
theorem windowPairSupply_of_sophieWitness {M : ℕ} (h : SophieWitness M) :
    WindowPairSupply M := by
  rcases h with ⟨q, hq, hq5, hM3, hfit, hp⟩ | ⟨q, hq, hq5, hM3, hfit, hp⟩
  · -- plus witness: `x = 2q`, `x + 1 = 2q + 1`
    have hwu : M / q ^ 1 ≤ 2 := by
      rw [pow_one]; exact div_le_of_lt_mul (by omega) (by omega)
    have hwv : M / (2 * q + 1) ^ 1 ≤ 1 := by
      rw [pow_one]; exact div_le_of_lt_mul (by omega) (by omega)
    refine ⟨2 * q, q, 1, 2 * q + 1, 1, hq, hp, le_rfl, le_rfl, ⟨2, by rw [pow_one]; ring⟩,
      ⟨1, by rw [pow_one, mul_one]⟩, by omega, ?_, by omega, ?_, by omega, by omega⟩
    · have := CVal_le_three_of_le_two hwu; omega
    · have := CVal_eq_one_of_le_one hwv; omega
  · -- minus witness: `x = 2q - 1`, `x + 1 = 2q`
    have hwu : M / (2 * q - 1) ^ 1 ≤ 1 := by
      rw [pow_one]; exact div_le_of_lt_mul (by omega) (by omega)
    have hwv : M / q ^ 1 ≤ 2 := by
      rw [pow_one]; exact div_le_of_lt_mul (by omega) (by omega)
    refine ⟨2 * q - 1, 2 * q - 1, 1, q, 1, hp, hq, le_rfl, le_rfl,
      ⟨1, by rw [pow_one, mul_one]⟩, ⟨2, by rw [pow_one]; omega⟩,
      by omega, ?_, by omega, ?_, by omega, by omega⟩
    · have := CVal_eq_one_of_le_one hwu; omega
    · have := CVal_le_three_of_le_two hwv; omega

/-- **The end-to-end closure inputs.**  Exactly one mathematical field: the window-pair
supply above an explicit threshold that lies inside the kernel-verified finite range.
No field is the conclusion, and no field mentions counterexamples. -/
structure Erdos287ClosureInputs where
  /-- An explicit, effective threshold. -/
  M0 : ℕ
  /-- The threshold lies inside the kernel-verified finite range `[3, 4·10⁹]`. -/
  threshold_covered : M0 ≤ 4000000000
  /-- The supply statement above the threshold.  **Not proved in this repository.** -/
  supply : ∀ M : ℕ, M0 ≤ M → WindowPairSupply M

/-- **End-to-end compiler.**  The closure inputs imply the exact public statement. -/
theorem no_Erdos287Counterexample_of_closure (I : Erdos287ClosureInputs) :
    Erdos287Statement := by
  intro A h
  by_cases hM : A.max' h.nonempty ≤ 4000000000
  · exact no_Erdos287Counterexample_of_max_le_4e9 h hM
  · refine (h.toGap2CE).no_of_windowPairSupply ?_
    exact I.supply _ (by
      show I.M0 ≤ A.max' h.nonempty
      have := I.threshold_covered
      omega)

/-- **Ordered (public) form of the same compiler.** -/
theorem erdos287_seq_of_closure (I : Erdos287ClosureInputs)
    (k : ℕ) (n : ℕ → ℕ)
    (hmono : ∀ i j, i < j → j < k → n i < n j)
    (hone : ∀ i, i < k → 1 < n i)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / (n i) = 1) :
    ∃ i, i + 1 < k ∧ n i + 3 ≤ n (i + 1) :=
  erdos287_seq_of_no_counterexample (no_Erdos287Counterexample_of_closure I) k n hmono hone hsum

end Erdos287
