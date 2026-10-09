import RequestProject.Erdos287.Anchored.ReciprocalState

/-!
# The finite anchored fingerprint

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For a finite anchored state `(C, P, N)` the *fingerprint* is the finite integer product

`F_C(P,N) = ∏_{v ∈ 𝒱_C(P,N), v > 0} num v`,

taken over the strictly positive permitted values only; the zero value is handled separately
and is never encoded as a numerator.  The main theorem is the exact equivalence

`AnchoredFeasible p C P N ↔ (zero state allowed) ∨ p ∣ F_C(P,N)`,

valid for every prime `p`.  **No claim whatsoever is made about the size of `F`** — it is a
finite integer, and no asymptotic statement about it occurs anywhere in this namespace.
-/

open scoped BigOperators

namespace Erdos287
namespace Anchored

/-- The strictly positive permitted values. -/
def positiveValues (C P N : Finset ℕ) : Finset ℚ :=
  (valueSet C P N).filter (fun v => 0 < v)

@[simp] theorem mem_positiveValues {C P N : Finset ℕ} {v : ℚ} :
    v ∈ positiveValues C P N ↔ v ∈ valueSet C P N ∧ 0 < v := by
  simp [positiveValues]

/-- The finite anchored fingerprint `F_C(P,N)`. -/
def fingerprint (C P N : Finset ℕ) : ℤ := ∏ v ∈ positiveValues C P N, v.num

/-- **`anchoredFeasible_iff_fingerprint`.**  `KERNEL-PROVED`.  The exact finite criterion:
local feasibility holds iff the zero state is allowed or `p` divides the fingerprint. -/
theorem anchoredFeasible_iff_fingerprint (p : ℕ) [hp : Fact p.Prime] (C P N : Finset ℕ) :
    AnchoredFeasible p C P N ↔
      ((0 : ℚ) ∈ valueSet C P N) ∨ (p : ℤ) ∣ fingerprint C P N := by
  have hpZ : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp.out
  rw [anchoredFeasible_iff_num]
  constructor
  · rintro ⟨E, hE, h⟩
    rcases h with h | h
    · exact Or.inl (mem_valueSet.2 ⟨E, hE, h⟩)
    · by_cases h0 : recipSum E = 0
      · exact Or.inl (mem_valueSet.2 ⟨E, hE, h0⟩)
      · refine Or.inr ?_
        have hmem : recipSum E ∈ positiveValues C P N :=
          mem_positiveValues.2 ⟨mem_valueSet.2 ⟨E, hE, rfl⟩,
            lt_of_le_of_ne (recipSum_nonneg E) (Ne.symm h0)⟩
        exact dvd_trans h (Finset.dvd_prod_of_mem (fun v : ℚ => v.num) hmem)
  · rintro (h | h)
    · obtain ⟨E, hE, hE0⟩ := mem_valueSet.1 h
      exact ⟨E, hE, Or.inl hE0⟩
    · rw [fingerprint, hpZ.dvd_finset_prod_iff] at h
      obtain ⟨v, hv, hdvd⟩ := h
      obtain ⟨hvmem, _⟩ := mem_positiveValues.1 hv
      obtain ⟨E, hE, hEv⟩ := mem_valueSet.1 hvmem
      exact ⟨E, hE, Or.inr (by rw [hEv]; exact hdvd)⟩

/-- The fingerprint criterion makes local feasibility *exactly decidable*: the right-hand
side is a finite, purely arithmetic condition. -/
instance decidableAnchoredFeasible (p : ℕ) [Fact p.Prime] (C P N : Finset ℕ) :
    Decidable (AnchoredFeasible p C P N) :=
  decidable_of_iff _ (anchoredFeasible_iff_fingerprint p C P N).symm

/-- With positive cofactors the zero state is allowed exactly when `P = ∅`, so the criterion
takes the fully explicit form used downstream. -/
theorem anchoredFeasible_iff_fingerprint_of_pos (p : ℕ) [Fact p.Prime] {C P N : Finset ℕ}
    (hC : ∀ c ∈ C, 0 < c) :
    AnchoredFeasible p C P N ↔ (P = ∅ ∨ (p : ℤ) ∣ fingerprint C P N) := by
  rw [anchoredFeasible_iff_fingerprint p C P N, zero_mem_valueSet_iff hC]

end Anchored
end Erdos287
