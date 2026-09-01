import Mathlib
import RequestProject.CurrentProgramme.Erdos287FixedBudgetV22Arithmetic

/-!
# The all-`A` firewall

`STRONG ALL-A SUPERSQRT : OPEN / NONCONTROLLING`

The fixed-budget route consumes a correlation bound **at one fixed log exponent** `A`,
with one implied constant.  It does *not* consume, and must never be allowed to consume,
the arbitrary-`A` object

```
    ∀ A, ∃ C_A, |E(X)| ≤ C_A · X / (log X)^A .
```

This file separates the two predicates and proves the only valid implication together with
its refutation in the other direction.  **The arbitrary-`A` object is not derived anywhere.**
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace AllAFirewall

/-! ## §1.  The two correlation inputs -/

/-- **`FixedBudgetCorrelationInput`** — a correlation bound at **one** fixed log exponent
`A` with **one** explicit implied constant. -/
def FixedBudgetCorrelationInput (E : ℝ → ℝ) (Cerr : ℝ) (A : ℕ) : Prop :=
  0 < Cerr ∧ ∀ X : ℝ, 2 ≤ X → |E X| ≤ Cerr * X / (Real.log X) ^ A

/-- **`ArbitraryLogCorrelationInput`** — the all-`A` object: a correlation bound at *every*
log exponent, each with its own implied constant. -/
def ArbitraryLogCorrelationInput (E : ℝ → ℝ) : Prop :=
  ∀ A : ℕ, ∃ Cerr : ℝ, 0 < Cerr ∧ ∀ X : ℝ, 2 ≤ X → |E X| ≤ Cerr * X / (Real.log X) ^ A

/-! ## §2.  The only valid implication -/

/-- **`fixedBudget_of_arbitrary`.**  `KERNEL-PROVED`.

The all-`A` object supplies a fixed-budget input at every exponent.  This is the direction
that is logically valid, and it is the direction that is *not* used: the fixed-budget route
never needs it. -/
theorem fixedBudget_of_arbitrary {E : ℝ → ℝ} (h : ArbitraryLogCorrelationInput E) (A : ℕ) :
    ∃ Cerr : ℝ, FixedBudgetCorrelationInput E Cerr A := by
  obtain ⟨Cerr, hC, hb⟩ := h A
  exact ⟨Cerr, hC, hb⟩

/-! ## §3.  The firewall -/

/-- **`arbitrary_not_of_fixedBudget`.**  `KERNEL-PROVED`.

A fixed-budget correlation input does **not** yield the all-`A` object.  Witness:
`E(X) = X`, which satisfies the fixed budget at `A = 0` with constant `1`, but fails every
bound with `A = 1`. -/
theorem arbitrary_not_of_fixedBudget :
    ∃ (E : ℝ → ℝ) (Cerr : ℝ) (A : ℕ),
      FixedBudgetCorrelationInput E Cerr A ∧ ¬ ArbitraryLogCorrelationInput E := by
  refine ⟨fun X => X, 1, 0, ⟨one_pos, ?_⟩, ?_⟩
  · intro X hX
    have hX0 : (0 : ℝ) ≤ X := by linarith
    simp [abs_of_nonneg hX0]
  · intro hall
    obtain ⟨C, hC, hb⟩ := hall 1
    set X : ℝ := Real.exp (C + 1) with hXdef
    have hlog : Real.log X = C + 1 := by rw [hXdef, Real.log_exp]
    have hXpos : (0 : ℝ) < X := Real.exp_pos _
    have hX2 : (2 : ℝ) ≤ X := by
      have h1 : Real.exp 1 ≤ Real.exp (C + 1) := by
        apply Real.exp_le_exp.2; linarith
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      rw [hXdef]; linarith
    have h := hb X hX2
    rw [abs_of_nonneg (le_of_lt hXpos), hlog, pow_one] at h
    have hden : (0 : ℝ) < C + 1 := by linarith
    rw [le_div_iff₀ hden] at h
    nlinarith [hXpos]

/-- **`allA_object_is_noncontrolling`.**  `KERNEL-PROVED`.

Restatement of the firewall as a status fact: the fixed-budget input is strictly weaker, so
nothing that consumes only the fixed-budget input may be described as needing — or as
proving — the strong all-`A` statement. -/
theorem allA_object_is_noncontrolling :
    (∀ (E : ℝ → ℝ), ArbitraryLogCorrelationInput E → ∀ A : ℕ,
        ∃ Cerr : ℝ, FixedBudgetCorrelationInput E Cerr A) ∧
      ∃ (E : ℝ → ℝ) (Cerr : ℝ) (A : ℕ),
        FixedBudgetCorrelationInput E Cerr A ∧ ¬ ArbitraryLogCorrelationInput E :=
  ⟨fun _ h A => fixedBudget_of_arbitrary h A, arbitrary_not_of_fixedBudget⟩

/-- Neither object is inhabited here: the fixed-budget predicate is a genuine restriction
too. -/
theorem fixedBudgetCorrelation_not_automatic :
    ∃ (E : ℝ → ℝ) (Cerr : ℝ) (A : ℕ), ¬ FixedBudgetCorrelationInput E Cerr A := by
  refine ⟨fun _ => 1, 0, 0, ?_⟩
  rintro ⟨hC, -⟩
  exact lt_irrefl 0 hC

end AllAFirewall
end Erdos287
