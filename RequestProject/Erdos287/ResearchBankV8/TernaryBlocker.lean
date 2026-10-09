import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V8 §2G: ternary / multirow blocker fixtures

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A finite **truth-table level** fixture of the `p = 107`-style phenomenon: three rows, each of
which forces *exactly one* physical zero among two coordinates of a physical path `a – b – c`
carrying the no-`00` guard.

* `pairwise_extendible` — any two of the rows are jointly satisfiable together with the guard;
* `ternary_incompatible` — all three rows together are UNSAT;
* `pairwise_compatibility_not_sufficient` — hence the abstract principle "pairwise compatibility
  ⇒ joint compatibility" is false.

`PAIRWISE_COMPATIBILITY_NOT_SUFFICIENT` is a **proved finite/abstract fact**.  The actual
`p = 107` row data are not re-derived here, and **no asymptotic blocker theorem is inferred**
from this fixture.
-/

namespace Erdos287
namespace ResearchBankV8
namespace TernaryBlocker

/-- A physical assignment of the three path coordinates `a – b – c`. -/
abbrev Assign := Bool × Bool × Bool

/-- The physical no-`00` guard on the path `a – b – c`. -/
def guard (x : Assign) : Bool := (x.1 || x.2.1) && (x.2.1 || x.2.2)

/-- Row `R₁`: exactly one of `a, b` is a (forced) zero. -/
def R₁ (x : Assign) : Bool := x.1 != x.2.1
/-- Row `R₂`: exactly one of `b, c` is a (forced) zero. -/
def R₂ (x : Assign) : Bool := x.2.1 != x.2.2
/-- Row `R₃`: exactly one of `a, c` is a (forced) zero. -/
def R₃ (x : Assign) : Bool := x.1 != x.2.2

/-- **Pairwise extendibility** (each witness also satisfies the physical guard). -/
theorem pairwise_extendible :
    (guard (true, false, true) && R₁ (true, false, true) && R₂ (true, false, true)) = true ∧
    (guard (false, true, true) && R₁ (false, true, true) && R₃ (false, true, true)) = true ∧
    (guard (true, true, false) && R₂ (true, true, false) && R₃ (true, true, false)) = true := by
  decide

/-- **Ternary incompatibility.** -/
theorem ternary_incompatible : ∀ x : Assign, (R₁ x && R₂ x && R₃ x) = false := by decide

/-- With the physical guard added the triple is still UNSAT (the obstruction is a parity one). -/
theorem ternary_incompatible_with_guard :
    ∀ x : Assign, (guard x && R₁ x && R₂ x && R₃ x) = false := by decide

/-- **`PAIRWISE_COMPATIBILITY_NOT_SUFFICIENT`.**  The principle "a finite family of Boolean
constraints that is pairwise satisfiable is jointly satisfiable" is false. -/
theorem pairwise_compatibility_not_sufficient :
    ¬ ∀ (rows : List (Assign → Bool)),
      (∀ r ∈ rows, ∀ s ∈ rows, ∃ x, guard x = true ∧ r x = true ∧ s x = true) →
        ∃ x, guard x = true ∧ ∀ r ∈ rows, r x = true := by
  intro h
  obtain ⟨x, -, hx⟩ := h [R₁, R₂, R₃] (by
    intro r hr s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hs
    rcases hr with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl <;>
      first
      | exact ⟨(true, false, true), by decide⟩
      | exact ⟨(false, true, true), by decide⟩
      | exact ⟨(true, true, false), by decide⟩)
  have h1 := hx R₁ (by simp)
  have h2 := hx R₂ (by simp)
  have h3 := hx R₃ (by simp)
  have := ternary_incompatible x
  rw [h1, h2, h3] at this
  exact absurd this (by decide)

end TernaryBlocker
end ResearchBankV8
end Erdos287
