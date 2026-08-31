import Mathlib
import RequestProject.CurrentProgramme.PostRepairOwnerCompiler

/-!
# CurrentProgramme (post-Balanced7 pass) §16 — the K0 uniform fragmentation compiler

`287-K0-SP2-UNIFORM-FRAGMENTATION-REASSEMBLY45` is banked here as
`REDUCED / CONDITIONAL`, **not** activated.

What is proved is the purely logical reassembly compiler: if a physical sum `R` fragments
into finitely many uniform pieces, each of which is `o(X / log X)`, then `R` is
`o(X / log X)`.  The antecedent bundle additionally *requires* the Balanced7 conclusion and
the `Ω(d) ≥ 3` small-prime-prefix Type-II source as explicit hypotheses; neither is
available, so nothing is activated.

`k0_residual_is_three_prefix` records that the outstanding downstream residual is exactly
`287-K0-SP2-THREE-SMALLPRIME-PREFIX-TYPEII45`: with that source absent the bundle can never
be formed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace PostBalanced7Pro

open Erdos287.CurrentProgramme

/-! ## §16.1  The fragmentation bundle -/

/-- **`K0UniformFragmentationInputs`** — `CONDITIONAL BUNDLE / NOT INHABITED`.

`frag k` are the `K` fragments of the physical sum `R`. -/
structure K0UniformFragmentationInputs
    (R : ℝ → ℝ) (frag : ℕ → ℝ → ℝ) (K : ℕ)
    (balancedSevenSupplied threePrefixSupplied : Prop) : Prop where
  /-- The Balanced7 asymptotic conclusion is supplied (it is **not** available). -/
  balanced_seven : balancedSevenSupplied
  /-- The `Ω(d) ≥ 3` small-prime-prefix Type-II source is supplied (it is **not**
  available): this is the first exact downstream residual. -/
  three_prefix : threePrefixSupplied
  /-- The fragmentation is finite and nontrivial. -/
  fragment_count : 0 < K
  /-- Exact reassembly of the physical sum from its fragments. -/
  fragmentation : ∀ X : ℝ, R X = ∑ k ∈ Finset.range K, frag k X
  /-- Each fragment saves uniformly. -/
  uniform_savings : ∀ k : ℕ, ∀ eps : ℝ, 0 < eps →
    ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → |frag k X| ≤ eps * X / Real.log X

/-- **`k0_uniform_fragmentation_compiler`.**  `LEAN_PROVED` (purely logical implication).

Finitely many uniformly small fragments reassemble to an `o(X / log X)` sum. -/
theorem k0_uniform_fragmentation_compiler
    {R : ℝ → ℝ} {frag : ℕ → ℝ → ℝ} {K : ℕ} {balancedSevenSupplied threePrefixSupplied : Prop}
    (h : K0UniformFragmentationInputs R frag K balancedSevenSupplied threePrefixSupplied) :
    BalancedSevenAsymptoticConclusion R := by
  intro eps heps
  have hKpos := h.fragment_count
  have hK : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hpos : 0 < eps / K := by positivity
  choose X0 hX0 using fun k : ℕ => h.uniform_savings k (eps / K) hpos
  refine ⟨(Finset.range K).sup' ⟨0, Finset.mem_range.mpr hKpos⟩ X0, ?_⟩
  intro X hX
  have hXk : ∀ k ∈ Finset.range K, X0 k ≤ X := fun k hk =>
    le_trans (Finset.le_sup' X0 hk) hX
  calc |R X| = |∑ k ∈ Finset.range K, frag k X| := by rw [h.fragmentation X]
    _ ≤ ∑ k ∈ Finset.range K, |frag k X| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range K, eps / K * X / Real.log X :=
        Finset.sum_le_sum fun k hk => hX0 k X (hXk k hk)
    _ = eps * X / Real.log X := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

/-- **`k0FragmentationInputs_not_inhabited_here`.**  `LEAN_PROVED`.

The bundle is a genuine restriction and is not formed anywhere: the K0 uniform
fragmentation reassembly is `REDUCED / CONDITIONAL`, never activated. -/
theorem k0FragmentationInputs_not_inhabited_here :
    ∃ (R : ℝ → ℝ) (frag : ℕ → ℝ → ℝ) (K : ℕ) (a b : Prop),
      ¬ K0UniformFragmentationInputs R frag K a b := by
  refine ⟨fun _ => 0, fun _ _ => 0, 1, False, True, ?_⟩
  intro h
  exact h.balanced_seven

/-- **`k0_residual_is_three_prefix`.**  `LEAN_PROVED`.

The first exact downstream residual is the `Ω(d) ≥ 3` small-prime-prefix Type-II source:
if it is unavailable, the K0 bundle can never be formed, whatever else is supplied. -/
theorem k0_residual_is_three_prefix
    (R : ℝ → ℝ) (frag : ℕ → ℝ → ℝ) (K : ℕ) (a : Prop) :
    ¬ K0UniformFragmentationInputs R frag K a False := fun h => h.three_prefix

/-- **`k0_not_activated`.**  `LEAN_PROVED`.

The downstream firewall: the compiler is available only as an implication, and its
antecedent is refuted by explicit data. -/
theorem k0_not_activated :
    (∃ (R : ℝ → ℝ) (frag : ℕ → ℝ → ℝ) (K : ℕ) (a b : Prop),
      ¬ K0UniformFragmentationInputs R frag K a b) ∧
      ∀ (R : ℝ → ℝ) (frag : ℕ → ℝ → ℝ) (K : ℕ) (a b : Prop),
        K0UniformFragmentationInputs R frag K a b → BalancedSevenAsymptoticConclusion R :=
  ⟨k0FragmentationInputs_not_inhabited_here,
    fun _ _ _ _ _ h => k0_uniform_fragmentation_compiler h⟩

end PostBalanced7Pro
end Erdos287
