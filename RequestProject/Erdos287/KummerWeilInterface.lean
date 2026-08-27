import Mathlib
import RequestProject.Erdos287.KummerFiniteCompiler
import RequestProject.Erdos287.KummerRootStabilizer

/-!
# Quadratic-Kummer backend, layer 3: the Weil / interval-completion input

**Status of this layer.**  A search of Mathlib and of this project finds *no* theorem
giving a nontrivial bound for an incomplete character sum
`∑_{m ∈ interval} χ(F(n₁m)F(n₂m))` (no Weil bound for curves, no Burgess/Polya–Vinogradov
completion estimate).  Rather than axiomatize it, this file declares the required input
as an **explicit interface structure** whose fields are ordinary Lean propositions, and
proves the bilinear estimate *from* that interface together with

* the finite Cauchy/correlation compiler `kummer_bilinear_of_correlation_bounds`
  (`KummerFiniteCompiler.lean`, kernel-checked), and
* the root-stabilizer algebra (`KummerRootStabilizer.lean`, kernel-checked), which is
  what makes the exceptional set `{n₁, −n₁}` — of size at most two — the correct one.

No theorem in this file asserts that the interface is inhabited: supplying an instance
is exactly the external analytic obligation.

## Main results

* `pmExceptional_card_le_two`, `pmExceptional_symm`, `pmExceptional_subset` — the
  `±`-exceptional set is a legitimate sparse symmetric relation with `s = 2`;
* `QuadraticKummerCorrelationBound` — the interface (diagonal/exceptional bound `Mb`,
  nonexceptional completion bound `R`);
* `kummer_bilinear_of_interface` — the bilinear bound
  `|∑ α_m β_n K(m,n)|² ≤ ‖α‖₂²‖β‖₂²(2·Mb + R·|In|)`.
-/

open scoped BigOperators

namespace Erdos287
namespace Kummer

variable {K : Type*} [Field K] [DecidableEq K]

/-- The `±`-exceptional set: the partners of `n` inside `In` allowed by the
root-stabilizer theorem (`scalingSquareStabilizer_subset`). -/
def pmExceptional (In : Finset K) (n : K) : Finset K :=
  In.filter (fun x => x = n ∨ x = -n)

theorem pmExceptional_subset (In : Finset K) (n : K) : pmExceptional In n ⊆ In :=
  Finset.filter_subset _ _

theorem pmExceptional_symm (In : Finset K) (n₁ : K) (h1 : n₁ ∈ In) (n₂ : K)
    (h2 : n₂ ∈ In) : n₂ ∈ pmExceptional In n₁ ↔ n₁ ∈ pmExceptional In n₂ := by
  classical
  simp only [pmExceptional, Finset.mem_filter]
  constructor
  · rintro ⟨-, rfl | rfl⟩
    · exact ⟨h1, Or.inl rfl⟩
    · exact ⟨h1, Or.inr (by ring)⟩
  · rintro ⟨-, rfl | rfl⟩
    · exact ⟨h2, Or.inl rfl⟩
    · exact ⟨h2, Or.inr (by ring)⟩

theorem pmExceptional_card_le_two (In : Finset K) (n : K) :
    ((pmExceptional In n).card : ℝ) ≤ 2 := by
  classical
  have hsub : pmExceptional In n ⊆ ({n, -n} : Finset K) := by
    intro x hx
    simp only [pmExceptional, Finset.mem_filter] at hx
    simpa using hx.2
  have hcard : (pmExceptional In n).card ≤ ({n, -n} : Finset K).card :=
    Finset.card_le_card hsub
  have h2 : ({n, -n} : Finset K).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  exact_mod_cast le_trans hcard h2

/-- **The external analytic interface.**

`Mb` is the (trivial, diagonal) bound valid on the `±`-exceptional pairs — in the
intended application `Mb = M`, the length of the `m`-interval — and `R` is the
*nonexceptional* correlation bound, which in the intended application is the
Weil/interval-completion estimate `R ≍ (M/√p + √p)·p^{o(1)}`.

Supplying a term of this structure is precisely the external obligation
`WEIL_INPUT_EXTERNAL_INTERFACE_REQUIRED`; nothing here constructs one. -/
structure QuadraticKummerCorrelationBound
    {ιM : Type*} (Im : Finset ιM) (In : Finset K) (Kern : ιM → K → ℝ) (Mb R : ℝ) :
    Prop where
  /-- The exceptional (diagonal) bound. -/
  exceptional : ∀ n₁ ∈ In, ∀ n₂ ∈ pmExceptional In n₁,
    |∑ m ∈ Im, Kern m n₁ * Kern m n₂| ≤ Mb
  /-- The Weil / interval-completion bound on nonexceptional pairs. -/
  completion : ∀ n₁ ∈ In, ∀ n₂ ∈ In, n₂ ∉ pmExceptional In n₁ →
    |∑ m ∈ Im, Kern m n₁ * Kern m n₂| ≤ R
  /-- Both bounds are nonnegative. -/
  nonneg : 0 ≤ Mb ∧ 0 ≤ R

/-- **Bilinear bound from the interface.**  Purely formal consequence of the interface
and the kernel-checked finite compiler: no arithmetic is used at this step. -/
theorem kummer_bilinear_of_interface {ιM : Type*} (Im : Finset ιM) (In : Finset K)
    (alpha : ιM → ℝ) (beta : K → ℝ) (Kern : ιM → K → ℝ) (Mb R : ℝ)
    (h : QuadraticKummerCorrelationBound Im In Kern Mb R) :
    (∑ m ∈ Im, ∑ n ∈ In, alpha m * beta n * Kern m n) ^ 2
      ≤ (∑ m ∈ Im, alpha m ^ 2) * (∑ n ∈ In, beta n ^ 2) * (2 * Mb + R * In.card) :=
  kummer_bilinear_of_correlation_bounds Im In alpha beta Kern (pmExceptional In) 2 Mb R
    (fun n => pmExceptional_subset In n)
    (fun n _ => pmExceptional_card_le_two In n)
    (fun n₁ h₁ n₂ h₂ => pmExceptional_symm In n₁ h₁ n₂ h₂)
    h.nonneg.1 h.nonneg.2 h.exceptional h.completion

/-- **Why `±` is the right exceptional set.**  If `n₂` is *not* `±n₁`, then by the
root-stabilizer theorem the product `F(n₁X)F(n₂X)` is not a square, which is exactly the
nondegeneracy hypothesis under which the completion bound is expected to hold.  This
lemma records that implication in the form used above. -/
theorem not_square_of_not_pmExceptional {a b c n₁ n₂ : K} {In : Finset K}
    (ha : a ≠ 0) (hdisc : b ^ 2 - 4 * a * c ≠ 0) (h1 : n₁ ≠ 0) (h2 : n₂ ≠ 0)
    (hmem : n₂ ∈ In) (hnot : n₂ ∉ pmExceptional In n₁) :
    ¬ ∃ G : Polynomial K, quadPoly (a * n₁ ^ 2) (b * n₁) c * quadPoly (a * n₂ ^ 2) (b * n₂) c
      = G ^ 2 := by
  rintro ⟨G, hG⟩
  apply hnot
  simp only [pmExceptional, Finset.mem_filter]
  exact ⟨hmem, quadratic_scaling_square_criterion ha hdisc h1 h2 hG⟩

end Kummer
end Erdos287
