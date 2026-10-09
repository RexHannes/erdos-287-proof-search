import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V15 §B2: the derivative kernel

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The functional kernel `F` and its integrated cutoff `G` are **different objects**.  The intended
relation is

    (−1)^K ∂_1 ⋯ ∂_K G = F.

At the abstraction level available here the coordinate partial derivative is Mathlib's one-variable
`deriv` along a coordinate line (`partialDeriv`), iterated over the coordinates
(`mixedPartial`).  Whether the actual `G` satisfies the relation for the actual `F` is an
external functional-analysis fact: it enters only through the provider structure
`DerivativeKernelProvider`, which is never constructed.

Regression fixtures (`K = 1`): `G(x) = −x₀`, `F ≡ 1` satisfy the relation (`fixture_relation`)
while `G ≠ F` (`fixture_G_ne_F`), and the silent identification `G := F` fails the relation
(`identify_G_with_F_fails`).
-/

namespace Erdos287
namespace ResearchBankV15
namespace DerivativeKernel

/-- A kernel on `ℝ^K`. -/
abbrev Kernel (K : ℕ) := (Fin K → ℝ) → ℝ

/-- Coordinate partial derivative `∂_i f (x)`. -/
noncomputable def partialDeriv {K : ℕ} (i : Fin K) (f : Kernel K) : Kernel K :=
  fun x => deriv (fun s => f (Function.update x i s)) (x i)

/-- Iterated mixed partial `∂_{i_1} ⋯ ∂_{i_m} f`. -/
noncomputable def mixedPartial {K : ℕ} (l : List (Fin K)) (f : Kernel K) : Kernel K :=
  l.foldr partialDeriv f

/-- The kernel pair: functional kernel `F` and integrated cutoff `G` (distinct fields). -/
structure KernelPair (K : ℕ) where
  F : Kernel K
  G : Kernel K

/-- The intended relation `(−1)^K ∂_1 ⋯ ∂_K G = F`. -/
def DerivativeRelation {K : ℕ} (P : KernelPair K) : Prop :=
  ∀ x, (-1 : ℝ) ^ K * mixedPartial (List.finRange K) P.G x = P.F x

/-- **External functional-analysis provider** (never constructed): the actual cutoff `G`
integrates the actual kernel `F`. -/
structure DerivativeKernelProvider {K : ℕ} (P : KernelPair K) : Prop where
  relation : DerivativeRelation P

/-- Fixture kernel pair on `ℝ^1`: `F ≡ 1`, `G(x) = −x₀`. -/
noncomputable def fixture : KernelPair 1 where
  F := fun _ => 1
  G := fun x => -x 0

theorem fixture_relation : DerivativeRelation fixture := by
  intro x
  simp only [mixedPartial, List.finRange_succ, List.finRange_zero, List.map_nil,
    List.foldr_cons, List.foldr_nil, partialDeriv, fixture]
  have : (fun s : ℝ => -(Function.update x 0 s) 0) = fun s => -s := by
    funext s; simp
  simp only [Fin.isValue, this, deriv_neg', pow_one]
  norm_num

theorem fixture_G_ne_F : fixture.G ≠ fixture.F := by
  intro h
  have := congrFun h (fun _ => 0)
  simp [fixture] at this

/-- **Silently identifying `G` with `F` breaks the relation.** -/
theorem identify_G_with_F_fails :
    ¬ DerivativeRelation ({ F := fixture.F, G := fixture.F } : KernelPair 1) := by
  intro h
  have := h (fun _ => 0)
  simp only [mixedPartial, List.finRange_succ, List.finRange_zero, List.map_nil,
    List.foldr_cons, List.foldr_nil, partialDeriv, fixture] at this
  simp at this

end DerivativeKernel
end ResearchBankV15
end Erdos287
