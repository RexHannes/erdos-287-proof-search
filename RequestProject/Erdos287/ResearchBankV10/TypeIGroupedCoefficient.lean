import Mathlib

/-!
# Erdős #287 — Research Bank V10 §F: the Type-I grouped-coefficient dependency contract

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A semantic / type-level firewall.

* `CoeffIndex`, `SpectralIndex`, `OuterIndex` — three **distinct** index types (coefficient-side
  variables, later spectral variables, outer variables on which root/base factors may depend);
* `GroupedCoeff` — the trusted grouped Type-I coefficient: a function of `CoeffIndex` **only**,
  with the unit bound.  Its constructor `GroupedCoeff.ofCoeffSide` accepts only coefficient-side
  data; by its type it cannot receive a `SpectralIndex`;
* `GroupedCoeff.lift_spectral_invariant` — a grouped coefficient, viewed as a function of
  `(CoeffIndex, SpectralIndex)`, never depends on the spectral argument;
* `root_removed_in_abs` — a unimodular root/base factor depending only on the **outer** variable
  is removed inside the absolute value *before* the grouped coefficient is formed;
* `root_depending_on_inner_not_removable` — the same removal fails if the root factor depends on
  the inner (summed) variable (explicit numerical countermodel);
* `not_factorsThrough_of_depends` and `spectralDependent_fails_interface` — **negative fixture**:
  a coefficient that genuinely depends on a `SpectralIndex` does **not** inhabit the trusted
  `GroupedCoeff` interface.
-/

namespace Erdos287
namespace ResearchBankV10
namespace TypeIGroupedCoefficient

/-- Coefficient-side variables of the grouped Type-I coefficient. -/
structure CoeffIndex where
  /-- First coefficient-side variable. -/
  m : ℕ
  /-- Second coefficient-side variable. -/
  n : ℕ
  deriving DecidableEq

/-- Later spectral variables (e.g. the level `c` and the frequency `r`). -/
structure SpectralIndex where
  /-- The spectral level. -/
  c : ℕ
  /-- The spectral frequency. -/
  r : ℕ
  deriving DecidableEq

/-- Outer variables, on which root/base factors are allowed to depend. -/
structure OuterIndex where
  /-- The outer variable. -/
  x : ℕ
  deriving DecidableEq

/-- **The trusted grouped Type-I coefficient**: a function of the coefficient-side index only,
bounded by `1`.  There is no field through which a `SpectralIndex` could enter. -/
structure GroupedCoeff where
  /-- The coefficient. -/
  coeff : CoeffIndex → ℂ
  /-- Unit bound. -/
  bound : ∀ i, ‖coeff i‖ ≤ 1

/-- The only constructor: coefficient-side data only. -/
def GroupedCoeff.ofCoeffSide (w : CoeffIndex → ℂ) (hw : ∀ i, ‖w i‖ ≤ 1) : GroupedCoeff :=
  ⟨w, hw⟩

/-- A grouped coefficient viewed on `(CoeffIndex, SpectralIndex)`. -/
def GroupedCoeff.lift (g : GroupedCoeff) : CoeffIndex → SpectralIndex → ℂ :=
  fun i _ => g.coeff i

/-- **Spectral invariance by construction.** -/
theorem GroupedCoeff.lift_spectral_invariant (g : GroupedCoeff) (i : CoeffIndex)
    (s s' : SpectralIndex) : g.lift i s = g.lift i s' := rfl

/-- A two-variable coefficient *inhabits the trusted interface* iff it is the lift of a
`GroupedCoeff`. -/
def FactorsThroughCoeff (f : CoeffIndex → SpectralIndex → ℂ) : Prop :=
  ∃ g : GroupedCoeff, ∀ i s, f i s = g.coeff i

/-- Genuine dependence on a spectral variable. -/
def DependsOnSpectral (f : CoeffIndex → SpectralIndex → ℂ) : Prop :=
  ∃ i s s', f i s ≠ f i s'

/-- **Negative fixture (general)**: a coefficient depending on a spectral variable does not
inhabit the grouped-coefficient interface. -/
theorem not_factorsThrough_of_depends {f : CoeffIndex → SpectralIndex → ℂ}
    (h : DependsOnSpectral f) : ¬ FactorsThroughCoeff f := by
  rintro ⟨g, hg⟩
  obtain ⟨i, s, s', hne⟩ := h
  exact hne ((hg i s).trans (hg i s').symm)

/-- The explicit spectral-dependent coefficient `f(i, s) = 1_{s.c = 0}`. -/
def spectralDependent : CoeffIndex → SpectralIndex → ℂ :=
  fun _ s => if s.c = 0 then 1 else 0

/-- **Negative fixture (explicit)**: `spectralDependent` fails the trusted interface. -/
theorem spectralDependent_fails_interface : ¬ FactorsThroughCoeff spectralDependent := by
  apply not_factorsThrough_of_depends
  refine ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ?_⟩
  simp [spectralDependent]

/-- Positive control: a coefficient-side function does inhabit the interface. -/
theorem coeffSide_inhabits (w : CoeffIndex → ℂ) (hw : ∀ i, ‖w i‖ ≤ 1) :
    FactorsThroughCoeff (fun i _ => w i) :=
  ⟨GroupedCoeff.ofCoeffSide w hw, fun _ _ => rfl⟩

/-- **Root/base factors are removed inside the absolute value**: a unimodular factor `ρ(o)`
depending only on the outer variable `o` drops out of `|∑_i ρ(o) a(i) K(i, s)|`, so the grouped
coefficient can be formed from `a` alone. -/
theorem root_removed_in_abs {ι : Type*} (I : Finset ι) (ρ : OuterIndex → ℂ) (o : OuterIndex)
    (hρ : ‖ρ o‖ = 1) (a : ι → ℂ) (K : ι → SpectralIndex → ℂ) (s : SpectralIndex) :
    ‖∑ i ∈ I, ρ o * (a i * K i s)‖ = ‖∑ i ∈ I, a i * K i s‖ := by
  rw [← Finset.mul_sum, norm_mul, hρ, one_mul]

/-- **Firewall**: if the root factor depends on the inner summation variable, it can **not** be
removed inside the absolute value (explicit countermodel with two inner terms). -/
theorem root_depending_on_inner_not_removable :
    ∃ (ρ : Fin 2 → ℂ) (a : Fin 2 → ℂ), (∀ i, ‖ρ i‖ = 1) ∧
      ‖∑ i, ρ i * a i‖ ≠ ‖∑ i, a i‖ := by
  refine ⟨![1, -1], ![1, 1], ?_, ?_⟩
  · intro i; fin_cases i <;> simp
  · simp [Fin.sum_univ_two]; norm_num

end TypeIGroupedCoefficient
end ResearchBankV10
end Erdos287
