import RequestProject.Erdos287.ResearchBankV28.RepairedAnalyticBundle

/-!
# Erdős #287 — Research Bank V29 §4: the physical clean state (audit)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## Audit finding (source-literal)

The V27 object `ResearchBankV27.CleanNonzero.CleanState x` is an ABSTRACT structure: it bundles a
`DecoratedData` (whose Kloosterman form `KloostermanData` carries only the real numbers
`Q, R, S, N, d, x, ε_DI, Ξ, mass, Rep, N_q, T, Δ₂, Δ₃`, an arbitrary finite kernel `Kl` and an
off-diagonal set) together with colour data.  **No V25–V28 declaration produces a clean state from
a physical source**: there is no definition of `q = D q₀`, `r₁, r₂`, `n₁, n₂`, `u₁, u₂`, `v₁, v₂`,
canonical roots, or rough supports as fields of any clean state.  The DI arithmetic conditions of
the task (§4) are therefore not even *expressible* on `KloostermanData`.

This file makes the missing arithmetic layer explicit (`DIArithmeticData`,
`DIArithmeticConditions`) so that the earliest hole can be stated precisely, and proves:

* `DIArithmeticConditions_satisfiable` — the conditions are consistent (a concrete witness);
* `DIArithmeticConditions_nontrivial` — they are not automatic (a concrete failure);
* `arithOnlyClass_provider_false` — (FINITE REGRESSION) the class of Kloosterman forms that merely
  *carry* arithmetic data satisfying every §4 gcd/congruence/separation condition, with matching
  `N, d, x`, still makes the DI provider FALSE.  Hence the arithmetic conditions alone cannot serve
  as `DIClass`: kernel realization (§5) is load-bearing, and DIClass must not be weakened to them.

**STOP (task §4).** The earliest remaining composition hole is the field
`DIClass s.DD.KD` of `CleanAdmissible` for every clean state `s` used in the nonzero branch: it
has no source derivation because (i) `DIClass` is an uninterpreted predicate parameter of the V28
bundle and (ii) no physical clean state exists in the bank.  See `DIClassRealization`.
-/

namespace Erdos287
namespace ResearchBankV29
namespace PhysicalCleanState

open ResearchBankV27.DISpectral

/-- The arithmetic data of one clean DI state as listed in task §4 (NOT present in V25–V28). -/
structure DIArithmeticData where
  q0 : ℕ
  D : ℕ
  d : ℕ
  r1 : ℕ
  r2 : ℕ
  n1 : ℕ
  n2 : ℕ
  N : ℝ
  x : ℝ
  C : ℝ

/-- The modulus `q = D q₀`. -/
def DIArithmeticData.q (a : DIArithmeticData) : ℕ := a.D * a.q0

/-- The literal §4 gcd / congruence / separation conditions. -/
def DIArithmeticConditions (a : DIArithmeticData) : Prop :=
  Nat.Coprime a.r1 a.r2 ∧
  Nat.Coprime (a.q * a.d) a.r2 ∧
  Nat.Coprime a.n1 a.n2 ∧
  Nat.Coprime a.n1 (a.q * a.d * a.r1) ∧
  Nat.Coprime a.n2 (a.q * a.d * a.r2) ∧
  a.n1 ≡ a.n2 [MOD a.q * a.d] ∧
  a.N / Real.log a.x ^ a.C ≤ |(a.n1 : ℝ) - a.n2| ∧
  Nat.Coprime a.D (a.q0 * a.d * a.r1 * a.r2)

/-- A concrete witness: `q₀ = 1, D = 1, d = 1, r₁ = 2, r₂ = 3, n₁ = 5, n₂ = 7, N = 0`. -/
def witness : DIArithmeticData :=
  { q0 := 1, D := 1, d := 1, r1 := 2, r2 := 3, n1 := 5, n2 := 7, N := 0, x := 2, C := 1 }

/-- **The §4 conditions are consistent** (LEAN BANK). -/
theorem DIArithmeticConditions_satisfiable : DIArithmeticConditions witness := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_, by decide⟩
  · simp [witness, DIArithmeticData.q, Nat.ModEq, Nat.mod_one]
  · simp [witness]

/-- **The §4 conditions are not automatic** (LEAN BANK): `r₁ = r₂ = 2` fails `gcd(r₁,r₂)=1`. -/
theorem DIArithmeticConditions_nontrivial :
    ¬ DIArithmeticConditions { witness with r1 := 2, r2 := 2 } := by
  rintro ⟨h, -⟩
  exact absurd h (by decide)

/-- Arithmetic data attached to the degenerate form (`N = 0`, `d = 0`, `x = 2`). -/
def degenerateArith : DIArithmeticData :=
  { q0 := 1, D := 1, d := 0, r1 := 1, r2 := 1, n1 := 1, n2 := 1, N := 0, x := 2, C := 1 }

theorem degenerateArith_conditions : DIArithmeticConditions degenerateArith := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, Nat.ModEq.refl _, ?_, by decide⟩
  simp [degenerateArith]

/-- The class of forms that merely carry §4-admissible arithmetic data with matching `N, d, x`
(no kernel realization).  Recorded ONLY to show it is too weak to be `DIClass`. -/
def ArithOnlyClass (K : KloostermanData) : Prop :=
  ∃ a : DIArithmeticData, DIArithmeticConditions a ∧ K.N = a.N ∧ K.d = a.d ∧ K.x = a.x

/-- **Arithmetic conditions alone do not give a valid DI class** (FINITE REGRESSION). -/
theorem arithOnlyClass_provider_false (η : ℝ) : ¬ DISpectralProvider η ArithOnlyClass := by
  intro h
  refine degenerateForm_not_DI η (h.spectral _ ?_ (degenerateForm_admissible η))
  exact ⟨degenerateArith, degenerateArith_conditions, by simp [degenerateForm, degenerateArith],
    by simp [degenerateForm, degenerateArith], by simp [degenerateForm, degenerateArith]⟩

end PhysicalCleanState
end ResearchBankV29
end Erdos287
