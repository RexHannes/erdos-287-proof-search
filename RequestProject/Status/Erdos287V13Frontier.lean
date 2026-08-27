import RequestProject.Erdos287.ClosureInputs
import RequestProject.Erdos287.Uniform
import RequestProject.TrustedBank.Erdos287.GoodPrime

/-!
# Erdős #287 — V13 frontier status

This file is deliberately conservative.  It banks no new analytic number-theory
estimate and does not claim a solution of Erdős #287.

The kernel-checked finite endgame already uses `WindowPairSupply`, whose definition
contains the required upper-half placement `M ≤ 2*x`.  The older exploratory
`Challenges.Delta6.LCBeta` interface omitted this placement condition, so it is not by
itself a literal input to the adjacent-hole blocker.  The repaired open interface below
records the missing condition without asserting that the supply exists.

V13 research-status delta (prose only):

* finite exact range `3 ≤ M ≤ 4·10^9`: BANKED in the existing project;
* `WindowPairSupply`: exact remaining formal supply interface;
* log-cofactor asymptotic reduction: paper-level mathematics, not formalised here;
* a fixed-certificate Ford leakage estimate is now the narrowest proposed analytic
  endgame; it is NOT a Lean theorem in this repository;
* the proposed H8/H9 source-to-Kummer splice and any seven-prime Kummer estimate are
  analytic research claims and remain outside the trusted Lean bank;
* Gate 1A is not a logically mandatory dependency for #287.  It is only a possible
  provider if a future literal packet/source census routes an actual #287 packet through
  its canonical common-weight theorem.

No uninhabited analytic interface below is imported into a proved theorem.
-/

namespace Erdos287

/-- Repaired log-cofactor supply interface.  This is an OPEN proposition: no theorem in
this project proves it for all sufficiently large `M`.

Compared with the older exploratory `LCBeta`, the condition `M ≤ 2*x` is included so
that the adjacent pair lies in the upper half; together with the already-banked
half-range lemma this is the placement needed by the adjacent-hole blocker. -/
def LCBetaUpperHalf (M J : ℕ) : Prop :=
  ∃ x q₀ q₁ : ℕ,
    q₀.Prime ∧ q₁.Prime ∧
    M ≤ 2 * J * q₀ ∧ M ≤ 2 * J * q₁ ∧
    M < q₀ ^ 2 ∧ M < q₁ ^ 2 ∧
    q₀ ∣ x ∧ q₁ ∣ (x + 1) ∧
    M ≤ 2 * x ∧ x + 1 ≤ M

-- Regression/status pins: these declarations are already kernel checked elsewhere.
#check Erdos287.WindowPairSupply
#check Erdos287.Gap2CE.no_of_windowPairSupply
#check Erdos287.no_Erdos287Counterexample_of_closure
#check Erdos287.C_le_U
#check TrustedBank.Erdos287Good.Gap2CE.logCofactor_finite_blocker

end Erdos287
