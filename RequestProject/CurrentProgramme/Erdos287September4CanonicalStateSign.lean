import Mathlib

/-!
# Erdős #287 — September-4 signed-floor bank, §2: canonical-state sign invariance

```
CANONICAL STATE SIGN INVARIANCE   (TOT-BSRC-CANONICAL-STATE-SIGN-INVARIANCE45) : KERNEL-PROVED
ONE-PRIME THRESHOLD-CROSSING INVARIANCE                                        : KERNEL-PROVED
PRIME DISTRIBUTION / NUMERICAL FLOOR / ANALYTIC ASYMPTOTIC                     : NOT ASSERTED
```

This module is **append-only** and is *pure source algebra*.  It asserts no
prime-distribution estimate, no numerical floor bound and no analytic asymptotic; it does not
inhabit any analytic socket and does not bear on Erdős #287.

## What is formalised

For a squarefree modulus `d` split as `d = d_low · d_high` with coprime factors, with

    ω(d_high) = j,          μ(d_low) = (-1)^(ω d − j),

and with the active physical `g`-state `g_j = (-1)^j`, the canonical source sign is

    κ_ε(d; n) = μ(d_low) · g_j = (-1)^(ω d) = μ(d).

All hypotheses that the proof consumes are explicit binders of the theorem
(`canonicalStateSignInvariance45`): squarefreeness of `d`, the coprime low/high split, the
active state (`gState j`, supplied as the *definition* of the active `g`-value), and the
value `j = ω(d_high)`.  The conclusion is **not** a structure field anywhere in this file.

## Threshold crossing

When one squarefree prime moves across the high/low threshold, `μ(d_low)` and `g_j` each
flip sign and the product `κ_ε` is unchanged (`thresholdCrossing_sign_invariance`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction
open scoped ArithmeticFunction.omega

namespace Erdos287
namespace September4CanonicalStateSign

/-! ## §2.1  The active physical `g`-state and the canonical sign -/

/-- The active physical `g`-state at high-depth `j`: `g_j = (-1)^j`. -/
def gState (j : ℕ) : ℤ := (-1) ^ j

/-- The canonical source sign attached to a low part `d_low` and a high depth `j`:

    κ_ε = μ(d_low) · g_j. -/
def kappaEpsSign (dlow : ℕ) (j : ℕ) : ℤ := (moebius dlow : ℤ) * gState j

/-- On a squarefree modulus the Möbius function is the parity sign of `ω`. -/
theorem moebius_eq_neg_one_pow_omega {n : ℕ} (hn : Squarefree n) :
    (moebius n : ℤ) = (-1) ^ (ω n) := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hn]
  congr 1
  exact ((ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hn.ne_zero).2 hn).symm

/-! ## §2.2  The canonical-state sign invariance -/

/-- **`canonicalStateSignInvariance45`** (row `TOT-BSRC-CANONICAL-STATE-SIGN-INVARIANCE45`).
`KERNEL-PROVED`.

For squarefree `d = d_low · d_high` with coprime factors and `ω(d_high) = j`, the canonical
source sign in the active `g`-state satisfies

    κ_ε(d) = μ(d_low) · g_j = (-1)^(ω d) = μ(d).

Every hypothesis actually used is an explicit binder: `hd` (squarefree `d`), `hsplit`
(the low/high factorisation), `hcop` (coprimality of the two parts), `hj` (the high depth),
and the active state is the definition `gState j = (-1)^j`.  The intermediate equality
`μ(d_low) = (-1)^(ω d − j)` is *derived*, and recorded as the third conjunct. -/
theorem canonicalStateSignInvariance45 {d dlow dhigh j : ℕ} (hd : Squarefree d)
    (hsplit : d = dlow * dhigh) (hcop : Nat.Coprime dlow dhigh) (hj : ω dhigh = j) :
    kappaEpsSign dlow j = (-1 : ℤ) ^ (ω d) ∧
      kappaEpsSign dlow j = (moebius d : ℤ) ∧
      (moebius dlow : ℤ) = (-1) ^ (ω d - j) := by
  have hdlow : Squarefree dlow := by
    refine hd.squarefree_of_dvd ?_
    exact ⟨dhigh, hsplit⟩
  have homega : ω d = ω dlow + j := by
    rw [hsplit, ArithmeticFunction.cardDistinctFactors_mul hcop, hj]
  have hmu : (moebius dlow : ℤ) = (-1) ^ (ω dlow) := moebius_eq_neg_one_pow_omega hdlow
  have hkappa : kappaEpsSign dlow j = (-1 : ℤ) ^ (ω d) := by
    unfold kappaEpsSign gState
    rw [hmu, homega, pow_add]
  refine ⟨hkappa, ?_, ?_⟩
  · rw [hkappa, moebius_eq_neg_one_pow_omega hd]
  · rw [hmu, homega]
    congr 1
    omega

/-- The same statement in the literal "product of the two sign factors" form. -/
theorem canonicalStateSign_product {d dlow dhigh j : ℕ} (hd : Squarefree d)
    (hsplit : d = dlow * dhigh) (hcop : Nat.Coprime dlow dhigh) (hj : ω dhigh = j) :
    (moebius dlow : ℤ) * gState j = (moebius d : ℤ) :=
  (canonicalStateSignInvariance45 hd hsplit hcop hj).2.1

/-! ## §2.3  One-prime threshold crossing -/

/-- **`thresholdCrossing_sign_flip`.**  `KERNEL-PROVED`.  Moving one squarefree prime `p`
from the high part into the low part flips *both* sign factors:

    μ(d_low · p) = − μ(d_low),      g_j = − g_{j+1}. -/
theorem thresholdCrossing_sign_flip {dlow p : ℕ} (hp : p.Prime) (hnd : ¬ p ∣ dlow) (j : ℕ) :
    (moebius (dlow * p) : ℤ) = - (moebius dlow : ℤ) ∧ gState j = - gState (j + 1) := by
  have hcop : Nat.Coprime dlow p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm
  constructor
  · rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp]
    ring
  · simp only [gState, pow_succ]
    ring

/-- **`thresholdCrossing_sign_invariance`.**  `KERNEL-PROVED`.  The canonical sign `κ_ε` is
*unchanged* when one squarefree prime crosses the high/low threshold: the two flips of
`thresholdCrossing_sign_flip` cancel. -/
theorem thresholdCrossing_sign_invariance {dlow p : ℕ} (hp : p.Prime) (hnd : ¬ p ∣ dlow)
    (j : ℕ) : kappaEpsSign (dlow * p) j = kappaEpsSign dlow (j + 1) := by
  obtain ⟨h1, h2⟩ := thresholdCrossing_sign_flip hp hnd j
  simp only [kappaEpsSign, h1, h2]
  ring

end September4CanonicalStateSign
end Erdos287
