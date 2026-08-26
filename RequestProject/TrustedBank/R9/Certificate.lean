import Mathlib

/-!
# R9 — the finite nine-prime certificate combinatorics

Banked here is **only** the finite binomial fact and its immediate algebraic
consequence for a certificate value:

```
∑_{j=5}^{9} (-1)^j · C(9,j) = -70,
```

so that, *for any* certificate functional whose supplied formula has the shape
`H_g(n) = -(∑_{j=5}^{9} (-1)^j C(9,j)) · g(∅)`, one gets `H_g(n) = 70 · g(∅)`, hence
`H_g(n) = 70` when `g(∅) = 1` — independently of the adjustable lower-dimensional
`g`-values, which do not appear in the formula.

**Range guard / honesty.**  The exact Ford-certificate definitions (the `γ`-window and
the full `H_g` formula) are *not* present in this repository, so the value theorem is
stated with the formula as an explicit hypothesis; it is not asserted that the actual
Ford certificate has this shape.  Nothing here says that R9 has positive analytic mass:
that is an analytic question and remains **OPEN**.
-/

open scoped BigOperators

namespace TrustedBank
namespace R9

/-- The alternating divisor-count sum over the nine-prime window in which exactly the
divisors with `5,6,7,8,9` prime factors exceed `n^γ`. -/
def altSum : ℤ := ∑ j ∈ Finset.Icc 5 9, (-1 : ℤ) ^ j * (Nat.choose 9 j : ℤ)

/-- **The finite R9 binomial identity**: `∑_{j=5}^{9} (-1)^j C(9,j) = -70`. -/
theorem altSum_eq : altSum = -70 := by decide

/-- Expanded form of the identity, term by term. -/
theorem altSum_terms :
    (-(Nat.choose 9 5 : ℤ)) + (Nat.choose 9 6 : ℤ) - (Nat.choose 9 7 : ℤ)
      + (Nat.choose 9 8 : ℤ) - (Nat.choose 9 9 : ℤ) = -70 := by decide

/-- **Certificate value.**  For any certificate functional whose supplied formula is
`H = -altSum · g∅`, the value is `70 · g∅`, with no dependence on lower-dimensional
`g`-values. -/
theorem Hg_value_of_formula (H gEmpty : ℤ) (hformula : H = -altSum * gEmpty) :
    H = 70 * gEmpty := by
  rw [hformula, altSum_eq]; ring

/-- Under the normalisation `g(∅) = 1` the certificate value is exactly `70`. -/
theorem Hg_value_one (H gEmpty : ℤ) (hformula : H = -altSum * gEmpty) (hg : gEmpty = 1) :
    H = 70 := by
  rw [Hg_value_of_formula H gEmpty hformula, hg]; ring

/-- **Independence of the adjustable data.**  Two certificate values computed from the
same supplied formula with the same `g(∅)` agree, whatever other (lower-dimensional)
`g`-values are chosen: the formula does not see them. -/
theorem Hg_independent (H H' gEmpty : ℤ)
    (h : H = -altSum * gEmpty) (h' : H' = -altSum * gEmpty) : H = H' := by
  rw [h, h']

/-! ## The complementary low-index half (appended: `≤ 4` prime factors)

The following is **pure finite combinatorics**.  It is the number that a Ford-type
certificate would take if — and only if — exactly the divisors with at most four of the
nine prime factors fell below the cutoff.  Whether that split is the correct one for the
actual Ford `G(m;n)` is a *source* question about equation (7.17); the defining formulas
are not present in this repository, so **`H(n) = 70` is not banked here**: only the
identity below, and the conditional value theorems above, are. -/

/-- The alternating divisor count over subsets of at most four of the nine primes. -/
def lowSum : ℤ := ∑ j ∈ Finset.Icc 0 4, (-1 : ℤ) ^ j * (Nat.choose 9 j : ℤ)

/-- **The low-index R9 binomial identity**: `∑_{j=0}^{4} (-1)^j C(9,j) = 70`. -/
theorem lowSum_eq : lowSum = 70 := by decide

/-- The two halves cancel: the full alternating sum over all nine indices vanishes. -/
theorem lowSum_add_altSum : lowSum + altSum = 0 := by decide

end R9
end TrustedBank
