import Mathlib

/-!
# Gate 1A — the rational scale ledger (finite / symbolic bank)

This file banks *only* exponent bookkeeping.  Nothing here asserts, or even mentions,
any analytic estimate: `SOURCE-AVG-JDR` and Gate 1A remain **OPEN**.

With `X` the main parameter, all scales are recorded as rational exponents of `X`:

```
M = X^(1/3),  R = X^a,  L = X^b,  H = X^(a + 2b - 2/3),  K = X^(1/3 - a).
```

The natural (diagonal) energy benchmark is `M^2 L^4 / H^2` and the candidate target
energy is `M L^4 / H`; the *missing ratio* is therefore `M / H`.  We prove this
symbolically at the level of exponents and evaluate it at the three vertices

```
V1 = (5/18, 1/3),   V2 = (5/18, 25/72),   V3 = (7/24, 1/3),
```

obtaining the gaps `1/18`, `1/36`, `1/24`.

All arithmetic is exact (`ℚ`); no floating point is used.
-/

namespace TrustedBank
namespace Gate1A

/-- A vertex of the parameter region: the pair of rational exponents `(a, b)` with
`R = X^a` and `L = X^b`. -/
structure Vertex where
  /-- The exponent `a` with `R = X^a`. -/
  a : ℚ
  /-- The exponent `b` with `L = X^b`. -/
  b : ℚ
  deriving DecidableEq

/-- `M = X^(1/3)`. -/
def expM : ℚ := 1 / 3

/-- `R = X^a`. -/
def expR (v : Vertex) : ℚ := v.a

/-- `L = X^b`. -/
def expL (v : Vertex) : ℚ := v.b

/-- `H = X^(a + 2b - 2/3)`. -/
def expH (v : Vertex) : ℚ := v.a + 2 * v.b - 2 / 3

/-- `K = X^(1/3 - a)`. -/
def expK (v : Vertex) : ℚ := 1 / 3 - v.a

/-- Exponent of the natural (diagonal) energy benchmark `M^2 L^4 / H^2`. -/
def naturalEnergyExp (v : Vertex) : ℚ := 2 * expM + 4 * expL v - 2 * expH v

/-- Exponent of the candidate target energy `M L^4 / H`. -/
def targetEnergyExp (v : Vertex) : ℚ := expM + 4 * expL v - expH v

/-- Exponent of the ratio `M / H`. -/
def missingRatioExp (v : Vertex) : ℚ := expM - expH v

/-- The vertex `V1 = (5/18, 1/3)`. -/
def V1 : Vertex := ⟨5 / 18, 1 / 3⟩

/-- The vertex `V2 = (5/18, 25/72)`. -/
def V2 : Vertex := ⟨5 / 18, 25 / 72⟩

/-- The vertex `V3 = (7/24, 1/3)`. -/
def V3 : Vertex := ⟨7 / 24, 1 / 3⟩

/-- **Ledger identity.**  (natural energy)/(target energy) = `M / H`, at the level of
exponents, at every vertex. -/
theorem naturalEnergy_sub_targetEnergy (v : Vertex) :
    naturalEnergyExp v - targetEnergyExp v = missingRatioExp v := by
  simp only [naturalEnergyExp, targetEnergyExp, missingRatioExp]
  ring

/-- The missing ratio in closed form: `M/H = X^(1 - a - 2b)`. -/
theorem missingRatioExp_eq (v : Vertex) : missingRatioExp v = 1 - v.a - 2 * v.b := by
  simp only [missingRatioExp, expM, expH]; ring

/-- Gap at `V1`: `M/H = X^(1/18)`. -/
theorem missingRatio_V1 : missingRatioExp V1 = 1 / 18 := by
  norm_num [missingRatioExp, expM, expH, V1]

/-- Gap at `V2`: `M/H = X^(1/36)`. -/
theorem missingRatio_V2 : missingRatioExp V2 = 1 / 36 := by
  norm_num [missingRatioExp, expM, expH, V2]

/-- Gap at `V3`: `M/H = X^(1/24)`. -/
theorem missingRatio_V3 : missingRatioExp V3 = 1 / 24 := by
  norm_num [missingRatioExp, expM, expH, V3]

/-- The three exponent gaps, bundled. -/
theorem missingRatio_vertices :
    missingRatioExp V1 = 1 / 18 ∧ missingRatioExp V2 = 1 / 36 ∧
      missingRatioExp V3 = 1 / 24 :=
  ⟨missingRatio_V1, missingRatio_V2, missingRatio_V3⟩

/-- At all three vertices the gap is strictly positive.  (Bookkeeping only: this does
not assert that the target energy is attainable.) -/
theorem missingRatio_pos :
    0 < missingRatioExp V1 ∧ 0 < missingRatioExp V2 ∧ 0 < missingRatioExp V3 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [missingRatio_V1]; norm_num
  · rw [missingRatio_V2]; norm_num
  · rw [missingRatio_V3]; norm_num

/-- Consistency of the ledger: `H = R · L^2 / M^2` at the level of exponents. -/
theorem expH_eq (v : Vertex) : expH v = expR v + 2 * expL v - 2 * expM := by
  simp only [expH, expR, expL, expM]; ring

/-- `K = M / R` at the level of exponents. -/
theorem expK_eq (v : Vertex) : expK v = expM - expR v := by
  simp only [expK, expM, expR]

end Gate1A
end TrustedBank
