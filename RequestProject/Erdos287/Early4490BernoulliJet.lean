import Mathlib

/-!
# Erdős #287 effectivity — exact Bernoulli polynomials and the three-term rational jet (§44)

```
B2 / B3 EXACT RATIONAL ALGEBRA        : KERNEL-PROVED
SAWTOOTH ENDPOINT CONVENTION          : KERNEL-PROVED (strict, ψ(integer) = −1/2)
DERIVATIVE LADDER B3' = 3B2, B2' = 2ψ : KERNEL-PROVED (polynomial derivatives)
THREE-TERM JET Φ₃                     : KERNEL-PROVED DEFINITION
I_X = Φ₃ + E₃ + Δ                     : CONDITIONAL ANALYTIC INTERFACE (hypothesis object)
ERDŐS #287                            : OPEN
```

Exact rational polynomials

    B₂(r) = r² − r + 1/6,        B₃(r) = r³ − (3/2)r² + (1/2)r,        ψ(r) = r − 1/2,

with the strict endpoint convention of the repository (`ψ(0) = −1/2`, never `0`).  The
reflection laws `B₂(1−r) = B₂(r)`, `B₃(1−r) = −B₃(r)`, `ψ(1−r) = −ψ(r)` and the derivative
ladder `B₃' = 3B₂`, `B₂' = 2ψ` are kernel-proved; the polynomial forms live in
`Polynomial ℚ` so the derivatives are genuine kernel statements.

The three-term rational jet is, with `y = z²/X`, `t = zq/X` and `r = frac(z/q)`,

    Φ₃(z,q;X) = ψ(r)·W(y) − (t/2)·B₂(r)·W'(y) + (t²/6)·B₃(r)·W''(y),

a `KERNEL-READY` definition taking the weight jet `(W, W', W'')` as data.

The analytic Euler-summation identity `I_X = Φ₃ + E₃ + Δ` is **not** reconstructed here.  It
is carried by the explicit hypothesis object `BernoulliJetIdentity` (option B of the
specification), and only downstream algebra is kernel-proved; no custom axiom is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace Effectivity

/-! ## §44.1  The exact rational Bernoulli polynomials as functions -/

/-- `B₂(r) = r² − r + 1/6`. -/
def bern2 {K : Type*} [Field K] (r : K) : K := r ^ 2 - r + 1 / 6

/-- `B₃(r) = r³ − (3/2) r² + (1/2) r`. -/
def bern3 {K : Type*} [Field K] (r : K) : K := r ^ 3 - (3 / 2) * r ^ 2 + (1 / 2) * r

/-- The **strict** sawtooth `ψ(r) = r − 1/2` (repository endpoint convention:
`ψ(integer) = −1/2`). -/
def psiSaw {K : Type*} [Field K] (r : K) : K := r - 1 / 2

/-- **`psiSaw_endpoint`.**  `KERNEL-PROVED`.  The strict endpoint convention. -/
theorem psiSaw_endpoint : psiSaw (0 : ℚ) = -1 / 2 ∧ psiSaw (1 : ℚ) = 1 / 2 := by
  constructor <;> · unfold psiSaw; norm_num

/-- **`bern2_values`.**  `KERNEL-PROVED`.  `B₂(0) = B₂(1) = 1/6`, `B₂(1/2) = −1/12`. -/
theorem bern2_values :
    bern2 (0 : ℚ) = 1 / 6 ∧ bern2 (1 : ℚ) = 1 / 6 ∧ bern2 (1 / 2 : ℚ) = -1 / 12 := by
  refine ⟨?_, ?_, ?_⟩ <;> · unfold bern2; norm_num

/-- **`bern3_values`.**  `KERNEL-PROVED`.  `B₃(0) = B₃(1/2) = B₃(1) = 0`. -/
theorem bern3_values :
    bern3 (0 : ℚ) = 0 ∧ bern3 (1 / 2 : ℚ) = 0 ∧ bern3 (1 : ℚ) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> · unfold bern3; norm_num

/-- **`bern2_reflect`.**  `KERNEL-PROVED`.  `B₂(1−r) = B₂(r)`. -/
theorem bern2_reflect {K : Type*} [Field K] (r : K) : bern2 (1 - r) = bern2 r := by
  unfold bern2; ring

/-- **`bern3_reflect`.**  `KERNEL-PROVED`.  `B₃(1−r) = −B₃(r)`. -/
theorem bern3_reflect {K : Type*} [Field K] [CharZero K] (r : K) : bern3 (1 - r) = -bern3 r := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  unfold bern3
  field_simp
  ring

/-- **`psiSaw_reflect`.**  `KERNEL-PROVED`.  `ψ(1−r) = −ψ(r)`. -/
theorem psiSaw_reflect {K : Type*} [Field K] [CharZero K] (r : K) :
    psiSaw (1 - r) = -psiSaw r := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  unfold psiSaw
  field_simp
  ring

/-! ## §44.2  The polynomial forms and the derivative ladder -/

/-- `B₂` as an exact rational polynomial. -/
noncomputable def bern2Poly : Polynomial ℚ :=
  Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (1 / 6)

/-- `B₃` as an exact rational polynomial. -/
noncomputable def bern3Poly : Polynomial ℚ :=
  Polynomial.X ^ 3 - Polynomial.C (3 / 2) * Polynomial.X ^ 2 + Polynomial.C (1 / 2) * Polynomial.X

/-- The strict sawtooth as an exact rational polynomial. -/
noncomputable def psiPoly : Polynomial ℚ := Polynomial.X - Polynomial.C (1 / 2)

/-- **`bern2Poly_eval`.**  `KERNEL-PROVED`.  The polynomial and functional forms agree. -/
theorem bern2Poly_eval (r : ℚ) : bern2Poly.eval r = bern2 r := by
  simp [bern2Poly, bern2]

/-- **`bern3Poly_eval`.**  `KERNEL-PROVED`. -/
theorem bern3Poly_eval (r : ℚ) : bern3Poly.eval r = bern3 r := by
  simp [bern3Poly, bern3]

/-- **`psiPoly_eval`.**  `KERNEL-PROVED`. -/
theorem psiPoly_eval (r : ℚ) : psiPoly.eval r = psiSaw r := by
  simp [psiPoly, psiSaw]

/-- **`bernoulli_derivative_ladder`.**  `KERNEL-PROVED`.  `B₃' = 3 B₂` and `B₂' = 2 ψ`: the
three jet terms form the Bernoulli ladder used by the Euler-summation identity. -/
theorem bernoulli_derivative_ladder :
    Polynomial.derivative bern3Poly = Polynomial.C 3 * bern2Poly ∧
      Polynomial.derivative bern2Poly = Polynomial.C 2 * psiPoly := by
  constructor
  · apply Polynomial.funext
    intro r
    simp [bern3Poly, bern2Poly, Polynomial.derivative_sub, Polynomial.derivative_add,
      Polynomial.eval_mul]
    ring
  · apply Polynomial.funext
    intro r
    simp [bern2Poly, psiPoly]
    ring

/-! ## §44.3  The three-term rational jet -/

/-- `y = z²/X`. -/
noncomputable def jetY (z X : ℝ) : ℝ := z ^ 2 / X

/-- `t = z q / X`. -/
noncomputable def jetT (z q X : ℝ) : ℝ := z * q / X

/-- `r = frac(z/q)`. -/
noncomputable def jetR (z q : ℝ) : ℝ := Int.fract (z / q)

/-- **`jetR_mem`.**  `KERNEL-PROVED`.  `r ∈ [0,1)`. -/
theorem jetR_mem (z q : ℝ) : 0 ≤ jetR z q ∧ jetR z q < 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- The weight jet `(W, W', W'')` entering the three-term expansion. -/
structure WeightJet where
  /-- The weight `W`. -/
  W : ℝ → ℝ
  /-- Its first derivative `W'`. -/
  W1 : ℝ → ℝ
  /-- Its second derivative `W''`. -/
  W2 : ℝ → ℝ

/-- **The exact three-term rational jet.**  `KERNEL-READY DEFINITION`.

    Φ₃(z,q;X) = ψ(r) W(y) − (t/2) B₂(r) W'(y) + (t²/6) B₃(r) W''(y). -/
noncomputable def Phi3 (J : WeightJet) (z q X : ℝ) : ℝ :=
  psiSaw (jetR z q) * J.W (jetY z X)
    - (jetT z q X / 2) * bern2 (jetR z q) * J.W1 (jetY z X)
    + (jetT z q X ^ 2 / 6) * bern3 (jetR z q) * J.W2 (jetY z X)

/-- **`Phi3_eq`.**  `KERNEL-PROVED`.  The definitional unfolding, kept as a named theorem so
downstream files never re-inline the jet. -/
theorem Phi3_eq (J : WeightJet) (z q X : ℝ) :
    Phi3 J z q X = psiSaw (jetR z q) * J.W (jetY z X)
      - (jetT z q X / 2) * bern2 (jetR z q) * J.W1 (jetY z X)
      + (jetT z q X ^ 2 / 6) * bern3 (jetR z q) * J.W2 (jetY z X) := rfl

/-- The one-term (sawtooth endpoint only) jet. -/
noncomputable def PhiPsi (J : WeightJet) (z q X : ℝ) : ℝ :=
  psiSaw (jetR z q) * J.W (jetY z X)

/-- **`Phi3_sub_PhiPsi`.**  `KERNEL-PROVED`.  The exact difference between the three-term and
the one-term charts is the pair of higher Bernoulli terms — the two charts are alternatives,
never additive. -/
theorem Phi3_sub_PhiPsi (J : WeightJet) (z q X : ℝ) :
    Phi3 J z q X - PhiPsi J z q X
      = -(jetT z q X / 2) * bern2 (jetR z q) * J.W1 (jetY z X)
        + (jetT z q X ^ 2 / 6) * bern3 (jetR z q) * J.W2 (jetY z X) := by
  unfold Phi3 PhiPsi; ring

/-- **`Phi3_zero_jet`.**  `KERNEL-PROVED`.  A vanishing weight jet gives a vanishing jet
value: no hidden constant is smuggled into `Φ₃`. -/
theorem Phi3_zero_jet (z q X : ℝ) : Phi3 ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩ z q X = 0 := by
  simp [Phi3]

/-- **`Phi3_additive_in_jet`.**  `KERNEL-PROVED`.  `Φ₃` is additive in the weight jet. -/
theorem Phi3_additive_in_jet (J J' : WeightJet) (z q X : ℝ) :
    Phi3 ⟨fun y => J.W y + J'.W y, fun y => J.W1 y + J'.W1 y, fun y => J.W2 y + J'.W2 y⟩ z q X
      = Phi3 J z q X + Phi3 J' z q X := by
  unfold Phi3; simp; ring

/-! ## §44.4  The Euler/Bernoulli identity interface (option B) -/

/-- The exact analytic identity `I_X = Φ₃ + E₃ + Δ` supplied by the research report, carried as
an explicit **hypothesis object** rather than an axiom.  Its status is
`CONDITIONAL_ANALYTIC_INTERFACE`: nothing in this repository proves it. -/
structure BernoulliJetIdentity (J : WeightJet) where
  /-- The exact endpoint datum `I_X(z,q)`. -/
  IX : ℝ → ℝ → ℝ → ℝ
  /-- The third-order Euler remainder `E₃`. -/
  E3 : ℝ → ℝ → ℝ → ℝ
  /-- The exact nonlinear endpoint correction `Δ`. -/
  Delta : ℝ → ℝ → ℝ → ℝ
  /-- The supplied identity. -/
  identity : ∀ z q X, IX z q X = Phi3 J z q X + E3 z q X + Delta z q X

/-- **`bernoulliJet_downstream_algebra`.**  `KERNEL-PROVED`.  All that the interface yields
downstream: the exact replacement error, and its triangle bound.  No analytic estimate of
`E₃` or `Δ` is asserted. -/
theorem bernoulliJet_downstream_algebra {J : WeightJet} (H : BernoulliJetIdentity J)
    (z q X : ℝ) :
    H.IX z q X - Phi3 J z q X = H.E3 z q X + H.Delta z q X ∧
      |H.IX z q X - Phi3 J z q X| ≤ |H.E3 z q X| + |H.Delta z q X| := by
  have h : H.IX z q X - Phi3 J z q X = H.E3 z q X + H.Delta z q X := by
    rw [H.identity z q X]; ring
  exact ⟨h, by rw [h]; exact abs_add_le _ _⟩

/-- **`bernoulliJetIdentity_not_proved`.**  `KERNEL-PROVED`.  The interface is genuinely a
hypothesis: it is inhabited by data with no analytic content (take `I_X := Φ₃`, `E₃ = Δ = 0`),
so possessing a `BernoulliJetIdentity` proves nothing about the physical endpoint datum. -/
theorem bernoulliJetIdentity_not_proved (J : WeightJet) :
    ∃ H : BernoulliJetIdentity J, H.E3 = (fun _ _ _ => 0) ∧ H.Delta = (fun _ _ _ => 0) :=
  ⟨⟨fun z q X => Phi3 J z q X, fun _ _ _ => 0, fun _ _ _ => 0, by intro z q X; ring⟩, rfl, rfl⟩

end Effectivity
end Erdos287
