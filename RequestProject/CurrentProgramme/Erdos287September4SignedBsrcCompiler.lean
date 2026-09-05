import RequestProject.CurrentProgramme.Erdos287September4PhysicalW
import RequestProject.CurrentProgramme.Erdos287September4T0T2DeepEvenCancellation

/-!
# Erdős #287 — September-4 signed-floor bank, §6–§7: the exact signed `B_src` source

```
FINITE (TRUNCATED) SIGNED SOURCE IDENTITY  R_signed = −4 Σ_d (E_d[V0] − E_d[V2]) : KERNEL-PROVED
THE FACTOR −4  (two affine signs × T⁰−T² comparison sign)                        : KERNEL-PROVED
ANALYTIC LIMIT (integral / convergence)                                          : ISOLATED, NOT ASSERTED
SECONDARY POLE  Res_{s=0} F_d(s) = −1/4                                          : EXTERNAL / NOT FORMALIZED
SECONDARY POLE ⇒ SHOULDER FORMULA (algebraic implication)                        : KERNEL-PROVED
NUMERICAL BOUND OF ANY KIND                                                      : NOT ASSERTED
```

This module is **append-only**.  It formalises the *exact signed source before absolute
values*: no triangle inequality is taken, and no numerical bound is claimed.

## The finite / analytic separation

`E_d[V] = Σ_m B_src(d·m) V(m) − (d/φ(d)) · I` uses a **supplied** real number `I` in place
of `∫V`, and the sum runs over a **supplied finite** range `M`.  The finite identity below
is therefore kernel-proved with no integrability or convergence input.  What `I` is supposed
to be is not hidden: `IntegralSupplyObligation` states exactly the analytic identity
`I = ∫ V`, and it is **not** proved here.

## The factor −4

`R_signed` is *defined* as a double sum over the two physical affine sign families
(`affineSigns = {+1, −1}`, one for each affine copy) of the `T⁰ − T²` comparison, whose sign
is `compareSign = −1`.  The prefactor `−4` is then **derived**
(`affineSigns.card * affineSigns.card * compareSign = −4`), not postulated.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace September4SignedCompiler

open September4T0T2 (ind)

/-! ## §6.1  The exact centred functional `E_d` -/

/-- The exact (finite, truncated) centred functional

    E_d[V] = Σ_{m ∈ M} B_src(d·m) · V(m) − (d/φ(d)) · I,

with `I` the supplied value of `∫V`. -/
noncomputable def Ed (Bsrc : ℕ → ℝ) (d : ℕ) (M : Finset ℕ) (V : ℕ → ℝ) (I : ℝ) : ℝ :=
  (∑ m ∈ M, Bsrc (d * m) * V m) - ((d : ℝ) / (Nat.totient d : ℝ)) * I

/-- The analytic obligation that the supplied number `I` really is the integral of the
supplied continuous test function `Vc`.  This is **isolated, not asserted**: no theorem of
this file proves or uses it. -/
def IntegralSupplyObligation (Vc : ℝ → ℝ) (I : ℝ) : Prop :=
  MeasureTheory.IntegrableOn Vc (Set.Ioi (0 : ℝ)) ∧ ∫ x in Set.Ioi (0 : ℝ), Vc x = I

/-! ## §6.2  The two physical test functions -/

/-- The family-`0` test function at `d`: the supplied physical weight at `n = d·m`, cut by
the `γ`-indicator `1_{d ≤ Y(dm)}`. -/
def V0 (Wt : ℕ → ℝ) (Y : ℕ → ℕ) (d m : ℕ) : ℝ := Wt (d * m) * ind (d ≤ Y (d * m))

/-- The family-`2` test function at `d`: the supplied physical weight at `n = 2·d·m`, cut by
the doubled indicator `1_{2d ≤ Y(2dm)}`. -/
def V2 (Wt : ℕ → ℝ) (Y : ℕ → ℕ) (d m : ℕ) : ℝ := Wt (2 * d * m) * ind (2 * d ≤ Y (2 * d * m))

/-- The physical instantiation of the supplied weight: `Wt n = W(n/X)` for the exact bump of
§1 and a supplied scale `X`. -/
noncomputable def physicalWeight (X : ℝ) (n : ℕ) : ℝ := September4PhysicalW.W ((n : ℝ) / X)

/-! ## §6.3  The two affine signs and the comparison sign -/

/-- The two physical affine signs `ε ∈ {+1, −1}` of one affine copy. -/
def affineSigns : Finset ℤ := {1, -1}

@[simp] theorem affineSigns_card : affineSigns.card = 2 := by decide

/-- The sign of the `T⁰ − T²` comparison. -/
def compareSign : ℤ := -1

/-- **`factor_minus_four`.**  `KERNEL-PROVED`.  The compiler prefactor is *derived* from the
two physical affine sign families and the comparison sign:

    (#affineSigns) · (#affineSigns) · compareSign = −4. -/
theorem factor_minus_four :
    (affineSigns.card : ℤ) * (affineSigns.card : ℤ) * compareSign = -4 := by decide

/-! ## §6.4  The exact signed source -/

/-- The per-modulus signed contribution `E_d[V0,d] − E_d[V2,d]`. -/
noncomputable def signedContribution (Bsrc Wt : ℕ → ℝ) (Y : ℕ → ℕ) (M : Finset ℕ) (I0 I2 : ℕ → ℝ)
    (d : ℕ) : ℝ :=
  Ed Bsrc d M (V0 Wt Y d) (I0 d) - Ed Bsrc d M (V2 Wt Y d) (I2 d)

/-- **The exact signed source, before absolute values.**  It is *defined* as the double sum
over the two affine sign families of the sign-`compareSign` comparison of the two centred
functionals — the prefactor is not put in by hand. -/
noncomputable def R_signed (Bsrc Wt : ℕ → ℝ) (Y : ℕ → ℕ) (D M : Finset ℕ) (I0 I2 : ℕ → ℝ) : ℝ :=
  ∑ _e1 ∈ affineSigns, ∑ _e2 ∈ affineSigns,
    (compareSign : ℝ) * ∑ d ∈ D.filter (fun d => Odd d), signedContribution Bsrc Wt Y M I0 I2 d

/-- **`signedBsrcSourceIdentity45`.**  `KERNEL-PROVED`.  The exact symbolic identity

    R_{B,signed} = −4 · Σ_{d odd} ( E_d[V0,d] − E_d[V2,d] ),

with the factor `−4` derived from the two physical affine signs and the `T⁰ − T²`
comparison sign (`factor_minus_four`).  No absolute value, no estimate, no analytic input. -/
theorem signedBsrcSourceIdentity45 (Bsrc Wt : ℕ → ℝ) (Y : ℕ → ℕ) (D M : Finset ℕ)
    (I0 I2 : ℕ → ℝ) :
    R_signed Bsrc Wt Y D M I0 I2
      = -4 * ∑ d ∈ D.filter (fun d => Odd d), signedContribution Bsrc Wt Y M I0 I2 d := by
  classical
  simp only [R_signed, Finset.sum_const, affineSigns_card, compareSign]
  push_cast
  ring

/-- The same identity written out with `E_d` unfolded, in the literal source shape. -/
theorem signedBsrcSourceIdentity45_expanded (Bsrc Wt : ℕ → ℝ) (Y : ℕ → ℕ) (D M : Finset ℕ)
    (I0 I2 : ℕ → ℝ) :
    R_signed Bsrc Wt Y D M I0 I2
      = -4 * ∑ d ∈ D.filter (fun d => Odd d),
          (((∑ m ∈ M, Bsrc (d * m) * V0 Wt Y d m)
              - ((d : ℝ) / (Nat.totient d : ℝ)) * I0 d)
            - ((∑ m ∈ M, Bsrc (d * m) * V2 Wt Y d m)
              - ((d : ℝ) / (Nat.totient d : ℝ)) * I2 d)) := by
  rw [signedBsrcSourceIdentity45]
  rfl

/-! ## §7  The secondary-pole interface (EXTERNAL) -/

/-- **External input socket** for the universal secondary residue.  Its fields are
mathematical only: a supplied family `F_d` of complex functions, a rational residue value,
and the *limit* characterisation of that residue.  The socket does **not** contain the
desired floor conclusion, and this development builds **no** inhabitant: the analytic proof
of `Res_{s=0} F_d(s) = −1/4` is EXTERNAL / NOT FORMALIZED. -/
structure SecondaryPoleInput where
  /-- The supplied family of complex functions. -/
  F : ℕ → ℂ → ℂ
  /-- The supplied rational residue value. -/
  residue : ℚ
  /-- The residue is characterised as a limit of `s · F_d(s)` at `s = 0`. -/
  isResidue : ∀ d : ℕ, Filter.Tendsto (fun s : ℂ => s * F d s)
    (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds ((residue : ℝ) : ℂ))

/-- The downstream **algebraic** shoulder contribution of a pole of residue `ρ` carrying
weight mass `mass`, through the compiler prefactor `−4` of §6. -/
def poleShoulder (residue mass : ℚ) : ℚ := (-4 : ℚ) * residue * mass

/-- **`shoulder_of_residue_quarter`.**  `KERNEL-PROVED`.  The downstream implication asked
for: *if* the secondary residue equals `−1/4`, *then* the shoulder contribution is exactly
the weight mass.  The analytic hypothesis is an explicit binder; it is not proved here. -/
theorem shoulder_of_residue_quarter (residue mass : ℚ) (h : residue = -1 / 4) :
    poleShoulder residue mass = mass := by
  rw [poleShoulder, h]; ring

/-- The same implication phrased against the external socket. -/
theorem shoulder_of_secondaryPoleInput (P : SecondaryPoleInput) (mass : ℚ)
    (h : P.residue = -1 / 4) : poleShoulder P.residue mass = mass :=
  shoulder_of_residue_quarter P.residue mass h

end September4SignedCompiler
end Erdos287
