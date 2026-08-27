import Mathlib
import RequestProject.Erdos287.AffineTwoOuterSource
import RequestProject.Erdos287.FixedCertificateSingletonCompiler

/-!
# The conditional two-outer compiler and its firewalls (V14, Parts 13–16)

## Part 13 — the open analytic interface

`AffinePrimeModulusMuTwoOuterInput` is the smallest honest interface for
`AFFINE287-PRIME-MODULUS-MU-TWOOUTER45`: a bound `|S₂| ≤ E₂` for the prime-modulus
two-outer source quantity.  It is **`OPEN_ANALYTIC`**, is never inhabited here, and is not
an `axiom`: every theorem that uses it takes it as an explicit hypothesis.

## Part 14 — the comparison-side firewall

The prime-side Vaughan decomposition does *not* by itself decompose the comparison term
`B(mn)`.  `Affine287TwoOuterComparisonMatch` is a separate, never-proved interface
asserting exactly the decomposition of the singleton target sum into the three channels
`S_I + S_pp + S₂`.  Status **`SOURCE_BLOCKED`**.  No main term is defined after the fact:
the three channel quantities are free parameters supplied by whoever inhabits the
interface (hostile check 14).

## Part 15 — the conditional compiler

`singletonTypeII_of_vaughan_twoOuter` assembles

  Type-I sibling input + prime-power input + two-outer analytic input + comparison match
  + the singleton window and complement-depth certificates

into a `SingletonGeneratedTypeIIInput`, and `smoothParity_of_vaughan_twoOuter` /
`parentLeakage_of_vaughan_twoOuter` push that through the banked singleton compiler.  The
error channels are kept **separate** throughout: the resulting bound is
`E_I + C·X^{5/6} + E₂`, never a merged constant.  Classification `PROVED_COMPILER`.

## Part 16 — the Gate / F3 firewall

`Affine287ToTwoOuterF3Adapter` is an *uninhabited* adapter interface.  Nothing in this
project asserts that `AffinePrimeModulusMuTwoOuterInput` is the historical
`TWO_OUTER_VARIABLE_F3_KERNEL`, or that either maps to Gate 1A/1B: those dictionaries are
not present in this workspace, and name coincidence is not a proof (hostile check 16).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace TwoOuterCompiler

open Erdos287.Vaughan Erdos287.VaughanOuter Erdos287.TwoOuter
open Erdos287.Singleton Erdos287.SmoothParity

/-- The singleton Type-II target sum, exactly the quantity bounded by the `smallness`
field of `SingletonGeneratedTypeIIInput`. -/
noncomputable def singletonTargetSum (X : ℝ) (support : Finset (ℕ × ℕ))
    (xi kappa Lam B : ℕ → ℝ) (W : ℝ → ℝ) : ℝ :=
  ∑ p ∈ support, xi p.1 * kappa p.2 * W ((p.1 * p.2 : ℕ) / X) *
    (Lam (2 * p.1 * p.2 - 1) + Lam (2 * p.1 * p.2 + 1) - 4 * B (p.1 * p.2))

/-! ## Part 13 — the open analytic interface -/

/-- **`AffinePrimeModulusMuTwoOuterInput`** — `OPEN_ANALYTIC`.

The bound for the prime-modulus two-outer source quantity `S2`.  Never inhabited. -/
structure AffinePrimeModulusMuTwoOuterInput (X E S2 : ℝ) : Prop where
  /-- Asymptotic regime. -/
  X_gt_one : 1 < X
  /-- **The open analytic estimate.** -/
  bound : |S2| ≤ E

/-- **`VaughanTypeIGeneratedKappaInput`** — `OPEN_ANALYTIC / CONDITIONAL_INTERFACE`.

The Type-I sibling channel (`I₁ + I₂` after the generated-`κ` reduction).  Never
inhabited. -/
structure VaughanTypeIGeneratedKappaInput (X E SI : ℝ) : Prop where
  /-- Asymptotic regime. -/
  X_gt_one : 1 < X
  /-- **The open analytic estimate.** -/
  bound : |SI| ≤ E

/-! ## Part 14 — the comparison-side firewall -/

/-- **`Affine287TwoOuterComparisonMatch`** — `SOURCE_BLOCKED`.

The statement that the singleton target sum (prime side *minus* comparison side) splits
into the three Vaughan channels.  Never proved in this project. -/
def Affine287TwoOuterComparisonMatch (X : ℝ) (support : Finset (ℕ × ℕ))
    (xi kappa Lam B : ℕ → ℝ) (W : ℝ → ℝ) (SI Spp S2 : ℝ) : Prop :=
  singletonTargetSum X support xi kappa Lam B W = SI + Spp + S2

/-! ## Part 15 — the conditional compiler -/

variable {eps : ℝ}

/-- **`singletonTypeII_of_vaughan_twoOuter`** — `PROVED_COMPILER`.

The four separate channels plus the singleton window/depth certificates produce a
`SingletonGeneratedTypeIIInput` with error `E_I + C·X^{5/6} + E₂`. -/
theorem singletonTypeII_of_vaughan_twoOuter
    {cls : SingletonClass} {X EI C E2 SI Spp S2 : ℝ} {dep : ℕ}
    {support : Finset (ℕ × ℕ)} {xi kappa Lam B : ℕ → ℝ} {W : ℝ → ℝ}
    (hwin : ∀ p ∈ support,
      X ^ (sigmaOf eps / 3) < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X ^ sigmaOf eps)
    (hdep : dep ≤ 39)
    (hmatch : Affine287TwoOuterComparisonMatch X support xi kappa Lam B W SI Spp S2)
    (hI : VaughanTypeIGeneratedKappaInput X EI SI)
    (hpp : PrimePowerOuterBound X C Spp)
    (h2 : AffinePrimeModulusMuTwoOuterInput X E2 S2) :
    SingletonGeneratedTypeIIInput eps cls X (EI + C * X ^ ((5 : ℝ) / 6) + E2) dep
      support xi kappa Lam B W where
  X_gt_one := hI.X_gt_one
  window := hwin
  complement_depth_le := hdep
  smallness := by
    have h : singletonTargetSum X support xi kappa Lam B W = SI + Spp + S2 := hmatch
    have htri : |SI + Spp + S2| ≤ |SI| + |Spp| + |S2| :=
      le_trans (abs_add_le _ _) (by
        have := abs_add_le SI Spp
        linarith)
    have hsum : |SI| + |Spp| + |S2| ≤ EI + C * X ^ ((5 : ℝ) / 6) + E2 := by
      have h1 := hI.bound
      have h2' := hpp.bound
      have h3 := h2.bound
      linarith
    calc |∑ p ∈ support, xi p.1 * kappa p.2 * W ((p.1 * p.2 : ℕ) / X) *
            (Lam (2 * p.1 * p.2 - 1) + Lam (2 * p.1 * p.2 + 1) - 4 * B (p.1 * p.2))|
        = |SI + Spp + S2| := by rw [← h, singletonTargetSum]
      _ ≤ |SI| + |Spp| + |S2| := htri
      _ ≤ EI + C * X ^ ((5 : ℝ) / 6) + E2 := hsum

/-- **`smoothParity_of_vaughan_twoOuter`** — `PROVED_COMPILER /
CONDITIONAL_ON_OPEN_ANALYTIC_INPUT`.

The Vaughan two-outer route, chained through the banked singleton compiler, gives the
smooth-parity packet bound — conditional on: the source-blocked cell identity, the
source-blocked packet reduction, the source-blocked comparison match, and the three open
analytic channels, each kept separate. -/
theorem smoothParity_of_vaughan_twoOuter
    (h : AdmissibleEps eps) (c : FordSmoothFragmentCertificate (sigmaOf eps))
    {cls : SingletonClass} {X EI C E2 SI Spp S2 : ℝ} {dep : ℕ}
    {support : Finset (ℕ × ℕ)} {xi kappa Lam B : ℕ → ℝ} {W : ℝ → ℝ}
    {sector : Finset ℕ} {Hs : ℕ → ℤ} {cut : ℕ → ℕ} {f : ℕ → ℝ}
    (hcut : ∀ n ∈ sector, 1 ≤ cut n)
    (hcell : K0CellIdentitySource sector Hs cut)
    (hred : SingletonPacketReduction sector Hs f X support xi kappa Lam B W)
    (hwin : ∀ p ∈ support,
      X ^ (sigmaOf eps / 3) < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X ^ sigmaOf eps)
    (hdep : dep ≤ 39)
    (hmatch : Affine287TwoOuterComparisonMatch X support xi kappa Lam B W SI Spp S2)
    (hI : VaughanTypeIGeneratedKappaInput X EI SI)
    (hpp : PrimePowerOuterBound X C Spp)
    (h2 : AffinePrimeModulusMuTwoOuterInput X E2 S2) :
    FixedCertificateSmoothParityPacket sector Hs cut f (EI + C * X ^ ((5 : ℝ) / 6) + E2) ∧
      eps < chosenSize c ∧ chosenSize c ≤ eps + sigmaOf eps :=
  smoothParity_of_singletonTypeII h c hcut hcell hred
    (singletonTypeII_of_vaughan_twoOuter (cls := cls) (dep := dep) hwin hdep hmatch hI hpp h2)

/-- **`parentLeakage_of_vaughan_twoOuter`** — `PROVED_COMPILER /
CONDITIONAL_ON_OPEN_ANALYTIC_INPUT`.

The same route continued to the parent leakage bound over `Usmooth ∪ Urest`.  The smooth
channel bound `E_I + C·X^{5/6} + E₂` and the remaining-children bound `Er` stay separate. -/
theorem parentLeakage_of_vaughan_twoOuter
    (h : AdmissibleEps eps) (c : FordSmoothFragmentCertificate (sigmaOf eps))
    {cls : SingletonClass} {X EI C E2 Er SI Spp S2 : ℝ} {dep : ℕ}
    {support : Finset (ℕ × ℕ)} {xi kappa Lam B : ℕ → ℝ} {W : ℝ → ℝ}
    {Usmooth Urest : Finset ℕ} {Hs : ℕ → ℤ} {cut : ℕ → ℕ} {f : ℕ → ℝ}
    (hdisj : Disjoint Usmooth Urest)
    (hcut : ∀ n ∈ Usmooth, 1 ≤ cut n)
    (hcell : K0CellIdentitySource Usmooth Hs cut)
    (hred : SingletonPacketReduction Usmooth Hs f X support xi kappa Lam B W)
    (hwin : ∀ p ∈ support,
      X ^ (sigmaOf eps / 3) < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X ^ sigmaOf eps)
    (hdep : dep ≤ 39)
    (hmatch : Affine287TwoOuterComparisonMatch X support xi kappa Lam B W SI Spp S2)
    (hI : VaughanTypeIGeneratedKappaInput X EI SI)
    (hpp : PrimePowerOuterBound X C Spp)
    (h2 : AffinePrimeModulusMuTwoOuterInput X E2 S2)
    (hr : |∑ n ∈ Urest, f n * (Hs n : ℝ)| ≤ Er) :
    |∑ n ∈ (Usmooth ∪ Urest), f n * (Hs n : ℝ)| ≤ (EI + C * X ^ ((5 : ℝ) / 6) + E2) + Er :=
  parentLeakage_of_singletonTypeII h c hdisj hcut hcell hred
    (singletonTypeII_of_vaughan_twoOuter (cls := cls) (dep := dep) hwin hdep hmatch hI hpp h2) hr

/-! ## Part 16 — the Gate / F3 adapter firewall -/

/-- **`Affine287ToTwoOuterF3Adapter`** — `CONDITIONAL_INTERFACE`, deliberately
**uninhabited**.

An inhabitant would be an exact dictionary identifying the prime-modulus two-outer source
quantity `S2` with the historical `TWO_OUTER_VARIABLE_F3_KERNEL` quantity `F3`.  The
literal F3 source is not present in this workspace, so no inhabitant is constructed, and
no theorem below assumes one. -/
structure Affine287ToTwoOuterF3Adapter (S2 F3 : ℝ) : Prop where
  /-- The exact dictionary between the two source quantities. -/
  exact_dictionary : S2 = F3

/-- *If* an exact dictionary were supplied, a bound would transfer.  This is the only use
made of the adapter, and it is purely conditional: it inhabits nothing. -/
theorem twoOuter_bound_transfer_of_adapter {X E S2 F3 : ℝ}
    (ha : Affine287ToTwoOuterF3Adapter S2 F3)
    (h2 : AffinePrimeModulusMuTwoOuterInput X E S2) : |F3| ≤ E := by
  rw [← ha.exact_dictionary]
  exact h2.bound

end TwoOuterCompiler
end Erdos287
