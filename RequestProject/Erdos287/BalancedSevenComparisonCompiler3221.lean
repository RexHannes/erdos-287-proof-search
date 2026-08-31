import Mathlib
import RequestProject.Erdos287.PrincipalQCell3221
import RequestProject.Erdos287.AggregateEulerLocal3221
import RequestProject.Erdos287.QPacketPartition3221
import RequestProject.Erdos287.SmallConductorExceptional3221
import RequestProject.Erdos287.SP2ClosureCompiler3221

/-!
# V23, §11–§13 — sign bookkeeping, the conditional comparison compiler, and the
Balanced7 asymptotic closure compiler

`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45` (conditional)

## What is proved here

Only **implications**.  Every analytic or source antecedent is one of the uninhabited
interfaces of §4–§9, and none of them is inhabited anywhere in this repository.  Per the
independent audit (`OPUS NANC : CASE F — SOURCE-MISSING`) the literal SP-2 one-sign source,
the uniform `H_P(w)` estimate, dyadic/full-`q` exhaustiveness, the independent physical
`2B(P)`, the small-conductor and exceptional physical sources, and no-double-spending are
all *unverified*; they appear here exactly as hypotheses.

* §11 `oneSign_match` / `twoSign_total` — finite sign bookkeeping: one sign gives `2B(P)`,
  two signs give `4B(P)`, and the second sign is a genuinely separate supply.
* §12 `BalancedSevenComparisonInputs` and `balancedSevenComparison_of_inputs` — the
  conditional comparison compiler, concluding the repository's own comparison object
  `MuLogComparisonAtCutoff` at the shared cutoff.
* §13 `balancedSevenAsymptotic_of_closure_and_comparison` — SP-2 analytic closure plus
  comparison closure gives the Balanced7 packet input.  Effective closure is *not*
  produced; see the effectivity firewall in `SmallConductorExceptional3221`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction
open scoped BigOperators

namespace Erdos287
namespace V23CompilerLayer

open Erdos287.Vaughan Erdos287.V23Comparison Erdos287.V23Principal Erdos287.V23Euler
open Erdos287.V23QPacket Erdos287.V23LowCond Erdos287.SP2Source Erdos287.SP2PrimeBox
open Erdos287.V21PrimeBox

/-! ## §11  Both signs -/

/-- One-sign matching at the interface level: the one-sign physical channel equals `2B(P)`. -/
def OneSignMatch (val B : ℝ) : Prop := val = 2 * B

/-- **`twoSign_total`.**  `LEAN_PROVED`.

Supplying *both* sign packages gives `4B(P)`; one package alone does not. -/
theorem twoSign_total {vplus vminus B : ℝ}
    (hp : OneSignMatch vplus B) (hm : OneSignMatch vminus B) :
    vplus + vminus = 4 * B := by
  rw [OneSignMatch] at hp hm
  rw [hp, hm]; ring

/-- **`oneSign_is_not_twoSign`.**  `LEAN_PROVED`.

The second sign is a genuinely separate supply: a single sign package gives `2B`, not
`4B`, unless `B = 0`. -/
theorem oneSign_is_not_twoSign {v B : ℝ} (h : OneSignMatch v B) (hB : B ≠ 0) :
    v ≠ 4 * B := by
  rw [OneSignMatch] at h
  rw [h]
  intro hcon
  exact hB (by linarith)

/-! ## §12  The comparison compiler -/

/-- The parameter bundle of the comparison compiler (data only, no claims). -/
structure ComparisonParams where
  /-- The physical one-sign cell. -/
  C : SP2PhysicalCell
  /-- The sign. -/
  s : AffineSign
  /-- The SP-2 fixed-certificate metadata. -/
  Ccert : SP2FixedCertificateData
  /-- The prime-box data. -/
  Pdat : PrimeBoxData
  /-- The independently defined physical singular series. -/
  Bsrc : ℕ → ℝ
  /-- The aggregate `μ/φ log` sum. -/
  J : ℕ → ℝ → ℝ
  /-- The small-conductor remainder, cell by cell. -/
  rem1 : (Fin 7 → ℕ) → ℝ
  /-- The exceptional-character remainder, cell by cell. -/
  rem2 : (Fin 7 → ℕ) → ℝ
  /-- The aggregate cutoff parameter `z`. -/
  z : ℝ
  /-- The scale. -/
  X : ℝ
  /-- The shared low-conductor cutoff `D`. -/
  D : ℝ
  /-- The aggregate log saving. -/
  Aexp : ℝ
  /-- The small-conductor pointwise budget. -/
  e2 : ℝ
  /-- The exceptional pointwise budget. -/
  e3 : ℝ
  /-- The source moduli. -/
  sourceModuli : Finset ℕ
  /-- The packet index set. -/
  indexSet : Finset ℕ
  /-- The declared packet owner. -/
  owner : ℕ → ℕ
  /-- The currently treated analytic cell. -/
  Qcell : ℕ
  /-- The value of a `q`-cell. -/
  cellValue : ℕ → ℝ
  /-- The reassembly target. -/
  target : ℝ
  /-- The aggregate Euler product. -/
  F : ℕ → ℂ → ℂ
  /-- The aggregate Euler numerator. -/
  H : ℕ → ℂ → ℂ
  /-- The reciprocal zeta factor. -/
  zetaInv : ℂ → ℂ
  /-- The twin-prime constant parameter. -/
  S2 : ℝ
  /-- The physical seven-prime family. -/
  family : Finset ℕ
  /-- The contour region. -/
  contour : Set ℂ
  /-- The uniform bound on `H_P`. -/
  Hbound : ℝ
  /-- The fixed sufficient log saving. -/
  A0 : ℝ
  /-- The small-conductor constant. -/
  Cbound : ℝ
  /-- The number of prime boxes. -/
  boxCount : ℕ
  /-- The small-conductor moduli. -/
  moduli : Finset ℕ
  /-- The small primitive conductors. -/
  conductors : Finset ℕ
  /-- The inducing map. -/
  inducedBy : ℕ → ℕ
  /-- The cell contribution. -/
  cellContribution : ℕ → ℝ
  /-- The Mellin weight. -/
  weightFn : ℕ → ℝ
  /-- The log insertion. -/
  logInsertion : ℕ → ℝ
  /-- The small-conductor total. -/
  totalLow : ℝ
  /-- The optional exceptional conductor. -/
  excConductor : Option ℕ
  /-- The exceptional moduli. -/
  excModuli : Finset ℕ
  /-- The exceptional inducing map. -/
  excInducedBy : ℕ → ℕ
  /-- The exceptional total. -/
  totalExc : ℝ
  /-- The ineffectivity flag of the exceptional input. -/
  ineffective : Bool
  /-- The exceptional log saving. -/
  excAexp : ℝ
  /-- The exceptional constant. -/
  excCbound : ℝ

/-- The pointwise discrepancy budget assembled from the three channels. -/
noncomputable def totalBudget (prm : ComparisonParams) : ℝ :=
  (Real.log prm.z) ^ (-prm.Aexp) + prm.e2 + prm.e3

/-- **`BalancedSevenComparisonInputs`** — `CONDITIONAL / UNINHABITED ANTECEDENTS`.

The full antecedent list mandated by the audit: the direct SP-2 source, the source-level
decomposition of the physical `Λ`-channel, the physical noncircularity input, the `q`
partition and its exhaustiveness, the aggregate Euler uniformity, the small-conductor and
exceptional inputs with their pointwise budgets, the shared `D = log X` cutoff, the
non-unit/degeneracy router and the no-double-spending condition. -/
structure BalancedSevenComparisonInputs (prm : ComparisonParams) : Prop where
  /-- The direct SP-2 source identification. -/
  source : BalancedSevenOmegaSP2DirectSourceAdapter3221 prm.Ccert prm.Pdat
  /-- The source-level decomposition of the physical `Λ`-channel into the aggregate cell,
  the small-conductor remainder and the exceptional remainder. -/
  decomposition : ∀ pv ∈ prm.C.cell,
    vonMangoldt (affineNat prm.s 1 (physModulus pv))
      = prm.J (physModulus pv) prm.z + prm.rem1 pv + prm.rem2 pv
  /-- The independently defined physical `2B(P)`. -/
  noncircular : SP2PhysicalTwoBIndependent287Input prm.C prm.Bsrc prm.J prm.Aexp
  /-- The `q` partition of the physical source. -/
  qPartition : BalancedSevenQPartitionInput prm.sourceModuli prm.owner prm.indexSet prm.Qcell
  /-- Exhaustiveness of the `q` packets. -/
  qExhaustive : BalancedSevenQPacketExhaustiveness287Input prm.sourceModuli prm.indexSet
    prm.owner prm.Qcell prm.cellValue prm.target
  /-- The uniform aggregate Euler estimate. -/
  euler : AggregateEulerUniformity287Input prm.F prm.H prm.zetaInv prm.J prm.S2 prm.family
    prm.contour prm.Hbound prm.A0
  /-- The small-conductor analytic input. -/
  lowCond : SmallConductorNegligible287Input prm.X prm.D prm.A0 prm.Cbound prm.boxCount
    prm.moduli prm.conductors prm.inducedBy prm.cellContribution prm.weightFn
    prm.logInsertion prm.totalLow
  /-- Its pointwise form on the physical cell. -/
  lowCond_pointwise : ∀ pv ∈ prm.C.cell, |prm.rem1 pv| ≤ prm.e2
  /-- The exceptional-character input, kept separate and carrying its flag. -/
  exceptional : ExceptionalCharacterNegligible287Input prm.X prm.D prm.excAexp prm.excCbound
    prm.excConductor prm.excModuli prm.excInducedBy prm.totalExc prm.ineffective
  /-- Its pointwise form on the physical cell. -/
  exceptional_pointwise : ∀ pv ∈ prm.C.cell, |prm.rem2 pv| ≤ prm.e3
  /-- The shared cutoff. -/
  same_cutoff : prm.D = Real.log prm.X
  /-- The aggregate cutoff is in range. -/
  z_large : 2 ≤ prm.z
  /-- The non-unit / degeneracy router: even moduli carry no affine cell. -/
  nonunit_router : ∀ q : ℕ, 2 ∣ q → ∀ P : ℤ, ¬ ((q : ℤ) ∣ 2 * P + prm.s.val)
  /-- No double spending: each source modulus is owned once. -/
  no_double_spending : ∀ q ∈ prm.sourceModuli, ∀ k, q ∈ qPacket k → k = prm.owner q

/-- **`comparison_pointwise_of_inputs`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

From the decomposition, the aggregate limit and the two remainder budgets, the physical
pointwise discrepancy is at most `totalBudget`. -/
theorem comparison_pointwise_of_inputs {prm : ComparisonParams}
    (h : BalancedSevenComparisonInputs prm) :
    ∀ pv ∈ prm.C.cell,
      |vonMangoldt (affineNat prm.s 1 (physModulus pv)) - 2 * prm.C.B (physModulus pv)|
        ≤ totalBudget prm := by
  intro pv hpv
  have hB : prm.C.B (physModulus pv) = prm.Bsrc (physModulus pv) :=
    h.noncircular.physical_B_is_source pv hpv
  have hJ : |prm.J (physModulus pv) prm.z - 2 * prm.Bsrc (physModulus pv)|
      ≤ (Real.log prm.z) ^ (-prm.Aexp) :=
    h.noncircular.aggregate_limit pv hpv prm.z h.z_large
  have hdec := h.decomposition pv hpv
  have hsplit : vonMangoldt (affineNat prm.s 1 (physModulus pv))
        - 2 * prm.C.B (physModulus pv)
      = (prm.J (physModulus pv) prm.z - 2 * prm.Bsrc (physModulus pv))
        + prm.rem1 pv + prm.rem2 pv := by
    rw [hdec, hB]; ring
  rw [hsplit, totalBudget]
  calc |prm.J (physModulus pv) prm.z - 2 * prm.Bsrc (physModulus pv)
          + prm.rem1 pv + prm.rem2 pv|
      ≤ |prm.J (physModulus pv) prm.z - 2 * prm.Bsrc (physModulus pv)| + |prm.rem1 pv|
          + |prm.rem2 pv| := abs_add_three _ _ _
    _ ≤ (Real.log prm.z) ^ (-prm.Aexp) + prm.e2 + prm.e3 :=
        add_le_add (add_le_add hJ (h.lowCond_pointwise pv hpv))
          (h.exceptional_pointwise pv hpv)

/-- **`comparison_bound_of_inputs`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

The one-sign physical comparison is bounded by `20 · budget · ∑|Ω|`. -/
theorem comparison_bound_of_inputs {prm : ComparisonParams}
    (h : BalancedSevenComparisonInputs prm) :
    |SP2BalancedSevenPhysicalComparison prm.C prm.s|
      ≤ 20 * totalBudget prm * ∑ pv ∈ prm.C.cell, |prm.C.Om pv| :=
  sp2PhysicalComparison_bound prm.C prm.s (totalBudget prm)
    (comparison_pointwise_of_inputs h)

/-- **`balancedSevenComparison_of_inputs`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45`: the comparison inputs supply the repository's
own comparison object at the shared cutoff, with

```
    hard  = −20 ∑ Ω Λ(2P+s),      model = −40 ∑ Ω B(P),
    err   = 20 · budget · ∑|Ω|.
```

**No inhabitant of `BalancedSevenComparisonInputs` is constructed** — six of its fields are
uninhabited external/source interfaces. -/
theorem balancedSevenComparison_of_inputs {prm : ComparisonParams} {B0 Dcut : ℝ}
    (h : BalancedSevenComparisonInputs prm) (hB0 : 0 < B0)
    (hDcut : Dcut = Erdos287.V20Compiler.highConductorCutoff B0 prm.X) :
    Erdos287.V20Compiler.MuLogComparisonAtCutoff prm.X Dcut B0
      ((-20 : ℝ) * ∑ pv ∈ prm.C.cell, prm.C.Om pv *
        vonMangoldt (affineNat prm.s 1 (physModulus pv)))
      ((-40 : ℝ) * ∑ pv ∈ prm.C.cell, prm.C.Om pv * prm.C.B (physModulus pv))
      (20 * totalBudget prm * ∑ pv ∈ prm.C.cell, |prm.C.Om pv|) := by
  refine ⟨hB0, hDcut, ⟨?_, ?_⟩⟩
  · have h3 : (3 : ℝ) ≤ prm.X := h.lowCond.scale_large
    linarith
  · have hkey := comparison_bound_of_inputs h
    have hEq : (-20 : ℝ) * (∑ pv ∈ prm.C.cell, prm.C.Om pv *
          vonMangoldt (affineNat prm.s 1 (physModulus pv)))
        - (-40 : ℝ) * ∑ pv ∈ prm.C.cell, prm.C.Om pv * prm.C.B (physModulus pv)
        = SP2BalancedSevenPhysicalComparison prm.C prm.s := by
      rw [sp2PhysicalComparison_split]
      ring
    rw [hEq]
    exact hkey

/-! ## §13  The Balanced7 asymptotic closure compiler -/

/-- **`balancedSevenAsymptotic_of_closure_and_comparison`.**
`CONDITIONAL_COMPILER / LEAN_PROVED`.

```
    SP-2 analytic closure (log-variance interface + Cauchy prefactor + budget)
      + comparison closure at the same cutoff
          ⇒ AFFINE287-BALANCED7-MODULUS-AVERAGE45  (the Balanced7 packet input)
```

This is the *asymptotic* branch only.  Nothing here produces an explicit threshold, and by
`asymptoticBalancedSeven_not_effectiveAutomatically` an ineffective exceptional input can
never produce one. -/
theorem balancedSevenAsymptotic_of_closure_and_comparison
    {Dat : Erdos287.HighCond3221.InverseSampledHighCond3221Data}
    {X Q srcVal Sphys prefactor naturalScale Lsave E err Dcut B0 : ℝ}
    (hX : 1 < X) (hQ : Q = X ^ (3 / 5 : ℝ))
    (hcert : Erdos287.V19Compiler.CauchyPrefactor3221Certificate Dat srcVal prefactor)
    (hlog : Erdos287.HighCond3221.InverseSampledHighCondLogVar3221Input Dat naturalScale Lsave)
    (hE : 0 ≤ E) (hbudget : prefactor * (naturalScale / Lsave) ≤ E ^ 2)
    (hcomp : Erdos287.V20Compiler.MuLogComparisonAtCutoff X Dcut B0 Sphys srcVal err) :
    Erdos287.V16Status.BalancedSevenPacketInput X Sphys (E + err) :=
  Erdos287.V19Compiler.balancedSeven_of_highCondLogVar hX hQ hcert hlog hE hbudget
    (Erdos287.V20Compiler.comparisonAtCutoff_to_base hcomp)

/-! ## §14  Anti-circularity -/

/-- **`comparisonInputs_not_automatic`.**  `LEAN_PROVED`.

The comparison input package is a genuine restriction: its exceptional field alone can
fail, so no inhabitant follows from generalities. -/
theorem comparisonInputs_not_automatic :
    ∃ (X D Aexp Cbound : ℝ) (excConductor : Option ℕ) (moduli : Finset ℕ)
      (inducedBy : ℕ → ℕ) (total : ℝ) (ineffective : Bool),
      ¬ ExceptionalCharacterNegligible287Input X D Aexp Cbound excConductor moduli
        inducedBy total ineffective :=
  exceptionalCharacterNegligible_is_a_restriction

/-- **`comparisonCompiler_does_not_prove_balancedSeven`.**  `LEAN_PROVED`.

The compilers above are implications.  The `q`-packet exhaustiveness antecedent is
refutable by explicit data, so nothing here constructs a Balanced7 inhabitant. -/
theorem comparisonCompiler_does_not_prove_balancedSeven :
    ∃ (sourceModuli indexSet : Finset ℕ) (owner : ℕ → ℕ) (Qcell : ℕ)
      (cellValue : ℕ → ℝ) (target : ℝ),
      ¬ BalancedSevenQPacketExhaustiveness287Input sourceModuli indexSet owner Qcell
        cellValue target :=
  qPacketExhaustiveness_not_automatic

end V23CompilerLayer
end Erdos287
