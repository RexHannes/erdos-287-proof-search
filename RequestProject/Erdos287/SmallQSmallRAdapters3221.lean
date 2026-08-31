import Mathlib
import RequestProject.Erdos287.FullQStructuralPartition3221
import RequestProject.Erdos287.AffineVaughanIdentity

/-!
# V24, §9–§10 — the SmallQ and SmallR Type-I adapters

`AFFINE287-SP2-SMALLQ-TYPEI-ADAPTER45`   (OPEN — first exact residual)
`AFFINE287-SP2-SMALLR-SWITCHED-TYPEI45`  (OPEN)

The two "easy looking" sectors of the full-`q` partition are *not* supplied here.  What is
banked is:

* the **literal** sector sums `sigmaSmallQ`, `sigmaSmallR`, `sigmaHard` and their exact
  reassembly `sigma_threeWay_reassembly`;
* two **uninhabited** adapter interfaces recording precisely which literal data a Type-I
  provider would have to match, and conditional consumers of those interfaces;
* the firewall `smallQ_and_smallR_cells_differ`: the `q ↔ r` switch is *not* a symmetry of
  the problem, so a SmallQ adapter does not supply the SmallR sector.

No generic "Type-I theorem" is invoked: closure requires a literal generated-coefficient
adapter, which is what the interfaces demand.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction
open scoped BigOperators

namespace Erdos287
namespace V24Adapters

open Erdos287.V24FullQ

/-! ## §9.1  The literal sector sums -/

/-- The literal SmallQ sector sum `Σ^{(7)}_{smallQ,s}`:
`∑_{q·r = N, q ≤ u} μ(q) · log r · coeff(q,r)`. -/
noncomputable def sigmaSmallQ (u N : ℕ) (coeff : ℕ × ℕ → ℝ) : ℝ :=
  ∑ x ∈ sectorCell u N QSector.smallQ, (moebius x.1 : ℝ) * Real.log x.2 * coeff x

/-- The literal SmallR sector sum: `q > u`, `r ≤ u`. -/
noncomputable def sigmaSmallR (u N : ℕ) (coeff : ℕ × ℕ → ℝ) : ℝ :=
  ∑ x ∈ sectorCell u N QSector.smallR, (moebius x.1 : ℝ) * Real.log x.2 * coeff x

/-- The literal Hard sector sum: `q > u`, `r > u`. -/
noncomputable def sigmaHard (u N : ℕ) (coeff : ℕ × ℕ → ℝ) : ℝ :=
  ∑ x ∈ sectorCell u N QSector.hard, (moebius x.1 : ℝ) * Real.log x.2 * coeff x

/-- **`sigma_threeWay_reassembly`.**  `LEAN_PROVED`.

The whole `μ · log` factorisation sum is exactly the sum of the three literal sector sums. -/
theorem sigma_threeWay_reassembly (u N : ℕ) (coeff : ℕ × ℕ → ℝ) :
    ∑ x ∈ Nat.divisorsAntidiagonal N, (moebius x.1 : ℝ) * Real.log x.2 * coeff x =
      sigmaSmallQ u N coeff + sigmaSmallR u N coeff + sigmaHard u N coeff :=
  sum_threeWay_sector u N _

/-- The physical saving demanded of a sector: `N / log²(N+2)`. -/
noncomputable def sectorTargetNorm (N : ℕ) : ℝ := (N : ℝ) / (Real.log ((N : ℝ) + 2)) ^ 2

theorem sectorTargetNorm_nonneg (N : ℕ) : 0 ≤ sectorTargetNorm N := by
  apply div_nonneg (Nat.cast_nonneg N)
  positivity

/-! ## §9.2  The SmallQ Type-I adapter interface -/

/-- **`Affine287SP2SmallQTypeIAdapterInput`** — `EXTERNAL / UNINHABITED`.

The literal data a Type-I provider must supply for the SmallQ sector: the seven-prime
generated coefficient law with its `q`- and `r`-ranges, the Möbius carrier, the log carrier,
the smooth/Mellin weight normalisation, the affine sign, the intended provider and the
theorem-hypothesis dictionary translating the provider's norm into the physical saving. -/
structure Affine287SP2SmallQTypeIAdapterInput
    (u N : ℕ) (coeff : ℕ × ℕ → ℝ) (qRange rRange : Finset ℕ)
    (sgn : ℤ) (s : Erdos287.Vaughan.AffineSign) (targetNorm : ℝ)
    (provider : Provider) : Prop where
  /-- The generated seven-prime coefficient law is supported in the declared ranges. -/
  coefficient_law : ∀ x ∈ sectorCell u N QSector.smallQ,
    coeff x ≠ 0 → x.1 ∈ qRange ∧ x.2 ∈ rRange
  /-- The Möbius carrier is the small variable. -/
  mobius_carrier : ∀ q ∈ qRange, q ≤ u
  /-- The log carrier is the large variable. -/
  log_carrier : ∀ r ∈ rRange, u < r
  /-- Smooth / Mellin weight normalisation. -/
  smooth_weight : ∀ x ∈ sectorCell u N QSector.smallQ, |coeff x| ≤ 1
  /-- The affine sign supplied is the one recorded. -/
  sign_fixed : sgn = s.val
  /-- The provider actually intended. -/
  typeI_provider : provider = Provider.Gate0TypeI
  /-- The provider's own conclusion. -/
  target : |sigmaSmallQ u N coeff| ≤ targetNorm
  /-- Theorem-hypothesis dictionary: the provider's norm is at least as strong as the
  physical saving the Balanced7 comparison needs. -/
  dictionary : targetNorm ≤ sectorTargetNorm N

/-- **`smallQ_closed_of_literal_typeI_adapter`** — `CONDITIONAL`.

If a literal Type-I adapter is supplied, the SmallQ sector meets the physical saving. -/
theorem smallQ_closed_of_literal_typeI_adapter
    {u N : ℕ} {coeff : ℕ × ℕ → ℝ} {qRange rRange : Finset ℕ} {sgn : ℤ}
    {s : Erdos287.Vaughan.AffineSign} {targetNorm : ℝ} {provider : Provider}
    (h : Affine287SP2SmallQTypeIAdapterInput u N coeff qRange rRange sgn s targetNorm provider) :
    |sigmaSmallQ u N coeff| ≤ sectorTargetNorm N ∧ provider = Provider.Gate0TypeI :=
  ⟨le_trans h.target h.dictionary, h.typeI_provider⟩

/-- **`smallQAdapter_not_automatic`** — the interface is a genuine restriction. -/
theorem smallQAdapter_not_automatic :
    ∃ (u N : ℕ) (coeff : ℕ × ℕ → ℝ) (qRange rRange : Finset ℕ) (sgn : ℤ)
      (s : Erdos287.Vaughan.AffineSign) (targetNorm : ℝ) (provider : Provider),
      ¬ Affine287SP2SmallQTypeIAdapterInput u N coeff qRange rRange sgn s targetNorm provider := by
  refine ⟨1, 1, fun _ => 0, ∅, ∅, 1, Erdos287.Vaughan.AffineSign.plus, -1,
    Provider.Gate0TypeI, ?_⟩
  intro h
  have h1 : |sigmaSmallQ 1 1 (fun _ => 0)| ≤ -1 := h.target
  have h2 : (0 : ℝ) ≤ |sigmaSmallQ 1 1 (fun _ => 0)| := abs_nonneg _
  linarith

/-! ## §10  The SmallR switched Type-I interface -/

/-- **`Affine287SP2SmallRSwitchTypeIInput`** — `EXTERNAL / UNINHABITED`.

The SmallR sector is reached by the `q ↔ r` switch.  The switch is *not* assumed to be a
symmetry: the interface must record, as explicit Boolean parameters, whether the switch
moves the Möbius carrier, the log carrier, the normalisation, the sign, the residue class,
and the generated Type-I coefficient law. -/
structure Affine287SP2SmallRSwitchTypeIInput
    (u N : ℕ) (coeff : ℕ × ℕ → ℝ) (targetNorm : ℝ) (provider : Provider)
    (mobiusCarrierSwitched logCarrierSwitched normalizationChanged
      signChanged residueClassChanged coeffLawChanged : Bool) : Prop where
  /-- In this sector the *small* variable is `r`, not `q`. -/
  small_variable_is_r : ∀ x ∈ sectorCell u N QSector.smallR, x.2 ≤ u ∧ u < x.1
  /-- The Möbius factor still sits on `q`, so the Möbius carrier is not switched. -/
  mobius_carrier_flag : mobiusCarrierSwitched = false
  /-- The logarithm moves onto the small variable, so the log carrier is switched. -/
  log_carrier_flag : logCarrierSwitched = true
  /-- The Mellin normalisation changes with the roles of the variables. -/
  normalization_flag : normalizationChanged = true
  /-- The affine sign is unaffected by the switch. -/
  sign_flag : signChanged = false
  /-- The residue class `a_s(q) = −s·2⁻¹ mod q` is attached to `q`, so switching changes
  which variable carries it. -/
  residue_class_flag : residueClassChanged = true
  /-- The generated seven-prime coefficient law is not symmetric in `q ↔ r`. -/
  coefficient_law_flag : coeffLawChanged = true
  /-- The provider actually intended. -/
  typeI_provider : provider = Provider.Gate0TypeI
  /-- The provider's own conclusion. -/
  target : |sigmaSmallR u N coeff| ≤ targetNorm
  /-- Theorem-hypothesis dictionary. -/
  dictionary : targetNorm ≤ sectorTargetNorm N

/-- **`smallR_closed_of_switched_typeI_adapter`** — `CONDITIONAL`. -/
theorem smallR_closed_of_switched_typeI_adapter
    {u N : ℕ} {coeff : ℕ × ℕ → ℝ} {targetNorm : ℝ} {provider : Provider}
    {b1 b2 b3 b4 b5 b6 : Bool}
    (h : Affine287SP2SmallRSwitchTypeIInput u N coeff targetNorm provider b1 b2 b3 b4 b5 b6) :
    |sigmaSmallR u N coeff| ≤ sectorTargetNorm N ∧ provider = Provider.Gate0TypeI ∧
      b6 = true :=
  ⟨le_trans h.target h.dictionary, h.typeI_provider, h.coefficient_law_flag⟩

/-- **`smallRAdapter_not_automatic`** — the interface is a genuine restriction. -/
theorem smallRAdapter_not_automatic :
    ∃ (u N : ℕ) (coeff : ℕ × ℕ → ℝ) (targetNorm : ℝ) (provider : Provider)
      (b1 b2 b3 b4 b5 b6 : Bool),
      ¬ Affine287SP2SmallRSwitchTypeIInput u N coeff targetNorm provider b1 b2 b3 b4 b5 b6 := by
  refine ⟨1, 1, fun _ => 0, -1, Provider.Gate0TypeI, false, true, true, false, true, true, ?_⟩
  intro h
  have h1 : |sigmaSmallR 1 1 (fun _ => 0)| ≤ -1 := h.target
  have h2 : (0 : ℝ) ≤ |sigmaSmallR 1 1 (fun _ => 0)| := abs_nonneg _
  linarith

/-- **Firewall `smallQ_and_smallR_cells_differ`.**  `LEAN_PROVED`.

The `q ↔ r` switch is not a symmetry of the sector decomposition: for `N = 6`, `u = 2`
the SmallQ and SmallR cells are different finite sets.  Hence a SmallQ adapter does not
supply the SmallR sector. -/
theorem smallQ_and_smallR_cells_differ :
    sectorCell 2 6 QSector.smallQ ≠ sectorCell 2 6 QSector.smallR := by
  intro h
  have h1 : ((1 : ℕ), (6 : ℕ)) ∈ sectorCell 2 6 QSector.smallQ := by decide
  rw [h] at h1
  have h2 : sectorOf 2 ((1 : ℕ), (6 : ℕ)) = QSector.smallR := (mem_sectorCell.mp h1).2
  rw [sectorOf_smallQ (by norm_num)] at h2
  exact QSector.noConfusion h2

/-- **`smallQ_smallR_both_open`.**  Neither sector has a provider. -/
theorem smallQ_smallR_both_open :
    SmallQProvider = Provider.SourceOpen ∧ SmallRProvider = Provider.SourceOpen :=
  ⟨rfl, rfl⟩

end V24Adapters
end Erdos287
