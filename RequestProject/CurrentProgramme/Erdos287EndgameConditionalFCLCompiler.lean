import RequestProject.CurrentProgramme.Erdos287EndgameSourceSockets
import RequestProject.CurrentProgramme.Erdos287FullAnalyticKernelFCLChannels

/-!
# The conditional FCL compiler of the endgame layer

```
E_T CHANNEL  (master source + analytic kernel)  : KERNEL-PROVED CONDITIONAL
E_L CHANNEL  (U-source subset of master source) : KERNEL-PROVED CONDITIONAL
CONDITIONAL FCL COMPILER                        : KERNEL-PROVED CONDITIONAL
FIXED-CERTIFICATE POSITIVE MASS                 : OPEN (every socket uninhabited)
```

This module is **append-only** and contains no analytic proof whatsoever.

**§1 — the `E_T` channel.**  *Conditionally* on the master-source reconstruction and on the
external `FullSourceLocalAnalyticKernelInput`, the total-correlation deficit obeys

```
    Cc·Bmass − totalCorr  ≤  Cc·Bmass + 17·budget(X) − boundary − truncation  =:  E_T .
```

**§2 — the `E_L` channel.**  The `U`-source subset of the master source compiles into the
leakage error.  The firewall `leakage_not_implied_by_total` shows that `E_L` may **not** be
inferred from `E_T` by any monotonicity argument.

**§3 — the conditional FCL compiler.**  All five sockets

```
    MasterSourceInput + FullAnalyticKernelInput + N2LambdaCollarInput
      + GlobalBsrcComparisonMarginInput + PositiveMarginSupply
```

together with the explicit channel budget give `FixedCertificatePositiveMass`, by reuse of
the four-error transference theorem.  **No analytic estimate disappears from the
hypotheses, and no socket is inhabited.**
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace EndgameFCL

open Erdos287.PhysicalSupport
open Erdos287.FourErrorTransference
open Erdos287.EndgameSockets
open Erdos287.FullAnalyticKernel
open Erdos287.FullAnalyticKernelFCL

/-! ## §1  The `E_T` channel from master source + analytic kernel -/

/-- **`E_T_channel`** — the explicit transverse/total channel produced by the two inputs. -/
noncomputable def E_T_channel (d : PhysicalSupportData) (w : PhysicalWeightData)
    (Cc X boundaryTerm truncationTerm : ℝ) : ℝ :=
  Cc * Bmass d w + 17 * budget X - boundaryTerm - truncationTerm

/-- **`totalCorr_eq_fullCorrelation`.**  `KERNEL-PROVED CONDITIONAL`.

The master-source reconstruction, with owner accounts equal to the analytic owner values,
identifies the physical correlation with the analytic full correlation up to the boundary
and truncation terms. -/
theorem totalCorr_eq_fullCorrelation
    {d : PhysicalSupportData} {w : PhysicalWeightData} {admissible : FordSourceIndex → Prop}
    {X bT tT : ℝ} {v : OwnerValues}
    (hMaster : MasterSourceToTypedPerronPacketsInput d w admissible
      (fun o => ownerValue v o) bT tT)
    (hAnalytic : FullSourceLocalAnalyticKernelInput X v) :
    totalCorr d w = v.fullCorrelation + bT + tT := by
  have hrec := hMaster.reconstruction
  have hacct := hMaster.owner_accounting
  rw [hacct, ownerValues_sum hAnalytic] at hrec
  exact hrec

/-- **`E_T_bound_of_masterSource_and_analyticKernel`.**  `KERNEL-PROVED CONDITIONAL`.

The `E_T` channel bound.  Both inputs occur explicitly; neither is inhabited. -/
theorem E_T_bound_of_masterSource_and_analyticKernel
    {d : PhysicalSupportData} {w : PhysicalWeightData} {admissible : FordSourceIndex → Prop}
    {Cc X bT tT : ℝ} {v : OwnerValues}
    (hMaster : MasterSourceToTypedPerronPacketsInput d w admissible
      (fun o => ownerValue v o) bT tT)
    (hAnalytic : FullSourceLocalAnalyticKernelInput X v) :
    Cc * Bmass d w - totalCorr d w ≤ E_T_channel d w Cc X bT tT := by
  have hEq := totalCorr_eq_fullCorrelation hMaster hAnalytic
  have hbd := fullCorrelation_bound_of_analyticInput hAnalytic
  have h := (abs_le.mp hbd).1
  rw [hEq, E_T_channel]
  linarith

/-! ## §2  The `E_L` channel from the `U`-source subset -/

/-- **`USourceSubsetInput`** — `OPEN / UNINHABITED`.

The `U`-source subset of the master source: the sub-family of emitted packets whose owner
support is the leakage class `U_X`, its exact reconstruction of the leakage correlation,
and the supplied bound on it.  This is the *only* route to `E_L` in this layer. -/
structure USourceSubsetInput (d : PhysicalSupportData) (w : PhysicalWeightData)
    (EL : ℝ) : Prop where
  /-- The leakage correlation is bounded by the supplied leakage error. -/
  leakage_bound : E_L_exact d w ≤ EL

/-- **`E_L_bound_of_uSourceSubset`.**  `KERNEL-PROVED CONDITIONAL`.  The `U`-source subset
compiles into the leakage channel. -/
theorem E_L_bound_of_uSourceSubset {d : PhysicalSupportData} {w : PhysicalWeightData}
    {EL : ℝ} (h : USourceSubsetInput d w EL) : E_L_exact d w ≤ EL :=
  h.leakage_bound

/-- **`leakage_not_implied_by_total`.**  `KERNEL-PROVED` firewall.

`E_L` may **not** be inferred from `E_T` by monotonicity: explicit physical data have total
correlation `0` while the leakage class alone carries correlation `10`.  A bound on the
total therefore says nothing about the leakage channel. -/
theorem leakage_not_implied_by_total :
    ∃ (d : PhysicalSupportData) (w : PhysicalWeightData),
      totalCorr d w = 0 ∧ 1 < E_L_exact d w := by
  refine ⟨⟨{1, 2}, fun n => if n = 1 then SupportClass.U else SupportClass.N1⟩,
    ⟨1, fun _ => 1, fun _ => 0, fun n => if n = 1 then -5 / 2 else 5 / 2, fun _ => 1⟩,
    ?_, ?_⟩
  · simp [totalCorr, corrOn, PhysicalWeightData.wX, PhysicalWeightData.aX,
      PhysicalWeightData.bX, PhysicalWeightData.HX]
    norm_num
  · have : E_L_exact (⟨{1, 2}, fun n => if n = 1 then SupportClass.U else SupportClass.N1⟩ :
        PhysicalSupportData)
        (⟨1, fun _ => 1, fun _ => 0, fun n => if n = 1 then -5 / 2 else 5 / 2, fun _ => 1⟩ :
        PhysicalWeightData) = 10 := by
      simp [E_L_exact, corrOn, PhysicalSupportData.UX, PhysicalSupportData.region,
        PhysicalWeightData.wX, PhysicalWeightData.aX, PhysicalWeightData.bX,
        PhysicalWeightData.HX, Finset.filter_insert, Finset.filter_singleton]
      norm_num
    rw [this]; norm_num

/-! ## §3  The conditional FCL compiler -/

/-- **`FixedCertificatePositiveMass`** — the conclusion of the FCL layer: the
certificate-positive class carries strictly positive prime mass. -/
def FixedCertificatePositiveMass (d : PhysicalSupportData) (w : PhysicalWeightData) : Prop :=
  0 < primeMass d w

/-- **`fixedCertificatePositiveMass_of_all_sockets`.**  `KERNEL-PROVED CONDITIONAL`.

The endgame FCL compiler:

```
    MasterSourceInput + FullAnalyticKernelInput + N2LambdaCollarInput
      + GlobalBsrcComparisonMarginInput + PositiveMarginSupply + U-source subset
      + the explicit channel budget
        ⟹  FixedCertificatePositiveMass .
```

Every analytic input is an explicit hypothesis and none is constructed anywhere; the
four-error transference theorem is reused, not reproved. -/
theorem fixedCertificatePositiveMass_of_all_sockets
    {d : PhysicalSupportData} {w : PhysicalWeightData} {admissible : FordSourceIndex → Prop}
    {physicalB : ℕ → ℝ} {Cc X bT tT EL delta2 deltaM bLower : ℝ} {v : OwnerValues}
    (hKernel : ∀ n ∈ d.PX, w.HX n = 1)
    (hMaster : MasterSourceToTypedPerronPacketsInput d w admissible
      (fun o => ownerValue v o) bT tT)
    (hAnalytic : FullSourceLocalAnalyticKernelInput X v)
    (hCollar : FixedCertificateN2LambdaCollarInput d w delta2)
    (hBsrc : GlobalBsrcComparisonMarginInput d w physicalB deltaM bLower)
    (hMargin : Erdos287.FCLBridge.PositiveMarginSupply Cc)
    (hLeak : USourceSubsetInput d w EL)
    (hbudget : E_T_channel d w Cc X bT tT + EL + delta2 * Bmass d w + deltaM * Bmass d w
      ≤ (1 + Cc) / 6 * Bmass d w) :
    FixedCertificatePositiveMass d w := by
  have hBpos : 0 < Bmass d w := lt_of_lt_of_le hBsrc.Bmass_lower.1 hBsrc.Bmass_lower.2
  have hdom : ChannelDomination d w
      ⟨Cc, E_T_channel d w Cc X bT tT, EL, delta2 * Bmass d w, deltaM * Bmass d w⟩ :=
    { kernel_on_P := hKernel
      total_channel := E_T_bound_of_masterSource_and_analyticKernel hMaster hAnalytic
      main_channel := hBsrc.E_M_bound
      collar_channel := hCollar.collar
      leakage_channel := E_L_bound_of_uSourceSubset hLeak }
  exact transference_with_supplied_margin hMargin hdom hBpos hbudget

/-- **`fcl_compiler_keeps_every_analytic_hypothesis`.**  `KERNEL-PROVED`.

The compiler is genuinely conditional at each socket: each of the master source, the
`N2` collar and the global `Bsrc` comparison is refutable at explicit data, so none of them
may be dropped or silently discharged. -/
theorem fcl_compiler_keeps_every_analytic_hypothesis :
    (∃ (d : PhysicalSupportData) (w : PhysicalWeightData)
        (adm : FordSourceIndex → Prop) (acct : Owner → ℝ) (bT tT : ℝ),
      IsEmpty (MasterSourceToTypedPerronPacketsInput d w adm acct bT tT)) ∧
    (∃ (d : PhysicalSupportData) (w : PhysicalWeightData) (delta2 : ℝ),
      ¬ FixedCertificateN2LambdaCollarInput d w delta2) ∧
    (∃ (d : PhysicalSupportData) (w : PhysicalWeightData) (pB : ℕ → ℝ) (dM bL : ℝ),
      ¬ GlobalBsrcComparisonMarginInput d w pB dM bL) ∧
    (∃ Cc : ℝ, ¬ Erdos287.FCLBridge.PositiveMarginSupply Cc) :=
  ⟨masterSource_socket_is_a_genuine_constraint,
    n2Collar_socket_is_a_genuine_constraint,
    bsrcComparison_socket_is_a_genuine_constraint,
    Erdos287.FCLBridge.positiveMargin_not_automatic⟩

/-- **`fixedCertificatePositiveMass_not_established`.**  `KERNEL-PROVED`.

Nothing here establishes the conclusion unconditionally: at explicit data the conclusion is
false, so the compiler's hypotheses carry all of its content. -/
theorem fixedCertificatePositiveMass_not_established :
    ∃ (d : PhysicalSupportData) (w : PhysicalWeightData),
      ¬ FixedCertificatePositiveMass d w := by
  refine ⟨⟨∅, fun _ => SupportClass.P⟩, ⟨1, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    ?_⟩
  intro h
  rw [FixedCertificatePositiveMass, primeMass] at h
  simp [PhysicalSupportData.PX, PhysicalSupportData.region] at h

end EndgameFCL
end Erdos287
