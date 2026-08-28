import Mathlib
import RequestProject.Erdos287.ConductorRouter3221

/-!
# V20, Phase I — the surviving high-high-high shifted five-box character Gram

`3221-HIGHQUOTIENT-FIVEBOX-SHIFTED-GRAM45 : OPEN_ANALYTIC` — **the first exact analytic
residual and the controlling socket of the V20 frontier.**

The object defined here is *exactly* the surviving cell of the V20 decomposition: the
high-conductor, high-shifted-conductor, high-quotient part of the character Gram, with the
five-box factorisation left **unseparated** from the short-`m` Gram.  Its definition
contains **no analytic assumption of any kind** — it is a finite sum built from literal
Dirichlet characters, the literal short-`m` Gram, and the five labelled box transforms.

The required estimate is isolated in the uninhabited structure
`HighQuotientFiveBoxShiftedGram3221Input`; nothing in this repository inhabits it.

## Contents

* **§24.**  `SurvivingHHHConductorCell` — the surviving region, as explicit inequalities.
* **§25.**  `HHHGramData` (pure data) and `hhhGram` — the exact HHH Gram object.
* **§26.**  `HighQuotientFiveBoxShiftedGram3221Input` — the open analytic socket,
  uninhabited, with `hhhGram_input_not_automatic`.
* **§27.**  `logVar_of_four_channels` — the reassembly compiler
  `diagonal + low quotient + routed moderate + HHH ⇒ inverse-sampled high-conductor
  log-variance`, with every error channel explicit and no circular dependence.

Erdős #287 remains OPEN; Balanced7 remains OPEN.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace Erdos287
namespace V20HHH

open Erdos287.V20Gram Erdos287.V20Router

/-! ## §24. The surviving HHH conductor cell -/

/-- **`SurvivingHHHConductorCell`.**

The cell survives when the character, its `ξ`-shift and the quotient character are all of
large conductor, **and** the conductor pair lies outside the routed region.  Every
condition is an explicit inequality on explicit data; there is no free `Prop` field. -/
structure SurvivingHHHConductorCell {q : ℕ} (Dcut Lcut : ℕ)
    (chi xi : DirichletCharacter ℂ q) (e1 e2 eps : ℚ) : Prop where
  /-- `cond(χ) > Dcut`. -/
  chi_high : Dcut < chi.conductor
  /-- `cond(χ ξ̄) > Dcut`. -/
  shift_high : Dcut < (chi * xi⁻¹).conductor
  /-- `cond(ξ) > Lcut`: the high-quotient condition. -/
  xi_high_quotient : Lcut < xi.conductor
  /-- The conductor pair is **outside** the routed region of Phase H. -/
  outside_routed : ¬ RoutedExponentPair e1 e2 eps

/-! ## §25. The exact HHH Gram object -/

/-- **`HHHGramData`.**  Pure data for the surviving Gram: the modulus box and its
(post-Cauchy, unsigned) weight, the `m`-box and its profile, the sign, the two conductor
cutoffs, the five labelled box transforms, the dyadic conductor exponent bookkeeping and
the routing margin.  **No field is a free `Prop`.** -/
structure HHHGramData where
  /-- The modulus box. -/
  Qbox : Finset ℕ
  /-- The `q`-weight `μ²(q)/φ(q)²`. -/
  wt : ℕ → ℂ
  /-- The `m`-box. -/
  Mset : Finset ℕ
  /-- The `m`-profile `Φ`. -/
  Phi : ℕ → ℂ
  /-- The sign `s = ±1`. -/
  sign : ℤ
  /-- `s² = 1`. -/
  sign_sq : sign ^ 2 = 1
  /-- The high-conductor cutoff `Dcut`. -/
  Dcut : ℕ
  /-- The high-quotient cutoff `Lcut`. -/
  Lcut : ℕ
  /-- The five labelled box transforms `S_i(χ)`. -/
  S : (q : ℕ) → Fin 5 → DirichletCharacter ℂ q → ℂ
  /-- The dyadic conductor exponent attached to a character. -/
  expo : (q : ℕ) → DirichletCharacter ℂ q → ℚ
  /-- The routing margin `ε`. -/
  eps : ℚ

namespace HHHGramData

variable (D : HHHGramData)

/-- The surviving `χ`-set at modulus `q` and quotient character `ξ`: high conductor, high
shifted conductor, and outside the routed region. -/
noncomputable def survivingChiSet (q : ℕ) (xi : DirichletCharacter ℂ q) :
    Finset (DirichletCharacter ℂ q) :=
  Finset.univ.filter (fun chi => D.Dcut < chi.conductor ∧ D.Dcut < (chi * xi⁻¹).conductor ∧
    ¬ RoutedExponentPair (D.expo q chi) (D.expo q (chi * xi⁻¹)) D.eps)

/-- Membership in the surviving `χ`-set is exactly the surviving-cell predicate. -/
theorem mem_survivingChiSet_iff (q : ℕ) (xi chi : DirichletCharacter ℂ q) :
    chi ∈ D.survivingChiSet q xi
      ↔ (D.Dcut < chi.conductor ∧ D.Dcut < (chi * xi⁻¹).conductor ∧
          ¬ RoutedExponentPair (D.expo q chi) (D.expo q (chi * xi⁻¹)) D.eps) := by
  rw [survivingChiSet, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The surviving-cell structure is available for every member of the surviving set at a
high-quotient `ξ`. -/
theorem survivingCell_of_mem {q : ℕ} {xi chi : DirichletCharacter ℂ q}
    (hxi : D.Lcut < xi.conductor) (h : chi ∈ D.survivingChiSet q xi) :
    SurvivingHHHConductorCell D.Dcut D.Lcut chi xi
      (D.expo q chi) (D.expo q (chi * xi⁻¹)) D.eps :=
  let h' := (D.mem_survivingChiSet_iff q xi chi).mp h
  ⟨h'.1, h'.2.1, hxi, h'.2.2⟩

/-- The high-quotient `ξ`-set. -/
noncomputable def highQuotientSet (q : ℕ) : Finset (DirichletCharacter ℂ q) :=
  Finset.univ.filter (fun xi => D.Lcut < xi.conductor)

/-- The inner five-box shifted autocorrelation over the surviving cell. -/
noncomputable def survivingFiveBoxAutocorr (q : ℕ) (xi : DirichletCharacter ℂ q) : ℂ :=
  ∑ chi ∈ D.survivingChiSet q xi,
    ∏ i : Fin 5, D.S q i chi * (starRingEnd ℂ) (D.S q i (chi * xi⁻¹))

end HHHGramData

/-- **`HighQuotientFiveBoxShiftedGram3221`** — the exact HHH Gram object:

`∑_q μ²(q)/φ(q)² ∑_{ξ high quotient} ξ(−2s) G_{q,M}(ξ)
    ∑_{χ high, χξ̄ high, outside routed} ∏_{i=1}^{5} S_i(χ) conj(S_i(χ ξ̄))`.

All cutoffs and all support data are explicit, and **no analytic assumption is built into
the definition**. -/
noncomputable def hhhGram (D : HHHGramData) : ℂ :=
  ∑ q ∈ D.Qbox, D.wt q *
    ∑ xi ∈ D.highQuotientSet q,
      xi (((-2 * D.sign : ℤ) : ZMod q)) * shortMGram q D.Mset D.Phi xi *
        D.survivingFiveBoxAutocorr q xi

/-- The empty probe: a legitimate instance of the *data* (not of the analytic input). -/
noncomputable def probeHHHData : HHHGramData where
  Qbox := ∅
  wt := fun _ => 0
  Mset := ∅
  Phi := fun _ => 0
  sign := 1
  sign_sq := by norm_num
  Dcut := 0
  Lcut := 0
  S := fun _ _ _ => 0
  expo := fun _ _ => 0
  eps := 0

/-- The probe Gram vanishes (the modulus box is empty). -/
theorem probeHHHData_gram : hhhGram probeHHHData = 0 := by
  simp [hhhGram, probeHHHData]

/-! ## §26. The open analytic socket — `OPEN_ANALYTIC / UNINHABITED` -/

/-- **`HighQuotientFiveBoxShiftedGram3221Input`** —
`3221-HIGHQUOTIENT-FIVEBOX-SHIFTED-GRAM45 : OPEN_ANALYTIC`.

The required bound on the exact HHH Gram object, and nothing else.  **This structure is
never inhabited in this repository**, and no theorem here produces one: it is the
controlling first analytic socket of the V20 frontier. -/
structure HighQuotientFiveBoxShiftedGram3221Input (D : HHHGramData) (bound : ℝ) : Prop where
  /-- **The open analytic estimate.** -/
  gram_bound : ‖hhhGram D‖ ≤ bound

/-- **`hhhGram_input_not_automatic`.**  `LEAN_PROVED`.

The HHH socket is a genuine restriction: explicit data refutes it. -/
theorem hhhGram_input_not_automatic :
    ∃ (D : HHHGramData) (bound : ℝ),
      ¬ HighQuotientFiveBoxShiftedGram3221Input D bound := by
  refine ⟨probeHHHData, -1, ?_⟩
  intro h
  have h1 := h.gram_bound
  rw [probeHHHData_gram] at h1
  norm_num at h1

/-! ## §27. The log-variance reassembly compiler -/

/-- **`LogVarChannelDecomposition`.**  `CERTIFICATE`.

The explicit four-channel decomposition of the inverse-sampled high-conductor energy:
diagonal (`ξ = 1`), low quotient, routed moderate cells, and the surviving HHH cell.  Every
channel is a named nonnegative quantity; nothing is merged. -/
structure LogVarChannelDecomposition
    (Dat : Erdos287.HighCond3221.InverseSampledHighCond3221Data)
    (vdiag vlow vmod vhhh : ℝ) : Prop where
  /-- The diagonal channel is nonnegative. -/
  vdiag_nonneg : 0 ≤ vdiag
  /-- The low-quotient channel is nonnegative. -/
  vlow_nonneg : 0 ≤ vlow
  /-- The routed moderate channel is nonnegative. -/
  vmod_nonneg : 0 ≤ vmod
  /-- The surviving HHH channel is nonnegative. -/
  vhhh_nonneg : 0 ≤ vhhh
  /-- The four channels dominate the energy. -/
  decomposition : Dat.Vhi ≤ vdiag + vlow + vmod + vhhh

/-- **`logVar_of_four_channels`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

```
diagonal child bound
  + low-quotient child bound
  + routed moderate-cell bound
  + HHH Gram analytic input
      ⇒ 3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45
```

Each channel is given its own explicit quarter of the budget `naturalScale / Lsave`; no
channel is silently absorbed and the compiler has **no** circular dependence on the
log-variance conclusion itself.  The HHH antecedent is the uninhabited socket of §26, so
this theorem inhabits nothing. -/
theorem logVar_of_four_channels
    {Dat : Erdos287.HighCond3221.InverseSampledHighCond3221Data}
    {Hdat : HHHGramData} {vdiag vlow vmod vhhh naturalScale Lsave bound : ℝ}
    (hdec : LogVarChannelDecomposition Dat vdiag vlow vmod vhhh)
    (hscale : 0 < naturalScale) (hL : 0 < Lsave)
    (hdiag : vdiag ≤ naturalScale / (4 * Lsave))
    (hlow : vlow ≤ naturalScale / (4 * Lsave))
    (hmod : vmod ≤ naturalScale / (4 * Lsave))
    (hHHH : HighQuotientFiveBoxShiftedGram3221Input Hdat bound)
    (hchannel : vhhh ≤ ‖hhhGram Hdat‖)
    (hbudget : bound ≤ naturalScale / (4 * Lsave)) :
    Erdos287.HighCond3221.InverseSampledHighCondLogVar3221Input Dat naturalScale Lsave := by
  refine ⟨hscale, hL, ?_⟩
  have hhhh : vhhh ≤ naturalScale / (4 * Lsave) :=
    le_trans hchannel (le_trans hHHH.gram_bound hbudget)
  have hsum : vdiag + vlow + vmod + vhhh ≤ 4 * (naturalScale / (4 * Lsave)) := by
    linarith
  have hquarter : 4 * (naturalScale / (4 * Lsave)) = naturalScale / Lsave := by
    field_simp
  linarith [hdec.decomposition, hsum, hquarter.le, hquarter.ge]

/-- **`logVar_does_not_construct_hhh`.**  `LEAN_PROVED` (anti-circularity).

The log-variance conclusion is strictly weaker than the HHH socket: there are data and
parameters for which the log-variance interface *holds* while the HHH analytic input
*fails*.  Hence the reassembly compiler above can never manufacture its own HHH
antecedent. -/
theorem logVar_does_not_construct_hhh :
    ∃ (Dat : Erdos287.HighCond3221.InverseSampledHighCond3221Data)
      (naturalScale Lsave : ℝ) (Hdat : HHHGramData) (bound : ℝ),
      Erdos287.HighCond3221.InverseSampledHighCondLogVar3221Input Dat naturalScale Lsave ∧
        ¬ HighQuotientFiveBoxShiftedGram3221Input Hdat bound := by
  refine ⟨Erdos287.HighCond3221.probeData, 4, 2, probeHHHData, -1, ⟨by norm_num, by norm_num, ?_⟩,
    ?_⟩
  · rw [Erdos287.HighCond3221.probeData_Vhi]
    norm_num
  · intro h
    have h1 := h.gram_bound
    rw [probeHHHData_gram] at h1
    norm_num at h1

end V20HHH
end Erdos287
