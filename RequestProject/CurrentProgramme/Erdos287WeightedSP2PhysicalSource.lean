import Mathlib
import RequestProject.Erdos287.SP2PrimeBoxWeights3221
import RequestProject.CurrentProgramme.SevenBoxPrimeWeights
import RequestProject.CurrentProgramme.Erdos287StrictCellCanonicalSingleton

/-!
# Semantic repair layer §4, §7 — the *weighted* SP-2 physical slot source

`BALANCED7-OMEGABOX-SP2-WEIGHTED-SOURCE-ADAPTER45`

The older product-weight bridge carried the slot field

```
    Dat.omega i p = sp2Omega C i p      (a bare cell indicator).
```

Once the smooth / Mellin packets are included, the physical slot weight is the full

```
    ω^phys_i(p) = sp2Omega(C, i, p) · V_i(p/Y) · exp(i t_i log p),
```

with the repository's own convention for the smooth-and-twist factor: this is exactly
`Erdos287.PostBalanced7Pro.omegaBox`, which is **reused** here rather than redefined
(`omegaPhysical_eq_omegaBox`).

Contents:

* `PhysicalSlotData` — the smooth profile `V_i`, the scale `Y` and the archimedean twists
  `t_i`, with the normalisation `0 ≤ V ≤ 1`;
* `omegaPhysical`, its support identity `p ∈ physical box i ↔ p ∈ λ_i` (under the source
  positivity of the profile), pointwise bound and reduction to `omegaBox`;
* the firewall `weighted_omega_ne_bare_indicator`: the physical weight is **not** the bare
  indicator unless `V = 1` and `t = 0` have separately been specialised
  (`omegaPhysical_eq_sp2Omega_of_trivial`);
* the weighted adapter `BalancedSevenOmegaBoxSP2WeightedSourceAdapter45` (uninhabited source
  obligation) with the pointwise law proved from it;
* `OmegaSharpPhysical`, the full complex-weight integer pushforward, with the **exact**
  finite pushforward identity `∑_pvec Ω(pvec)F(∏p) = ∑_n Ω♯(n)F(n)`, and the guard that
  `Ω♯ = 1` is not automatic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace WeightedSP2

open Finset
open Erdos287.SP2Source
open Erdos287.V21PrimeBox
open Erdos287.SP2PrimeBox
open Erdos287.PostBalanced7Pro
open Erdos287.StrictCellSingleton

/-! ## §1.  The physical slot data -/

/-- **`PhysicalSlotData`** — the smooth/Mellin packet data of the seven physical slots: a
normalised profile `V_i`, the common scale `Y`, and the archimedean twist `t_i`. -/
structure PhysicalSlotData where
  /-- The smooth cutoff profile of slot `i`. -/
  V : Fin 7 → ℝ → ℝ
  /-- The common scale. -/
  Y : ℝ
  /-- The archimedean twist of slot `i`. -/
  t : Fin 7 → ℝ
  /-- Normalisation `0 ≤ V_i`. -/
  V_nonneg : ∀ (i : Fin 7) (x : ℝ), 0 ≤ V i x
  /-- Normalisation `V_i ≤ 1`. -/
  V_le_one : ∀ (i : Fin 7) (x : ℝ), V i x ≤ 1

/-- **`omegaPhysical`** — the full physical slot weight

```
    ω^phys_i(p) = sp2Omega(C,i,p) · V_i(p/Y) · exp(i t_i log p).
```
-/
noncomputable def omegaPhysical (C : SP2FixedCertificateData) (S : PhysicalSlotData)
    (i : Fin 7) (p : ℕ) : ℂ :=
  sp2Omega C i p * (S.V i ((p : ℝ) / S.Y) : ℂ) *
    Complex.exp ((S.t i : ℂ) * (Real.log p : ℂ) * Complex.I)

/-- Off the physical cell the weight vanishes. -/
theorem omegaPhysical_eq_zero_of_not_mem {C : SP2FixedCertificateData}
    {S : PhysicalSlotData} {i : Fin 7} {p : ℕ} (h : p ∉ C.lam i) :
    omegaPhysical C S i p = 0 := by
  simp [omegaPhysical, sp2Omega_eq_zero_of_not_mem h]

/-- On the cell the weight is the pure smooth-and-twist factor. -/
theorem omegaPhysical_of_mem {C : SP2FixedCertificateData} {S : PhysicalSlotData}
    {i : Fin 7} {p : ℕ} (h : p ∈ C.lam i) :
    omegaPhysical C S i p
      = (S.V i ((p : ℝ) / S.Y) : ℂ) *
          Complex.exp ((S.t i : ℂ) * (Real.log p : ℂ) * Complex.I) := by
  rw [omegaPhysical, sp2Omega_eq_one_of_mem h, one_mul]

/-- **`omegaPhysical_eq_omegaBox`.**  `LEAN_PROVED`.

The physical weight *is* the repository's literal seven-box weight `ω_i(p)` on the cell: no
new convention is introduced, the existing `omegaBox` is reused. -/
theorem omegaPhysical_eq_omegaBox {C : SP2FixedCertificateData} {S : PhysicalSlotData}
    {i : Fin 7} {p : ℕ} (hmem : p ∈ C.lam i) (hp : p.Prime) :
    omegaPhysical C S i p = omegaBox (S.V i) S.Y (S.t i) p := by
  rw [omegaPhysical_of_mem hmem, omegaBox, if_pos hp]

/-- **`norm_omegaPhysical_le_one`.**  `LEAN_PROVED`.  The pointwise law survives the
smooth/Mellin dressing. -/
theorem norm_omegaPhysical_le_one (C : SP2FixedCertificateData) (S : PhysicalSlotData)
    (i : Fin 7) (p : ℕ) : ‖omegaPhysical C S i p‖ ≤ 1 := by
  have htw : ‖Complex.exp (((S.t i * Real.log p : ℝ)) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  have hrw : ((S.t i : ℂ) * (Real.log p : ℂ) * Complex.I)
      = ((S.t i * Real.log p : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [omegaPhysical, hrw, norm_mul, norm_mul, htw, mul_one]
  have h1 : ‖sp2Omega C i p‖ ≤ 1 := sp2Omega_norm_le_one C i p
  have h2 : ‖((S.V i ((p : ℝ) / S.Y) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (S.V_nonneg i _)]
    exact S.V_le_one i _
  calc ‖sp2Omega C i p‖ * ‖((S.V i ((p : ℝ) / S.Y) : ℝ) : ℂ)‖
      ≤ 1 * 1 := by
        exact mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := by ring

/-! ## §2.  The exact support identity -/

/-- **`omegaPhysical_support`.**  `LEAN_PROVED`.

The support identity `p ∈ physical box i ↔ p ∈ λ_i`, valid exactly when the smooth profile
does not vanish on the cell — the condition the source supplies. -/
theorem omegaPhysical_support {C : SP2FixedCertificateData} {S : PhysicalSlotData}
    {i : Fin 7} (hV : ∀ p ∈ C.lam i, S.V i ((p : ℝ) / S.Y) ≠ 0) (p : ℕ) :
    omegaPhysical C S i p ≠ 0 ↔ p ∈ C.lam i := by
  constructor
  · intro h
    by_contra hmem
    exact h (omegaPhysical_eq_zero_of_not_mem hmem)
  · intro hmem
    rw [omegaPhysical_of_mem hmem]
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    exact_mod_cast (Complex.ofReal_ne_zero).mpr (hV p hmem)

/-- Without the profile positivity the support can be strictly smaller: the identity is a
*source* statement, not a formality. -/
theorem omegaPhysical_support_needs_profile :
    ∃ (C : SP2FixedCertificateData) (S : PhysicalSlotData) (i : Fin 7) (p : ℕ),
      p ∈ C.lam i ∧ omegaPhysical C S i p = 0 := by
  refine ⟨countermodelCert, ⟨fun _ _ => 0, 1, fun _ => 0, by intros; norm_num,
    by intros; norm_num⟩, 0, 2, ?_, ?_⟩
  · simp [countermodelCert]
  · simp [omegaPhysical]

/-! ## §3.  Firewall: weighted source versus bare indicator -/

/-- With `V = 1` and `t = 0` — and only then, in general — the physical weight collapses to
the bare cell indicator. -/
theorem omegaPhysical_eq_sp2Omega_of_trivial (C : SP2FixedCertificateData)
    {S : PhysicalSlotData} (hV : ∀ (i : Fin 7) (x : ℝ), S.V i x = 1)
    (ht : ∀ i : Fin 7, S.t i = 0) (i : Fin 7) (p : ℕ) :
    omegaPhysical C S i p = sp2Omega C i p := by
  simp [omegaPhysical, hV, ht]

/-- **`weighted_omega_ne_bare_indicator`.**  `LEAN_PROVED`.

The physical weighted slot source is **not** the bare indicator: explicit normalised data
give a cell prime at which the two differ.  Hence the older bare-indicator field is not the
current physical dictionary. -/
theorem weighted_omega_ne_bare_indicator :
    ∃ (C : SP2FixedCertificateData) (S : PhysicalSlotData) (i : Fin 7) (p : ℕ),
      p ∈ C.lam i ∧ omegaPhysical C S i p ≠ sp2Omega C i p := by
  refine ⟨countermodelCert, ⟨fun _ _ => 1 / 2, 1, fun _ => 0, ?_, ?_⟩, 0, 2, ?_, ?_⟩
  · intro i x; norm_num
  · intro i x; norm_num
  · simp [countermodelCert]
  · have hmem : (2 : ℕ) ∈ countermodelCert.lam 0 := by simp [countermodelCert]
    rw [sp2Omega_eq_one_of_mem hmem]
    simp [omegaPhysical, sp2Omega_eq_one_of_mem hmem]

/-! ## §4.  The weighted source adapter (SOURCE_OPEN / UNINHABITED) -/

/-- **`BalancedSevenOmegaBoxSP2WeightedSourceAdapter45`** — `SOURCE_OPEN / UNINHABITED`.

The corrected slot-weight adapter: the physical datum carries the **full** weighted slot
factor, its box is the SP-2 cell, and the profile is nonvanishing on the cell so that the
exact support identity holds.  No inhabitant is constructed. -/
structure BalancedSevenOmegaBoxSP2WeightedSourceAdapter45
    (C : SP2FixedCertificateData) (S : PhysicalSlotData) (Dat : PrimeBoxData) : Prop where
  /-- The SP-2 metadata normalisation. -/
  packet : SP2PacketNormalization C
  /-- The physical slot coefficient is the **full** weighted factor. -/
  omega_eq : ∀ (i : Fin 7) (p : ℕ), Dat.omega i p = omegaPhysical C S i p
  /-- The physical box is the SP-2 cell. -/
  box_eq : ∀ i : Fin 7, Dat.box i = C.lam i
  /-- The source supplies a nonvanishing profile on each cell. -/
  profile_nonvanishing : ∀ (i : Fin 7), ∀ p ∈ C.lam i, S.V i ((p : ℝ) / S.Y) ≠ 0

/-- Given the weighted adapter, the pointwise law is a theorem. -/
theorem weightedAdapter_pointwise {C : SP2FixedCertificateData} {S : PhysicalSlotData}
    {Dat : PrimeBoxData} (h : BalancedSevenOmegaBoxSP2WeightedSourceAdapter45 C S Dat)
    (i : Fin 7) (p : ℕ) : ‖Dat.omega i p‖ ≤ 1 := by
  rw [h.omega_eq i p]; exact norm_omegaPhysical_le_one C S i p

/-- Given the weighted adapter, the support identity `p ∈ box i ↔ p ∈ λ_i` is a theorem. -/
theorem weightedAdapter_support {C : SP2FixedCertificateData} {S : PhysicalSlotData}
    {Dat : PrimeBoxData} (h : BalancedSevenOmegaBoxSP2WeightedSourceAdapter45 C S Dat)
    (i : Fin 7) (p : ℕ) : Dat.omega i p ≠ 0 ↔ p ∈ Dat.box i := by
  rw [h.omega_eq i p, h.box_eq i]
  exact omegaPhysical_support (h.profile_nonvanishing i) p

/-- **`weightedAdapter_not_automatic`.**  `LEAN_PROVED`.  The adapter is a genuine source
obligation: explicit data refute it. -/
theorem weightedAdapter_not_automatic :
    ∃ (C : SP2FixedCertificateData) (S : PhysicalSlotData) (Dat : PrimeBoxData),
      ¬ BalancedSevenOmegaBoxSP2WeightedSourceAdapter45 C S Dat := by
  refine ⟨countermodelCert, ⟨fun _ _ => 0, 1, fun _ => 0, by intros; norm_num,
    by intros; norm_num⟩, ⟨fun _ _ => 0, fun _ => ∅⟩, ?_⟩
  intro h
  have := h.profile_nonvanishing 0 2 (by simp [countermodelCert])
  simp at this

/-! ## §5.  The weighted integer pushforward `Ω♯_phys` -/

/-- **`OmegaSharpPhysical`** — the full complex-weight pushforward of the physical direct
cell along `pvec ↦ ∏ᵢ pᵢ`. -/
noncomputable def OmegaSharpPhysical (C : SP2FixedCertificateData) (S : PhysicalSlotData)
    (n : ℕ) : ℂ :=
  ∑ v ∈ omegaSharpFibre C n, ∏ i, omegaPhysical C S i (v i)

/-- **`omegaSharpPhysical_pushforward`.**  `LEAN_PROVED`.

The **exact** finite pushforward identity

```
    ∑_{pvec ∈ cell} (∏_i ω^phys_i(p_i)) F(∏_i p_i) = ∑_n Ω♯_phys(n) F(n),
```

with `n` ranging over the image of the cell.  No approximation and no normalisation
assumption: in particular `Ω♯_phys(n) = 1` is *not* required. -/
theorem omegaSharpPhysical_pushforward (C : SP2FixedCertificateData)
    (S : PhysicalSlotData) (F : ℕ → ℂ) :
    ∑ v ∈ cellVectors C, (∏ i, omegaPhysical C S i (v i)) * F (pushforward v)
      = ∑ n ∈ (cellVectors C).image pushforward, OmegaSharpPhysical C S n * F n := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := pushforward) (t := (cellVectors C).image pushforward)
    (fun v hv => Finset.mem_image_of_mem _ hv)
    (f := fun v => (∏ i, omegaPhysical C S i (v i)) * F (pushforward v))]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [OmegaSharpPhysical, omegaSharpFibre, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [(Finset.mem_filter.mp hv).2]

/-- **`omegaSharpPhysical_one_not_automatic`.**  `LEAN_PROVED`.

`Ω♯_phys = 1` is not automatic: on the banked balanced certificate with trivial profile and
twist the mass at `192` is `7`. -/
theorem omegaSharpPhysical_one_not_automatic :
    ∃ (C : SP2FixedCertificateData) (S : PhysicalSlotData) (n : ℕ),
      OmegaSharpPhysical C S n = 7 := by
  classical
  refine ⟨countermodelCert, ⟨fun _ _ => 1, 1, fun _ => 0, by intros; norm_num,
    by intros; norm_num⟩, 192, ?_⟩
  have hone : ∀ v ∈ omegaSharpFibre countermodelCert 192,
      (∏ i, omegaPhysical countermodelCert
        ⟨fun _ _ => 1, 1, fun _ => 0, by intros; norm_num, by intros; norm_num⟩ i (v i))
        = 1 := by
    intro v hv
    refine Finset.prod_eq_one fun i _ => ?_
    have hmem : v i ∈ countermodelCert.lam i := by
      have hv' : v ∈ cellVectors countermodelCert := (Finset.mem_filter.mp hv).1
      exact (Fintype.mem_piFinset).mp (by simpa [cellVectors] using hv') i
    rw [omegaPhysical_of_mem hmem]
    simp
  rw [OmegaSharpPhysical, Finset.sum_congr rfl hone, Finset.sum_const,
    countermodel_fibre_card]
  norm_num

end WeightedSP2
end Erdos287
