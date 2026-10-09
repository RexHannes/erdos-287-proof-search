import RequestProject.Erdos287.ResearchBankV27.DecoratedLemma
import RequestProject.Erdos287.ResearchBankV27.CRTColourOrbit
import RequestProject.Erdos287.ResearchBankV27.SmoothFrequencyRecovery
import RequestProject.Erdos287.ResearchBankV27.GlobalConductorSum

/-!
# Erdős #287 — Research Bank V27 §9: the DERIVED clean-nonzero theorem

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The clean nonzero bound is here a THEOREM, derived from:
* the decorated master lemma (`DecoratedLemma`, itself LEAN CONDITIONAL on `DISpectralProvider`
  and `RepresentationMomentProvider`);
* the finite-label colour energy and the CRT orbit count (`FiniteLabelEnergy`, `CRTColourOrbit`,
  LEAN BANK);
* the exact `1/d` factor and the global conductor aggregation (`GlobalConductorSum`,
  LEAN CONDITIONAL on `DivisorSumProvider`);
* the named operator/pruning contract `NonzeroPruningContract` (the identity
  `R_nonzero = Σ_{D,b} Γ(D,b) P_clean(D,b) + E` with an acceptable error `E`).

Smooth-cutoff recovery (`SmoothFrequencyRecovery`) enters through the kernel `K` of each clean
state; its providers are recorded in the V28 analytic bundle.

**LEAN CONDITIONAL.**
* **`clean_state_bound`** — `|P_clean(D,b,d)| ≤ √φ(E_D) · √3 N_q x^{−η} / d` and
  `≤ √D · √3 N_q x^{−η} / d`;
* **`clean_global_bound`** — `Σ_{D,b} |Γ(D,b)| |P_clean(D,b)| ≤ √3 (N²/U) x^{−347/418000 + ε}`;
* **`clean_nonzero_derived`** (`CleanNonzeroDerivedProvider`, a theorem) — for every fixed `A`
  there is `X₀` such that for `x ≥ X₀`: `[Re R_nonzero]_+ ≤ (N²/U) / log^A x`.

**LEAN BANK.**
* `log_power_absorbed` — `K · log^A x ≤ x^c` eventually, for fixed `c > 0`.
-/

namespace Erdos287
namespace ResearchBankV27
namespace CleanNonzero

open Finset Filter CommonCauchy FiniteLabelEnergy CRTColourOrbit DecoratedLemma DISpectral
  DecoratedMaynardSetup GlobalConductorSum

/-- One clean state `(D, b, d)` at scale `x`: its decorated data, colour data and `d`. -/
structure CleanState (x : ℝ) where
  DD : DecoratedData
  D : ℕ
  [hD : NeZero D]
  t : ℕ
  Ψ0 : DD.I → ℂ
  hΨ0 : ∀ i, ‖Ψ0 i‖ ≤ 1
  v1 : DD.I → ZMod D
  hh : DD.I → ZMod D
  w : DD.O → (ZMod D)ˣ
  d : ℝ
  hd : 0 < d
  hx : DD.KD.x = x
  hΔ1eq : DD.Delta1 = Delta1 DD.KD.N DD.KD.R DD.KD.S DD.KD.x
  hΔ1 : 0 ≤ DD.Delta1
  hNq : 0 ≤ DD.KD.Nq

attribute [instance] CleanState.hD

/-- The clean sum `P_clean(D,b,d) = (1/d) · (coloured decorated sum)`. -/
noncomputable def CleanState.P {x : ℝ} (s : CleanState x) : ℂ :=
  ((1 / s.d : ℝ) : ℂ) * colouredSum s.D s.t s.DD.A s.DD.K s.Ψ0 s.v1 s.hh s.w

/-- Clean admissibility at level `η`: the form lies in the DI class, Maynard admissibility,
`ε ≤ η`, `T ≤ x^{η/4+ε}`. -/
def CleanAdmissible (DIClass : KloostermanData → Prop) (η : ℝ) {x : ℝ} (s : CleanState x) :
    Prop :=
  DIClass s.DD.KD ∧ MaynardAdmissible η s.DD.KD ∧ s.DD.eps ≤ η ∧ s.DD.KD.T ≤ s.DD.KD.x ^ (η / 4 + s.DD.eps)

/-- **Clean state bound** (LEAN CONDITIONAL on `DISpectralProvider` and
`RepresentationMomentProvider`). -/
theorem clean_state_bound {DIClass : KloostermanData → Prop} {η x : ℝ} (hη : 0 < η)
    (hDI : DISpectralProvider η DIClass) (s : CleanState x)
    (hRep : RepresentationMomentProvider s.DD) (hadm : CleanAdmissible DIClass η s) :
    ‖s.P‖ ≤ Real.sqrt (Nat.totient (ED s.D s.t)) *
        (Real.sqrt 3 * s.DD.KD.Nq * x ^ (-η)) / s.d ∧
      ‖s.P‖ ≤ Real.sqrt s.D * (Real.sqrt 3 * s.DD.KD.Nq * x ^ (-η)) / s.d := by
  obtain ⟨hC, hMA, hε, hT⟩ := hadm
  have hx1 : 1 ≤ s.DD.KD.x := hMA.1.le
  have hx0 : 0 < s.DD.KD.x := by linarith
  have hDIc := hDI.spectral _ hC hMA
  have hd1 : s.DD.Delta1 ≤ s.DD.KD.x ^ (-7 * η) := by
    rw [s.hΔ1eq]; exact hMA.2.2.1.1
  obtain ⟨hd2, hd3⟩ := admissible_delta_bounds hMA
  set B := Real.sqrt 3 * s.DD.KD.Nq * s.DD.KD.x ^ (-η) with hBdef
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) s.hNq) (Real.rpow_nonneg hx0.le _)
  have hsingle : ∀ Ψ : s.DD.I → ℂ, (∀ i, ‖Ψ i‖ ≤ 1) →
      (∑ o, s.DD.w o) * energy s.DD.K Ψ ≤ B ^ 2 := by
    intro Ψ hΨ
    rw [s.DD.hmass]
    refine (decorated_conservative s.DD hx1 hη hDIc hRep hε hMA.2.1 hT s.hΔ1 hd1 hd2 hd3 Ψ
      hΨ).trans (le_of_eq ?_)
    rw [hBdef, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), ← Real.rpow_mul_natCast hx0.le]
    push_cast; ring_nf
  obtain ⟨h1, h2⟩ := colour_sqrt_phi_bound s.D s.t s.DD.A s.DD.w s.DD.hA s.DD.K s.Ψ0 s.hΨ0
    s.v1 s.hh s.w hB hsingle
  have hPn : ‖s.P‖ = ‖colouredSum s.D s.t s.DD.A s.DD.K s.Ψ0 s.v1 s.hh s.w‖ / s.d := by
    unfold CleanState.P
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by have := s.hd; positivity)]
    ring
  have hxeq : s.DD.KD.x ^ (-η) = x ^ (-η) := by rw [s.hx]
  rw [hBdef, hxeq] at h1 h2
  rw [hPn]
  exact ⟨div_le_div_of_nonneg_right h1 s.hd.le, div_le_div_of_nonneg_right h2 s.hd.le⟩

/-- **Global clean bound** (LEAN CONDITIONAL on `DISpectralProvider`,
`RepresentationMomentProvider` for every state, and `DivisorSumProvider`): with the root-mass
contract `Σ_b |Γ(D,b)| ≤ τ(D)^C` and the common normalisation `N_q / d = N²/U`,
`Σ_{D,b} |Γ(D,b)| |P_clean(D,b)| ≤ √3 (N²/U) x^{−347/418000 + ε}`. -/
theorem clean_global_bound {DIClass : KloostermanData → Prop} {β : Type*} {x ε NU : ℝ}
    (hNU : 0 ≤ NU) (hDI : DISpectralProvider (1 / 1100) DIClass) (Ds : Finset ℕ) (bs : ℕ → Finset β)
    (st : ℕ → β → CleanState x) (Γ : ℕ → β → ℂ) (C : ℕ)
    (hstD : ∀ D ∈ Ds, ∀ b ∈ bs D, (st D b).D = D)
    (hnorm : ∀ D ∈ Ds, ∀ b ∈ bs D, (st D b).DD.KD.Nq / (st D b).d = NU)
    (hRep : ∀ D ∈ Ds, ∀ b ∈ bs D, RepresentationMomentProvider (st D b).DD)
    (hadm : ∀ D ∈ Ds, ∀ b ∈ bs D, CleanAdmissible DIClass (1 / 1100) (st D b))
    (hroot : ∀ D ∈ Ds, ∑ b ∈ bs D, ‖Γ D b‖ ≤ ((Nat.divisors D).card : ℝ) ^ C)
    (hdiv : DivisorSumProvider Ds C x (1 / 19000) ε) (hx : 0 < x) :
    ∑ D ∈ Ds, ∑ b ∈ bs D, ‖Γ D b‖ * ‖(st D b).P‖ ≤
      Real.sqrt 3 * NU * x ^ (-(347 / 418000) + ε) := by
  have hB : 0 ≤ Real.sqrt 3 * NU * x ^ (-(1 / 1100 : ℝ)) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hNU) (Real.rpow_nonneg hx.le _)
  have hstate : ∀ D ∈ Ds, ∀ b ∈ bs D,
      ‖(st D b).P‖ ≤ Real.sqrt D * (Real.sqrt 3 * NU * x ^ (-(1 / 1100 : ℝ))) := by
    intro D hD b hb
    have h := (clean_state_bound (by norm_num) hDI (st D b) (hRep D hD b hb) (hadm D hD b hb)).2
    rw [hstD D hD b hb] at h
    refine h.trans (le_of_eq ?_)
    rw [← hnorm D hD b hb]; ring
  have := global_aggregation Ds bs Γ (fun D b => (st D b).P) C hB hroot hstate hdiv
  refine this.trans (le_of_eq ?_)
  rw [show x ^ (3 * (1 / 19000 : ℝ) / 2 + ε) * (Real.sqrt 3 * NU * x ^ (-(1 / 1100 : ℝ))) =
    Real.sqrt 3 * NU * (x ^ (3 * (1 / 19000 : ℝ) / 2 + ε) * x ^ (-(1 / 1100 : ℝ))) by ring,
    global_saving_rpow hx]

/-- **Log-power absorption** (LEAN BANK): for fixed `c > 0`, `K > 0`, `A`,
eventually `K · log^A x ≤ x^c`. -/
theorem log_power_absorbed (c A K : ℝ) (hc : 0 < c) (hK : 0 < K) :
    ∀ᶠ x in atTop, K * Real.log x ^ A ≤ x ^ c := by
  have h := (isLittleO_log_rpow_rpow_atTop A hc).bound (c := 1 / K) (by positivity)
  filter_upwards [h, eventually_ge_atTop 1] with x hx hx1
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
  calc K * Real.log x ^ A ≤ K * (1 / K * x ^ c) := mul_le_mul_of_nonneg_left hx hK.le
    _ = x ^ c := by field_simp

/-- **Operator / pruning contract** (named composition interface): the nonzero-frequency form is
the clean aggregate plus an acceptable error `E` with `|E| ≤ (N²/U) x^{−347/836000}`. -/
structure NonzeroPruningContract {β : Type*} (Rnz : ℂ) (Ds : Finset ℕ) (bs : ℕ → Finset β)
    (Γ P : ℕ → β → ℂ) (NU x : ℝ) : Prop where
  decomp : ∃ E : ℂ, Rnz = (∑ D ∈ Ds, ∑ b ∈ bs D, Γ D b * P D b) + E ∧
    ‖E‖ ≤ NU * x ^ (-(347 / 836000 : ℝ))

/-- **`CleanNonzeroDerivedProvider` — a THEOREM, not an assumption** (LEAN CONDITIONAL on
`DISpectralProvider`, `RepresentationMomentProvider`, `DivisorSumProvider` and the named
`NonzeroPruningContract`): for every fixed `A` there is `X₀` such that for all `x ≥ X₀`,
`[Re R_nonzero]_+ ≤ (N²/U) / log^A x`. -/
theorem clean_nonzero_derived (A : ℝ) :
    ∃ X0 : ℝ, ∀ x ≥ X0, ∀ {β : Type} {DIClass : KloostermanData → Prop} (ε NU : ℝ) (Rnz : ℂ),
      0 ≤ NU → ε ≤ 347 / 836000 → DISpectralProvider (1 / 1100) DIClass →
      ∀ (Ds : Finset ℕ) (bs : ℕ → Finset β) (st : ℕ → β → CleanState x) (Γ : ℕ → β → ℂ) (C : ℕ),
      (∀ D ∈ Ds, ∀ b ∈ bs D, (st D b).D = D) →
      (∀ D ∈ Ds, ∀ b ∈ bs D, (st D b).DD.KD.Nq / (st D b).d = NU) →
      (∀ D ∈ Ds, ∀ b ∈ bs D, RepresentationMomentProvider (st D b).DD) →
      (∀ D ∈ Ds, ∀ b ∈ bs D, CleanAdmissible DIClass (1 / 1100) (st D b)) →
      (∀ D ∈ Ds, ∑ b ∈ bs D, ‖Γ D b‖ ≤ ((Nat.divisors D).card : ℝ) ^ C) →
      DivisorSumProvider Ds C x (1 / 19000) ε →
      NonzeroPruningContract Rnz Ds bs Γ (fun D b => (st D b).P) NU x →
      max Rnz.re 0 ≤ NU / Real.log x ^ A := by
  obtain ⟨X1, hX1⟩ := eventually_atTop.1
    (log_power_absorbed (347 / 836000) A (Real.sqrt 3 + 1) (by norm_num) (by positivity))
  refine ⟨max X1 2, fun x hx β DIClass ε NU Rnz hNU hε hDI Ds bs st Γ C hstD hnorm hRep hadm hroot hdiv
    hprune => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlog _
  have hkey := hX1 x (le_trans (le_max_left _ _) hx)
  have hglob := clean_global_bound hNU hDI Ds bs st Γ C hstD hnorm hRep hadm hroot hdiv hx0
  obtain ⟨E, hR, hE⟩ := hprune.decomp
  have hsum : ‖∑ D ∈ Ds, ∑ b ∈ bs D, Γ D b * (st D b).P‖ ≤
      ∑ D ∈ Ds, ∑ b ∈ bs D, ‖Γ D b‖ * ‖(st D b).P‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun D _ =>
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun b _ => norm_mul _ _)))
  have hmono : x ^ (-(347 / 418000 : ℝ) + ε) ≤ x ^ (-(347 / 836000 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  set y := x ^ (-(347 / 836000 : ℝ)) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg hx0.le _
  have hRn : ‖Rnz‖ ≤ (Real.sqrt 3 + 1) * NU * y := by
    rw [hR]
    refine (norm_add_le _ _).trans ?_
    have := mul_le_mul_of_nonneg_left hmono (mul_nonneg (Real.sqrt_nonneg 3) hNU)
    nlinarith
  have hyl : (Real.sqrt 3 + 1) * y * Real.log x ^ A ≤ 1 := by
    have hxc : 0 < x ^ (347 / 836000 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have hyx : y * x ^ (347 / 836000 : ℝ) = 1 := by
      rw [hy, ← Real.rpow_add hx0]; norm_num
    calc (Real.sqrt 3 + 1) * y * Real.log x ^ A = y * ((Real.sqrt 3 + 1) * Real.log x ^ A) := by
          ring
      _ ≤ y * x ^ (347 / 836000 : ℝ) := mul_le_mul_of_nonneg_left hkey hy0
      _ = 1 := hyx
  have hfin : (Real.sqrt 3 + 1) * NU * y ≤ NU / Real.log x ^ A := by
    rw [le_div_iff₀ hlogA]
    have := mul_le_mul_of_nonneg_left hyl hNU
    nlinarith
  refine max_le ((Complex.re_le_norm Rnz).trans (hRn.trans hfin)) ?_
  exact div_nonneg hNU hlogA.le

end CleanNonzero
end ResearchBankV27
end Erdos287
