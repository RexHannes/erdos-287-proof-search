import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilyActualAll
import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilySWLarge

/-!
# Erdős #287 — the actual Urem estimate with the residual analytic input in its final form

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

`actual_urem_paid`: `actual_urem_total` at the physical roughness threshold
`z₀ = physZ0 X = ⌊X^{1/(log log X)^3}⌋` (source §19), with the interval Siegel–Walfisz input
required **only for moduli `q ≤ (log N)^{A+1}`** (`IntervalSWSmall`) — the large moduli are
discharged by `intervalSW_of_small`.  The only remaining hypotheses are therefore:

1. `MaynardLemma13_8` — Maynard I, Lemma 13.8 (published; not formalized);
2. `IntervalSWSmall (roughOne z₀) N b cSW` and `IntervalSWSmall (roughMu z₀) N b cSW` at the scale
   `N = 2^{e_c} - 1/2` of each critical cell — small-modulus Siegel–Walfisz for the rough constant
   and rough Möbius function (paper proof in `ERDOS287_UREM_PAID_REPORT.md`: Rankin/fundamental
   lemma for `1_{P^-(n) ≥ z₀}`; Siegel–Walfisz for `μ` plus the identity `μ 1_{rough} = μ * 1_{smooth}`
   for the Möbius case; not formalized);
3. fixed source data (`k ≤ k₀`, tensor bound, slopes `≤ a_max`, support `δ_s` with `2δ_s < κ`,
   scalar level `K ≤ X`).
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII.UremFamily

open Erdos287.Physical Erdos287.Physical.TypeII Erdos287.Physical.Sieve
  Erdos287.Physical.Sieve.ScalarParams Erdos287.Physical.Factor

/-- **UREM, final form.**  For every `A > 0`: `∑_{cells} ∑_ξ |physUrem| ≤ C X/(log X)^A`, from
Maynard's Lemma 13.8 and small-modulus SW for the two rough base sequences at
`z₀ = X^{1/(log log X)^3}`. -/
theorem actual_urem_paid (hM : MaynardLemma13_8) (k₀ : ℕ) {b : ℕ} (hb : 2 * k₀ + 1 ≤ b)
    (cSW : ℝ → ℝ) (T : ℕ) {Astar κ δs amax CaMax : ℝ} (hA : 0 < Astar) (hκ0 : 0 < κ)
    (hδs : 0 ≤ δs) (hκδ : 2 * δs < κ) (hamax : 0 ≤ amax) :
    ∃ X0 Ctot : ℝ, ∀ (P : PhysData) (S : ScalarParams), X0 ≤ S.X → P.X = S.X →
    P.W = physW S.X → P.WGood → P.k ≤ k₀ → (∀ i, (P.a i : ℝ) ≤ amax) → FSupport P δs →
    ∀ (Bf : ℝ), (∀ v i t, |P.fp v i t| ≤ Bf) → (P.V * Bf ^ P.k) ^ 2 * (P.k : ℝ) ^ 2 ≤ CaMax →
    S.T = T → CritRegime S κ →
    ∀ (Ξ : Finset (Packet P.k)), Ξ ⊆ P.XiAll → ∀ (K K' : ℕ), (K : ℝ) ≤ S.X →
    ∀ (z E0 : ℕ), (2 : ℝ) ^ E0 ≤ S.X →
    ∀ 𝒞 : Finset (ℕ × (Fin 6 → ℕ) × Fin 6), 𝒞 ⊆ cellBox E0 → (∀ x ∈ 𝒞,
      CritCell S κ ((2 : ℝ) ^ x.2.1 x.2.2) ∧ (2 : ℝ) ^ (∑ i, x.2.1 i) ≤ S.X ∧
      4 * 2 ^ x.2.1 x.2.2 * 2 ^ betaTop x.2.1 x.2.2 ≤ K' ∧
      IntervalSWSmall (roughOne (physZ0 S.X)) (alphaScale x.2.1 x.2.2) b cSW ∧
      IntervalSWSmall (roughMu (physZ0 S.X)) (alphaScale x.2.1 x.2.2) b cSW) →
    ∑ x ∈ 𝒞, ∑ ξ ∈ Ξ, |physUrem S κ ((2 : ℝ) ^ x.2.1 x.2.2) (P.Gamma ξ) (P.f ξ) (P.cRes ξ)
        (P.A ξ) (P.B ξ) K K' (alphaSeq z (physZ0 S.X) x.1 x.2.1 x.2.2)
        (betaSeq z (physZ0 S.X) x.1 x.2.1 x.2.2)| ≤
      Ctot * S.X / Real.log S.X ^ Astar := by
  obtain ⟨X0, Ctot, hC⟩ := actual_urem_total hM k₀ hb
    (fun A => max (cSW A) (7 + 8 * A ^ A)) T (Astar := Astar) (CaMax := CaMax) hA hκ0 hδs hκδ
    hamax
  refine ⟨max X0 ((3 : ℝ) ^ (1 / (3 * κ))), Ctot, ?_⟩
  intro P S hX hPX hW hP hk ha hFs Bf hBf hCa hT hcr Ξ hΞ K K' hKX z E0 hE0 𝒞 h𝒞 hcells
  have hX0 : X0 ≤ S.X := le_trans (le_max_left _ _) hX
  have hX3 : (3 : ℝ) ^ (1 / (3 * κ)) ≤ S.X := le_trans (le_max_right _ _) hX
  have h3 : (3 : ℝ) ≤ S.X ^ (3 * κ) := by
    calc (3 : ℝ) = ((3 : ℝ) ^ (1 / (3 * κ))) ^ (3 * κ) := by
          rw [← Real.rpow_mul (by norm_num)]; field_simp; simp
      _ ≤ S.X ^ (3 * κ) := Real.rpow_le_rpow (by positivity) hX3 (by positivity)
  refine hC P S hX0 hPX hW hP hk ha hFs Bf hBf hCa hT hcr Ξ hΞ K K' hKX z (physZ0 S.X) E0 hE0 𝒞
    h𝒞 (fun x hx => ?_)
  obtain ⟨h1, h2, h3', h4, h5⟩ := hcells x hx
  have hN2 : 2 ≤ alphaScale x.2.1 x.2.2 := by
    unfold alphaScale
    have := h1.N_lo
    push_cast
    linarith
  exact ⟨h1, h2, h3', intervalSW_of_small (abs_roughOne_le _) hN2 (Nat.cast_nonneg b) h4,
    intervalSW_of_small (abs_roughMu_le _) hN2 (Nat.cast_nonneg b) h5⟩

end Erdos287.Physical.TypeII.UremFamily
