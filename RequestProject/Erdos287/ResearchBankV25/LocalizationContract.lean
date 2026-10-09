import RequestProject.Erdos287.ResearchBankV25.ExceptionalStateLocalization
import RequestProject.Erdos287.ResearchBankV25.CorrectionAggregation

/-!
# Erdős #287 — Research Bank V25 §3.4 (cont.): the localization contract

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

**LEAN BANK.**

* `locE`, `fullE` — localized energy `Σ_{u,a} |Δ_{α_u}(q,a)|²` and full energy
  `Σ_r |Δ_α(ℓ,r)|²` (zero at modulus `0`);
* `locE_le_fullE` — `locE(q) ≤ fullE(fq)` for `(f,q) = 1` (from §3.3);
* `weighted_localized_le_full` — the divisor-weighted reindexing
  `Σ_{q∈Qs} τ(q)^J locE(q) ≤ Σ_{ℓ≤fU} τ(ℓ)^J fullE(ℓ)`;
* **`loc_bound`** — `|Loc| ≤ √(Σ_{q∈Qs} τ(q)^J) · √(Σ_{ℓ≤fU} τ(ℓ)^J fullE(ℓ))` (centering bridge +
  single-residue ≤ energy + Cauchy–Schwarz + energy contraction + reindexing).

**EXTERNAL PROVIDER.**

* `BDHEnergyProvider` — the Barban–Davenport–Halberstam-type saving for the FULL-modulus energy
  of the ACTUAL source `γ` (never for `γ_u`).

**LEAN CONDITIONAL.**

* **`zero_frequency_localized_bound`** — `Full = Loc + C_f` with `Loc` bounded through the BDH
  provider and `C_f` through the masked SW provider:  for every `A`, eventually
  `|Full| ≤ √(Σ τ^J) √(C₁ B/log^A x) + C₂ M N/log^A x`.

**Firewall.**  `γ_u` is never assumed globally Siegel–Walfisz; only the full-modulus energy of `γ`
enters the provider.
-/

namespace Erdos287
namespace ResearchBankV25
namespace LocalizationContract

open Finset Complex FixedModulusCentering FixedResidueEnergy ExceptionalStateLocalization
open CorrectionAggregation

/-- Localized energy `Σ_{u ∈ G_f} Σ_{a ∈ G_q} |Δ_{α_u}(q,a)|²` (zero at `q = 0`). -/
noncomputable def locE (f : ℕ) [NeZero f] (Ns : Finset ℕ) (γ : ℕ → ℂ) (q : ℕ) : ℝ :=
  if h : q = 0 then 0 else
    haveI : NeZero q := ⟨h⟩
    ∑ u : (ZMod f)ˣ, ∑ a : (ZMod q)ˣ, normSq (Disc q Ns (alphaLoc γ u) a)

/-- Full energy `Σ_{r ∈ G_ℓ} |Δ_γ(ℓ,r)|²` (zero at `ℓ = 0`). -/
noncomputable def fullE (Ns : Finset ℕ) (γ : ℕ → ℂ) (l : ℕ) : ℝ :=
  if h : l = 0 then 0 else
    haveI : NeZero l := ⟨h⟩
    ∑ r : (ZMod l)ˣ, normSq (Disc l Ns γ r)

theorem fullE_nonneg (Ns : Finset ℕ) (γ : ℕ → ℂ) (l : ℕ) : 0 ≤ fullE Ns γ l := by
  unfold fullE; split_ifs
  · exact le_refl _
  · exact Finset.sum_nonneg fun _ _ => normSq_nonneg _

theorem locE_nonneg (f : ℕ) [NeZero f] (Ns : Finset ℕ) (γ : ℕ → ℂ) (q : ℕ) :
    0 ≤ locE f Ns γ q := by
  unfold locE; split_ifs
  · exact le_refl _
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => normSq_nonneg _

/-- **Localized energy ≤ full energy at `fq`** (LEAN BANK). -/
theorem locE_le_fullE {f q : ℕ} [NeZero f] (hq : q ≠ 0) (hfq : Nat.Coprime f q)
    (Ns : Finset ℕ) (γ : ℕ → ℂ) : locE f Ns γ q ≤ fullE Ns γ (f * q) := by
  haveI : NeZero q := ⟨hq⟩
  unfold locE fullE
  rw [dif_neg hq, dif_neg (Nat.mul_ne_zero (NeZero.ne f) hq)]
  exact localized_energy_le_full hfq Ns γ

/-- A single localized residue is bounded by the localized energy. -/
theorem single_le_locE {f q : ℕ} [NeZero f] (hq : q ≠ 0) (Ns : Finset ℕ) (γ : ℕ → ℂ)
    (u : (ZMod f)ˣ) (a : (ZMod q)ˣ) :
    normSq (Disc q Ns (alphaLoc γ u) a) ≤ locE f Ns γ q := by
  haveI : NeZero q := ⟨hq⟩
  unfold locE
  rw [dif_neg hq]
  calc normSq (Disc q Ns (alphaLoc γ u) a)
      ≤ ∑ a' : (ZMod q)ˣ, normSq (Disc q Ns (alphaLoc γ u) a') :=
        Finset.single_le_sum (f := fun a' : (ZMod q)ˣ => normSq (Disc q Ns (alphaLoc γ u) a'))
          (fun _ _ => normSq_nonneg _) (mem_univ a)
    _ ≤ ∑ u' : (ZMod f)ˣ, ∑ a' : (ZMod q)ˣ, normSq (Disc q Ns (alphaLoc γ u') a') :=
        Finset.single_le_sum (f := fun u' : (ZMod f)ˣ =>
          ∑ a' : (ZMod q)ˣ, normSq (Disc q Ns (alphaLoc γ u') a'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => normSq_nonneg _) (mem_univ u)

/-- `τ(q)^J`. -/
noncomputable def tauJ (J q : ℕ) : ℝ := ((q.divisors.card : ℝ)) ^ J

theorem tauJ_nonneg (J q : ℕ) : 0 ≤ tauJ J q := by unfold tauJ; positivity

/-- **Divisor-weighted localized energy ≤ full energy** (LEAN BANK). -/
theorem weighted_localized_le_full {f : ℕ} [NeZero f] (J U : ℕ) (Qs : Finset ℕ)
    (hQs : Qs ⊆ Finset.Icc 1 U) (hcop : ∀ q ∈ Qs, Nat.Coprime f q) (Ns : Finset ℕ)
    (γ : ℕ → ℂ) :
    ∑ q ∈ Qs, tauJ J q * locE f Ns γ q ≤
      ∑ l ∈ Finset.Icc 1 (f * U), tauJ J l * fullE Ns γ l := by
  classical
  set S : ℕ → ℝ := fun q => if Nat.Coprime f q then locE f Ns γ q else 0
  have hS : ∀ q, 0 ≤ S q := fun q => by
    simp only [S]; split_ifs
    · exact locE_nonneg f Ns γ q
    · exact le_refl _
  calc ∑ q ∈ Qs, tauJ J q * locE f Ns γ q = ∑ q ∈ Qs, tauJ J q * S q :=
        Finset.sum_congr rfl fun q hq => by simp only [S]; rw [if_pos (hcop q hq)]
    _ ≤ ∑ q ∈ Finset.Icc 1 U, tauJ J q * S q :=
        Finset.sum_le_sum_of_subset_of_nonneg hQs fun q _ _ =>
          mul_nonneg (tauJ_nonneg J q) (hS q)
    _ ≤ ∑ l ∈ Finset.Icc 1 (f * U), tauJ J l * fullE Ns γ l := by
        unfold tauJ
        refine divisor_reindexing f U J (Nat.pos_of_ne_zero (NeZero.ne f)) S (fullE Ns γ)
          (fun q hq => ?_) (fullE_nonneg Ns γ)
        simp only [S]
        split_ifs with h
        · exact locE_le_fullE (by omega) h Ns γ
        · exact fullE_nonneg Ns γ _

/-- Weighted Cauchy–Schwarz `Σ w √E ≤ √(Σ w) √(Σ w E)`. -/
theorem weighted_cauchy {ι : Type*} (s : Finset ι) (w E : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hE : ∀ i, 0 ≤ E i) :
    ∑ i ∈ s, w i * Real.sqrt (E i) ≤ Real.sqrt (∑ i ∈ s, w i) * Real.sqrt (∑ i ∈ s, w i * E i) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt s (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i) * Real.sqrt (E i))
  have e1 : ∀ i, Real.sqrt (w i) * (Real.sqrt (w i) * Real.sqrt (E i)) = w i * Real.sqrt (E i) :=
    fun i => by rw [← mul_assoc, Real.mul_self_sqrt (hw i)]
  have e2 : ∀ i, Real.sqrt (w i) ^ 2 = w i := fun i => Real.sq_sqrt (hw i)
  have e3 : ∀ i, (Real.sqrt (w i) * Real.sqrt (E i)) ^ 2 = w i * E i := fun i => by
    rw [mul_pow, Real.sq_sqrt (hw i), Real.sq_sqrt (hE i)]
  simp only [e1, e2, e3] at h
  exact h

/-- **Localized-sum bound** (LEAN BANK). -/
theorem loc_bound {f : ℕ} [NeZero f] {c : ℤ} (u0 : (ZMod f)ˣ) (hcu : (c : ZMod f) = u0)
    (J U : ℕ) (Qs : Finset ℕ) (hQs : Qs ⊆ Finset.Icc 1 U) (hcop : ∀ q ∈ Qs, Nat.Coprime f q)
    (aq : ℕ → ℤ) (haq : ∀ q ∈ Qs, IsUnit ((aq q : ℤ) : ZMod q)) (κ : ℕ → ℂ)
    (hκ : ∀ q, ‖κ q‖ ≤ tauJ J q) (Ns : Finset ℕ) (γ : ℕ → ℂ) :
    ‖LocSum f c Qs κ aq Ns γ‖ ≤
      Real.sqrt (∑ q ∈ Qs, tauJ J q) *
        Real.sqrt (∑ l ∈ Finset.Icc 1 (f * U), tauJ J l * fullE Ns γ l) := by
  have hq0 : ∀ q ∈ Qs, q ≠ 0 := fun q hq => by
    have := (Finset.mem_Icc.1 (hQs hq)).1; omega
  have step : ∀ q ∈ Qs, ‖κ q * ∑ n ∈ Ns, γ n * ((indMod f c n * delta q (aq q) n : ℝ) : ℂ)‖ ≤
      tauJ J q * Real.sqrt (locE f Ns γ q) := by
    intro q hq
    rw [norm_mul, sum_localized_delta_eq_Disc q c (aq q) u0 hcu Ns γ]
    refine mul_le_mul (hκ q) ?_ (norm_nonneg _) (tauJ_nonneg J q)
    obtain ⟨au, hau⟩ := haq q hq
    rw [← hau, Complex.norm_def]
    exact Real.sqrt_le_sqrt (single_le_locE (hq0 q hq) Ns γ u0 au)
  calc ‖LocSum f c Qs κ aq Ns γ‖
      ≤ ∑ q ∈ Qs, tauJ J q * Real.sqrt (locE f Ns γ q) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum step)
    _ ≤ Real.sqrt (∑ q ∈ Qs, tauJ J q) * Real.sqrt (∑ q ∈ Qs, tauJ J q * locE f Ns γ q) :=
        weighted_cauchy Qs _ _ (tauJ_nonneg J) (locE_nonneg f Ns γ)
    _ ≤ _ := by
        gcongr
        exact weighted_localized_le_full J U Qs hQs hcop Ns γ

/-- **BDH-type full-modulus energy provider** (EXTERNAL PROVIDER; never constructed): the
divisor-weighted full-modulus energy of the ACTUAL source `γ x` up to level `f · U x` saves
every power of `log x`. -/
structure BDHEnergyProvider (f J : ℕ) (Ns : ℝ → Finset ℕ) (γ : ℝ → ℕ → ℂ) (U : ℝ → ℕ)
    (Bnd : ℝ → ℝ) : Prop where
  saving : ∀ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ x0 : ℝ, ∀ x ≥ x0,
    ∑ l ∈ Finset.Icc 1 (f * U x), tauJ J l * fullE (Ns x) (γ x) l ≤ C * Bnd x / Real.log x ^ A

/-- Scale-indexed zero-frequency data at the fixed exceptional state `(f, c)`. -/
structure ZeroFreqData (f : ℕ) [NeZero f] (c : ℤ) (J : ℕ) where
  u0 : (ZMod f)ˣ
  hcu : (c : ZMod f) = u0
  Qs : ℝ → Finset ℕ
  U : ℝ → ℕ
  hQs : ∀ x, Qs x ⊆ Finset.Icc 1 (U x)
  hcop : ∀ x, ∀ q ∈ Qs x, Nat.Coprime f q
  aq : ℝ → ℕ → ℤ
  rq : ℝ → ℕ → ℤ
  haq : ∀ x, ∀ q ∈ Qs x, IsUnit ((aq x q : ℤ) : ZMod q)
  hrq : ∀ x, ∀ q ∈ Qs x, rq x q ≡ c [ZMOD (f : ℤ)] ∧ rq x q ≡ aq x q [ZMOD (q : ℤ)]
  κ : ℝ → ℕ → ℂ
  hκ : ∀ x q, ‖κ x q‖ ≤ tauJ J q
  Ns : ℝ → Finset ℕ
  γ : ℝ → ℕ → ℂ

/-- **Zero-frequency localized bound** (LEAN CONDITIONAL on `BDHEnergyProvider` and
`MaskedSWProvider`).  The full-modulus centred sum at the fixed exceptional modulus splits
exactly (`full_eq_loc_add_corr`); the localized part is controlled by the full-modulus energy of
the actual source, the correction by the masked SW saving. -/
theorem zero_frequency_localized_bound {f : ℕ} [NeZero f] {c : ℤ} {J : ℕ}
    (Z : ZeroFreqData f c J) {Bnd MN : ℝ → ℝ}
    (hB : BDHEnergyProvider f J Z.Ns Z.γ Z.U Bnd)
    (hM : MaskedSWProvider f c J Z.Qs Z.Ns Z.γ MN) :
    ∀ A : ℕ, ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∃ x0 : ℝ, ∀ x ≥ x0,
      ‖FullSum f (Z.Qs x) (Z.κ x) (Z.rq x) (Z.Ns x) (Z.γ x)‖ ≤
        Real.sqrt (∑ q ∈ Z.Qs x, tauJ J q) * Real.sqrt (C₁ * Bnd x / Real.log x ^ A) +
          C₂ * MN x / Real.log x ^ A := by
  intro A
  obtain ⟨C₁, hC₁, x1, hx1⟩ := hB.saving A
  obtain ⟨C₂, hC₂, x2, hx2⟩ := correction_aggregation_conditional hM Z.κ Z.hκ A
  refine ⟨C₁, C₂, hC₁, hC₂, max x1 x2, fun x hx => ?_⟩
  rw [full_eq_loc_add_corr (aq := Z.aq x) (Z.κ x) (Z.Ns x) (Z.γ x)
    (fun q hq => ⟨Z.hcop x q hq, Z.hrq x q hq⟩)]
  refine (norm_add_le _ _).trans (add_le_add ?_ (hx2 x (le_of_max_le_right hx)))
  refine (loc_bound Z.u0 Z.hcu J (Z.U x) (Z.Qs x) (Z.hQs x) (Z.hcop x) (Z.aq x) (Z.haq x) (Z.κ x)
    (Z.hκ x) (Z.Ns x) (Z.γ x)).trans ?_
  gcongr
  exact hx1 x (le_of_max_le_left hx)

end LocalizationContract
end ResearchBankV25
end Erdos287
