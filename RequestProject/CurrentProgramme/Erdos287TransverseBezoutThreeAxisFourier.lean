import Mathlib
import RequestProject.CurrentProgramme.Erdos287TransverseBezoutRowAffine

/-!
# Bézout three-axis frequency map and finite Fourier bound — Erdős #287 (append-only)

This module is **append-only**.  It adds:

* the abstract three-axis frequency map `f_g(ℓ,q) = γ_g(ℓ) · q⁻¹ (mod M_g)`, `M_g = m r₀`;
* its two exact fibre implications (one residue class in `q` mod `m`, one residue class in `ℓ`
  mod `r₀`), each under an **explicit** unit hypothesis;
* the exact finite fibre count `#f_g⁻¹(v) ≤ (⌊H₀/r₀⌋+1)(⌊Q/m⌋+1)` in `ℕ`-division form;
* a general finite `L²` Fourier inequality for a **fully coupled** coefficient `b_{ℓ,q}`,
  obtained by aggregating the `(ℓ,q)`-axis along `f_g` and reusing the already-banked finite
  Fourier Gram machinery (no new Fourier proof);
* the exact eight-term contraction identity of the research note, as an identity between
  positive reals only;
* the all-`q` atomic **grouped** compiler, whose product-energy input is an explicit hypothesis.

Nothing here asserts a saving, an asymptotic source length, or closure of any branch.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace TransverseBezoutThreeAxis

open Erdos287.ReciprocalUnitaryFourier
open Erdos287.BalancedBUnitaryFourier
open Erdos287.TransverseBezoutRow

/-! ## §1  General fibre aggregation -/

/-- Aggregation of a coefficient vector along the fibres of an arbitrary frequency map. -/
noncomputable def fiberAggregate {ι : Type*} {x : ℕ} (s : Finset ι) (F : ι → ZMod x)
    (b : ι → ℂ) (v : ZMod x) : ℂ :=
  ∑ i ∈ s.filter (fun i => F i = v), b i

/-- **`fiberAggregate_l2_le_maxFiber`.**  `LEAN_PROVED`.  If every fibre of `F` inside `s` has at
most `K` elements, then the aggregated vector has `ℓ²` mass at most `K` times the original. -/
theorem fiberAggregate_l2_le_maxFiber {ι : Type*} {x : ℕ} [NeZero x] (s : Finset ι)
    (F : ι → ZMod x) (b : ι → ℂ) (K : ℝ)
    (hK : ∀ v : ZMod x, ((s.filter (fun i => F i = v)).card : ℝ) ≤ K) :
    ∑ v : ZMod x, ‖fiberAggregate s F b v‖ ^ 2 ≤ K * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  classical
  have step : ∀ v : ZMod x, ‖fiberAggregate s F b v‖ ^ 2
      ≤ K * ∑ i ∈ s.filter (fun i => F i = v), ‖b i‖ ^ 2 := by
    intro v
    refine (norm_sum_sq_le_card _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hK v) (Finset.sum_nonneg fun _ _ => by positivity)
  calc ∑ v : ZMod x, ‖fiberAggregate s F b v‖ ^ 2
      ≤ ∑ v : ZMod x, K * ∑ i ∈ s.filter (fun i => F i = v), ‖b i‖ ^ 2 :=
        Finset.sum_le_sum fun v _ => step v
    _ = K * ∑ i ∈ s, ‖b i‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_fiberwise s F]

/-- **`fiberAggregate_sum`.**  `LEAN_PROVED`.  Exact regrouping of a phase sum along the fibres
of `F`: the phase depends on the index only through `F`. -/
theorem fiberAggregate_sum {ι : Type*} {x : ℕ} [NeZero x] (s : Finset ι) (F : ι → ZMod x)
    (b : ι → ℂ) (g : ZMod x → ℂ) :
    ∑ i ∈ s, b i * g (F i) = ∑ v : ZMod x, fiberAggregate s F b v * g v := by
  classical
  have : ∀ v : ZMod x, fiberAggregate s F b v * g v
      = ∑ i ∈ s.filter (fun i => F i = v), b i * g (F i) := by
    intro v
    rw [fiberAggregate, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp only [Finset.mem_filter] at hi
    rw [hi.2]
  rw [Finset.sum_congr rfl (fun v _ => this v)]
  exact (Finset.sum_fiberwise s F (fun i => b i * g (F i))).symm

/-! ## §2  The abstract three-axis finite Fourier inequality -/

/-- **`aggregatedFourier_bilinear_bound`.**  `LEAN_PROVED`.  Finite `L²` bound for a bilinear form
whose second axis is an arbitrary finite index set carrying a **fully coupled** coefficient
`b i`, coupled to the first axis only through an arbitrary frequency map `F`:

`‖∑_Δ ∑_i a_Δ b_i e_x(Δ F(i))‖² ≤ x (∑_Δ ‖a_Δ‖²) (K ∑_i ‖b_i‖²)`,

where `K` bounds the fibres of `F`.  Proof: fibre aggregation plus the already-banked Fourier
Gram identity.  No new Fourier proof. -/
theorem aggregatedFourier_bilinear_bound {ι : Type*} {x : ℕ} [NeZero x] (s : Finset ι)
    (F : ι → ZMod x) (a : ZMod x → ℂ) (b : ι → ℂ) (K : ℝ)
    (hK : ∀ v : ZMod x, ((s.filter (fun i => F i = v)).card : ℝ) ≤ K) :
    ‖∑ D : ZMod x, ∑ i ∈ s, a D * b i * ZMod.stdAddChar (D * F i)‖ ^ 2
      ≤ (x : ℝ) * (∑ D : ZMod x, ‖a D‖ ^ 2) * (K * ∑ i ∈ s, ‖b i‖ ^ 2) := by
  classical
  set B : ZMod x → ℂ := fun v => fiberAggregate s F b v with hB
  have hrw : ∑ D : ZMod x, ∑ i ∈ s, a D * b i * ZMod.stdAddChar (D * F i)
      = ∑ D : ZMod x, ∑ v : ZMod x, a D * B v * unitaryFourierKernel (1 : ZMod x) D v := by
    refine Finset.sum_congr rfl ?_
    intro D _
    have h1 : ∑ i ∈ s, a D * b i * ZMod.stdAddChar (D * F i)
        = a D * ∑ i ∈ s, b i * ZMod.stdAddChar (D * F i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : ∑ i ∈ s, b i * ZMod.stdAddChar (D * F i)
        = ∑ v : ZMod x, B v * ZMod.stdAddChar (D * v) :=
      fiberAggregate_sum s F b (fun v => ZMod.stdAddChar (D * v))
    rw [h1, h2, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro v _
    simp [unitaryFourierKernel]
    ring
  rw [hrw]
  refine (unitaryFourier_bilinear_bound (x := x) isUnit_one a B).trans ?_
  have hK' : ∑ v : ZMod x, ‖B v‖ ^ 2 ≤ K * ∑ i ∈ s, ‖b i‖ ^ 2 :=
    fiberAggregate_l2_le_maxFiber s F b K hK
  have hnn : (0 : ℝ) ≤ (x : ℝ) * ∑ D : ZMod x, ‖a D‖ ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left hK' hnn

/-! ## §3  The three-axis frequency map -/

variable (D : BezoutRowData)

/-- The three-axis frequency map `f_g(ℓ,q) = γ_g(ℓ) · q⁻¹` in `ZMod M_g`, `M_g = m r₀`. -/
noncomputable def fG (ell : ℤ) (q : ℕ) : ZMod D.Mg :=
  ((D.gammaG ell : ℤ) : ZMod D.Mg) * ((q : ℕ) : ZMod D.Mg)⁻¹

/-- **`fG_mul_q`.**  `LEAN_PROVED`.  Inverse-free form of the frequency equation: if `q` is a
unit modulo `M_g` and `f_g(ℓ,q) = v`, then `v q = γ_g(ℓ)` in `ZMod M_g`. -/
theorem fG_mul_q {ell : ℤ} {q : ℕ} (hq : IsUnit ((q : ℕ) : ZMod D.Mg)) {v : ZMod D.Mg}
    (h : fG D ell q = v) : v * ((q : ℕ) : ZMod D.Mg) = ((D.gammaG ell : ℤ) : ZMod D.Mg) := by
  rw [← h, fG]
  calc ((D.gammaG ell : ℤ) : ZMod D.Mg) * ((q : ℕ) : ZMod D.Mg)⁻¹ * ((q : ℕ) : ZMod D.Mg)
      = ((D.gammaG ell : ℤ) : ZMod D.Mg) *
          (((q : ℕ) : ZMod D.Mg)⁻¹ * ((q : ℕ) : ZMod D.Mg)) := by ring
    _ = ((D.gammaG ell : ℤ) : ZMod D.Mg) := by
        rw [ZMod.inv_mul_of_unit _ hq, mul_one]

/-- **`fG_fibre_q_congr`.**  `LEAN_PROVED`.  First fibre implication, in integer form.  If two
pairs have the same frequency `v`, and `v` (viewed mod `m`) is invertible, then their
`q`-coordinates are congruent modulo `m`: the `q`-fibre lies in one residue class mod `m`.

The unit hypothesis on `v` is explicit; nothing claims it holds for the physical source. -/
theorem fG_fibre_q_congr {ell ell' : ℤ} {q q' : ℕ} {v : ZMod D.Mg}
    (hq : IsUnit ((q : ℕ) : ZMod D.Mg)) (hq' : IsUnit ((q' : ℕ) : ZMod D.Mg))
    (h : fG D ell q = v) (h' : fG D ell' q' = v)
    {vm : ℤ} (hvm : ((vm : ℤ) : ZMod D.Mg) = v) {w : ℤ}
    (hw : vm * w ≡ 1 [ZMOD (D.m : ℤ)]) :
    (q : ℤ) ≡ (q' : ℤ) [ZMOD (D.m : ℤ)] := by
  have e1 : v * ((q : ℕ) : ZMod D.Mg) = ((D.gammaG ell : ℤ) : ZMod D.Mg) := fG_mul_q D hq h
  have e2 : v * ((q' : ℕ) : ZMod D.Mg) = ((D.gammaG ell' : ℤ) : ZMod D.Mg) := fG_mul_q D hq' h'
  -- transfer the two equations to integer congruences modulo `M_g`, then modulo `m`
  have hdvd : (D.m : ℤ) ∣ (D.Mg : ℤ) := ⟨(D.r0 : ℤ), by simp [BezoutRowData.Mg]⟩
  have i1 : vm * (q : ℤ) ≡ D.gammaG ell [ZMOD (D.Mg : ℤ)] := by
    have : ((vm * (q : ℤ) : ℤ) : ZMod D.Mg) = ((D.gammaG ell : ℤ) : ZMod D.Mg) := by
      push_cast
      rw [hvm]
      exact_mod_cast e1
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mp this
  have i2 : vm * (q' : ℤ) ≡ D.gammaG ell' [ZMOD (D.Mg : ℤ)] := by
    have : ((vm * (q' : ℤ) : ℤ) : ZMod D.Mg) = ((D.gammaG ell' : ℤ) : ZMod D.Mg) := by
      push_cast
      rw [hvm]
      exact_mod_cast e2
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mp this
  have j1 : vm * (q : ℤ) ≡ D.gammaG ell [ZMOD (D.m : ℤ)] := Int.ModEq.of_dvd hdvd i1
  have j2 : vm * (q' : ℤ) ≡ D.gammaG ell' [ZMOD (D.m : ℤ)] := Int.ModEq.of_dvd hdvd i2
  have k1 : D.gammaG ell ≡ D.cM [ZMOD (D.m : ℤ)] := D.gammaG_mod_m ell
  have k2 : D.gammaG ell' ≡ D.cM [ZMOD (D.m : ℤ)] := D.gammaG_mod_m ell'
  have key : vm * (q : ℤ) ≡ vm * (q' : ℤ) [ZMOD (D.m : ℤ)] :=
    ((j1.trans k1).trans (j2.trans k2).symm)
  -- cancel the unit `vm`
  have hcancel : (0 : ℤ) + vm * (q : ℤ) ≡ 0 + vm * (q' : ℤ) [ZMOD (D.m : ℤ)] := by simpa using key
  exact affine_residue_unique_of_unit_slope hw hcancel

/-- **`fG_fibre_ell_congr`.**  `LEAN_PROVED`.  Second fibre implication: for a **fixed**
`q`-coordinate, the `ℓ`-fibre lies in one residue class modulo `r₀`, provided the affine slope
`A_m` is invertible modulo `r₀` (witness supplied). -/
theorem fG_fibre_ell_congr {ell ell' : ℤ} {q : ℕ} {v : ZMod D.Mg}
    (hq : IsUnit ((q : ℕ) : ZMod D.Mg))
    (h : fG D ell q = v) (h' : fG D ell' q = v)
    {w : ℤ} (hw : D.A_m * w ≡ 1 [ZMOD (D.r0 : ℤ)]) :
    ell ≡ ell' [ZMOD (D.r0 : ℤ)] := by
  have e1 : v * ((q : ℕ) : ZMod D.Mg) = ((D.gammaG ell : ℤ) : ZMod D.Mg) := fG_mul_q D hq h
  have e2 : v * ((q : ℕ) : ZMod D.Mg) = ((D.gammaG ell' : ℤ) : ZMod D.Mg) := fG_mul_q D hq h'
  have heq : ((D.gammaG ell : ℤ) : ZMod D.Mg) = ((D.gammaG ell' : ℤ) : ZMod D.Mg) := by
    rw [← e1, ← e2]
  have hcong : D.gammaG ell ≡ D.gammaG ell' [ZMOD (D.Mg : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mp heq
  have hdvd : (D.r0 : ℤ) ∣ (D.Mg : ℤ) := ⟨(D.m : ℤ), by simp [BezoutRowData.Mg]; ring⟩
  have hr : D.gammaG ell ≡ D.gammaG ell' [ZMOD (D.r0 : ℤ)] := Int.ModEq.of_dvd hdvd hcong
  have h1 : D.dEll ell ≡ D.dEll ell' [ZMOD (D.r0 : ℤ)] :=
    ((D.gammaG_mod_r0 ell).symm.trans hr).trans (D.gammaG_mod_r0 ell')
  exact gammaG_affine_injective_mod_r0 D hw h1

/-! ## §4  The interval fibre count -/

/-- **`box_fibre_card_le`.**  `LEAN_PROVED`.  Abstract exact fibre count over a rectangular box
of integer intervals.  If, inside the fibre of `v`, the second coordinate is confined to one
residue class mod `m` and — for each fixed second coordinate — the first coordinate is confined
to one residue class mod `r₀`, then

`#fibre ≤ (H₀ / r₀ + 1) · (Q / m + 1)`

in exact `ℕ`-division form. -/
theorem box_fibre_card_le {x : ℕ} {m r0 : ℕ} (hm : 0 < m) (hr0 : 0 < r0)
    (aE H0 aQ Q : ℕ) (F : ℕ × ℕ → ZMod x) (v : ZMod x)
    (hq : ∀ p ∈ (Finset.Ico aE (aE + H0)) ×ˢ (Finset.Ico aQ (aQ + Q)),
      ∀ p' ∈ (Finset.Ico aE (aE + H0)) ×ˢ (Finset.Ico aQ (aQ + Q)),
      F p = v → F p' = v → ((p.2 : ℕ) : ZMod m) = ((p'.2 : ℕ) : ZMod m))
    (hell : ∀ p ∈ (Finset.Ico aE (aE + H0)) ×ˢ (Finset.Ico aQ (aQ + Q)),
      ∀ p' ∈ (Finset.Ico aE (aE + H0)) ×ˢ (Finset.Ico aQ (aQ + Q)),
      F p = v → F p' = v → p.2 = p'.2 → ((p.1 : ℕ) : ZMod r0) = ((p'.1 : ℕ) : ZMod r0)) :
    ((((Finset.Ico aE (aE + H0)) ×ˢ (Finset.Ico aQ (aQ + Q))).filter
      (fun p => F p = v)).card : ℕ) ≤ (H0 / r0 + 1) * (Q / m + 1) := by
  classical
  set box := (Finset.Ico aE (aE + H0)) ×ˢ (Finset.Ico aQ (aQ + Q)) with hbox
  set S := box.filter (fun p => F p = v) with hSdef
  -- each `q`-fibre of `S` has at most `H₀ / r₀ + 1` points
  have hfib : ∀ c ∈ S.image Prod.snd, (S.filter (fun p => p.2 = c)).card ≤ H0 / r0 + 1 := by
    intro c _
    rcases Finset.eq_empty_or_nonempty (S.filter (fun p => p.2 = c)) with he | ⟨p₀, hp₀⟩
    · simp [he]
    · have hmap : ((S.filter (fun p => p.2 = c)).image Prod.fst) ⊆
          (Finset.Ico aE (aE + H0)).filter
            (fun e : ℕ => ((e : ℕ) : ZMod r0) = ((p₀.1 : ℕ) : ZMod r0)) := by
        intro e he
        simp only [Finset.mem_image] at he
        obtain ⟨p, hp, rfl⟩ := he
        simp only [Finset.mem_filter, hSdef, hbox, Finset.mem_product] at hp hp₀
        simp only [Finset.mem_filter]
        refine ⟨hp.1.1.1, ?_⟩
        refine hell p ?_ p₀ ?_ hp.1.2 hp₀.1.2 (by rw [hp.2, hp₀.2])
        · simp only [hbox, Finset.mem_product]; exact hp.1.1
        · simp only [hbox, Finset.mem_product]; exact hp₀.1.1
      have hinj : Set.InjOn Prod.fst ((S.filter (fun p => p.2 = c)) : Set (ℕ × ℕ)) := by
        intro p hp p' hp' hpp
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hp'
        exact Prod.ext hpp (by rw [hp.2, hp'.2])
      calc (S.filter (fun p => p.2 = c)).card
          = ((S.filter (fun p => p.2 = c)).image Prod.fst).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ ((Finset.Ico aE (aE + H0)).filter
              (fun e : ℕ => ((e : ℕ) : ZMod r0) = ((p₀.1 : ℕ) : ZMod r0))).card :=
            Finset.card_le_card hmap
        _ ≤ H0 / r0 + 1 := interval_residue_fibre_card_le r0 hr0 aE H0 _
  -- the set of `q`-values met by `S` lies in one residue class mod `m`
  have himg : (S.image Prod.snd).card ≤ Q / m + 1 := by
    rcases Finset.eq_empty_or_nonempty S with he | ⟨p₀, hp₀⟩
    · simp [he]
    · have hsub : S.image Prod.snd ⊆ (Finset.Ico aQ (aQ + Q)).filter
          (fun q : ℕ => ((q : ℕ) : ZMod m) = ((p₀.2 : ℕ) : ZMod m)) := by
        intro q hq'
        simp only [Finset.mem_image] at hq'
        obtain ⟨p, hp, rfl⟩ := hq'
        simp only [Finset.mem_filter, hSdef, hbox, Finset.mem_product] at hp hp₀
        simp only [Finset.mem_filter]
        refine ⟨hp.1.2, ?_⟩
        refine hq p ?_ p₀ ?_ hp.2 hp₀.2
        · simp only [hbox, Finset.mem_product]; exact hp.1
        · simp only [hbox, Finset.mem_product]; exact hp₀.1
      exact le_trans (Finset.card_le_card hsub)
        (interval_residue_fibre_card_le m hm aQ Q _)
  have := Finset.card_le_mul_card_image (f := Prod.snd) S (H0 / r0 + 1) hfib
  exact this.trans (Nat.mul_le_mul_left _ himg)

/-! ## §5  The three-axis finite Fourier theorem -/

/-- **`bezoutRowThreeAxisFourier_bound`.**  `LEAN_PROVED`.  The Bézout three-axis finite Fourier
inequality.  The `Δ`-axis is aggregated by residue mod `M_g`; the `(ℓ,q)`-axis carries an
arbitrary **fully coupled** coefficient and is aggregated along `f_g`; `K` is any explicit bound
for the fibres of `f_g`.  Conclusion:

`‖∑_Δ ∑_{(ℓ,q)} a_Δ b_{ℓ,q} e_{M_g}(Δ f_g(ℓ,q))‖² ≤ M_g (∑_Δ ‖a_Δ‖²) (K ∑ ‖b‖²)`.

This is the banked Fourier Gram machinery applied to the three-axis map; no asymptotic
source-length claim is made. -/
theorem bezoutRowThreeAxisFourier_bound [NeZero D.Mg] (s : Finset (ℤ × ℕ))
    (a : ZMod D.Mg → ℂ) (b : ℤ × ℕ → ℂ) (K : ℝ)
    (hK : ∀ v : ZMod D.Mg,
      ((s.filter (fun p => fG D p.1 p.2 = v)).card : ℝ) ≤ K) :
    ‖∑ Δ : ZMod D.Mg, ∑ p ∈ s,
        a Δ * b p * ZMod.stdAddChar (Δ * fG D p.1 p.2)‖ ^ 2
      ≤ (D.Mg : ℝ) * (∑ Δ : ZMod D.Mg, ‖a Δ‖ ^ 2) * (K * ∑ p ∈ s, ‖b p‖ ^ 2) :=
  aggregatedFourier_bilinear_bound s (fun p => fG D p.1 p.2) a b K hK

/-! ## §6  The exact eight-term contraction identity -/

/-- **`bezoutThreeAxis_contraction_identity`.**  `LEAN_PROVED`.  The exact algebraic expansion
behind the research contraction, for positive real parameters and with the source relations
`M_g = m r₀`, `r = g r₀`, `H = g H₀`:

`M_g (1 + D₀/M_g)(1 + H₀/r₀)(1 + Q/m) / (D₀ H₀ Q)
   = M_g/(D₀H₀Q) + g/(HQ) + r/(D₀H) + m/(D₀Q) + g/(mH) + g/(rQ) + 1/D₀ + g/(mr)`.

This is an identity, **not** a saving: nothing asserts that the physical parameters make the
right-hand side small. -/
theorem bezoutThreeAxis_contraction_identity (Mg m r0 g r H H0 D0 Q : ℝ)
    (hm : 0 < m) (hr0 : 0 < r0) (hg : 0 < g) (hH0 : 0 < H0) (hD0 : 0 < D0) (hQ : 0 < Q)
    (hMg : Mg = m * r0) (hr : r = g * r0) (hH : H = g * H0) :
    Mg * (1 + D0 / Mg) * (1 + H0 / r0) * (1 + Q / m) / (D0 * H0 * Q)
      = Mg / (D0 * H0 * Q) + g / (H * Q) + r / (D0 * H) + m / (D0 * Q)
        + g / (m * H) + g / (r * Q) + 1 / D0 + g / (m * r) := by
  subst hMg; subst hr; subst hH
  field_simp
  ring

/-! ## §7  All-`q` atomic grouping: conditional compiler -/

/-- Explicit product-energy interface for the **grouped** `q`-coordinate
`q = 2° · E° · R · B°`, treated as a single `L²`-controlled source coordinate.

This is a hypothesis, never discharged here. -/
def GroupedQEnergyHypothesis (sQ : Finset (ℤ × ℕ)) (b : ℤ × ℕ → ℂ)
    (s2 sE sR sB : Finset ℕ) (c2 cE cR cB : ℕ → ℂ) (Kgrp : ℝ) : Prop :=
  ∑ p ∈ sQ, ‖b p‖ ^ 2 ≤ Kgrp * (∑ i ∈ s2, ‖c2 i‖ ^ 2) * (∑ i ∈ sE, ‖cE i‖ ^ 2) *
    (∑ i ∈ sR, ‖cR i‖ ^ 2) * (∑ i ∈ sB, ‖cB i‖ ^ 2)

/-- **`groupedQEnergy_not_automatic`.**  `LEAN_PROVED`.  The grouped product-energy interface is
a genuine hypothesis: there are data for which it fails, so no theorem carrying it is vacuous. -/
theorem groupedQEnergy_not_automatic :
    ∃ (sQ : Finset (ℤ × ℕ)) (b : ℤ × ℕ → ℂ) (s2 sE sR sB : Finset ℕ)
      (c2 cE cR cB : ℕ → ℂ) (Kgrp : ℝ),
      ¬ GroupedQEnergyHypothesis sQ b s2 sE sR sB c2 cE cR cB Kgrp := by
  refine ⟨{(0, 0)}, fun _ => 1, ∅, ∅, ∅, ∅, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, 1, ?_⟩
  intro h
  simp only [GroupedQEnergyHypothesis] at h
  norm_num at h

/-- **`transverseAllQAtomicGrouped_of_productEnergy`.**  `LEAN_PROVED (CONDITIONAL)`.

The all-`q` atomic **grouped** compiler.  The complete product `q = 2° E° R B°` is treated as one
source coordinate: given

* an explicit fibre bound `K` for the three-axis frequency map, and
* an explicit grouped product-energy hypothesis for the coupled coefficient `b`,

the three-axis finite Fourier inequality holds with the grouped energy substituted.  Both inputs
are explicit named hypotheses; no source packet is claimed to satisfy them. -/
theorem transverseAllQAtomicGrouped_of_productEnergy [NeZero D.Mg] (s : Finset (ℤ × ℕ))
    (a : ZMod D.Mg → ℂ) (b : ℤ × ℕ → ℂ) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ v : ZMod D.Mg, ((s.filter (fun p => fG D p.1 p.2 = v)).card : ℝ) ≤ K)
    (s2 sE sR sB : Finset ℕ) (c2 cE cR cB : ℕ → ℂ) (Kgrp : ℝ)
    (hgrp : GroupedQEnergyHypothesis s b s2 sE sR sB c2 cE cR cB Kgrp) :
    ‖∑ Δ : ZMod D.Mg, ∑ p ∈ s,
        a Δ * b p * ZMod.stdAddChar (Δ * fG D p.1 p.2)‖ ^ 2
      ≤ (D.Mg : ℝ) * (∑ Δ : ZMod D.Mg, ‖a Δ‖ ^ 2) *
          (K * (Kgrp * (∑ i ∈ s2, ‖c2 i‖ ^ 2) * (∑ i ∈ sE, ‖cE i‖ ^ 2) *
            (∑ i ∈ sR, ‖cR i‖ ^ 2) * (∑ i ∈ sB, ‖cB i‖ ^ 2))) := by
  refine (bezoutRowThreeAxisFourier_bound D s a b K hK).trans ?_
  have hnn : (0 : ℝ) ≤ (D.Mg : ℝ) * ∑ Δ : ZMod D.Mg, ‖a Δ‖ ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgrp hK0) hnn

end TransverseBezoutThreeAxis
end Erdos287
