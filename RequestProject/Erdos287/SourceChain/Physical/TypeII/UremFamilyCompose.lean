import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilyCauchy

/-!
# Erdős #287 — the family Urem estimate reduced to a complete-modulus BDH energy

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Everything here is a finite, unconditional inequality.

* `packet_bound` — (5.3) in absolute-value form, with `|z_l| ≤ |Γ| W` and `∑_m β_m² ≤ Bβ`:
  `|Y_ξ| ≤ |Γ_ξ| W √Bβ √((M/f + L) R_r(f))`.
* `energy_grouping` — (4.2): grouping `q = f l`,
  `∑_f a_f R_r(f) ≤ C_a ∑_{q < 2FL} τ(q)^{K+1} ∑*_{b mod q} E(q,b)²` when `a_f ≤ C_a τ(f)^K`.
* `family_urem_le_bdhEnergy` — (5.4) + (4.2): for a packet family sharing one sequence `ρ`,
  `∑_ξ |Y_ξ| ≤ W √Bβ √(∑_ξ |Γ_ξ| (M/f_ξ + L)) √(C_a · bdhEnergy)`, where
  `bdhEnergy = ∑_{q < 2FL} τ(q)^{K+1} ∑*_{b mod q} E_ρ(q,b)²` is exactly the quantity bounded by a
  Barban–Davenport–Halberstam-type theorem (cf. Maynard I, Lemma 13.8).
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII.UremFamily

open Erdos287.Physical.TypeII

/-- The divisor function `τ(q)` as a real number. -/
noncomputable def tau (q : ℕ) : ℝ := (q.divisors.card : ℝ)

/-- The complete-modulus BDH energy with divisor weight `τ(q)^{K+1}`, moduli `q < Q`. -/
noncomputable def bdhEnergy (I : Finset ℕ) (ρ : ℕ → ℝ) (Q K : ℕ) : ℝ :=
  ∑ q ∈ range Q, tau q ^ (K + 1) * ∑ b ∈ units q, disc I ρ q b ^ 2

/-- The packet Urem block `Y` for one `r` and one dyadic band `[L, 2L)`. -/
noncomputable def uremBlock (I : Finset ℕ) (ρ : ℕ → ℝ) (f c A : ℕ) (B : ℤ) (L M r : ℕ)
    (z β : ℕ → ℝ) : ℝ :=
  ∑ l ∈ Ico L (2 * L), z l * ∑ m ∈ Ico M (2 * M), β m * copInd m (f * l * r) *
    relDisc I ρ f (cRes f c m) l (aRes l A B m)

/-- Weighted Cauchy–Schwarz. -/
lemma weighted_cauchy {ι : Type*} (s : Finset ι) (G u R : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i) (hR : ∀ i ∈ s, 0 ≤ R i) :
    ∑ i ∈ s, |G i| * Real.sqrt (u i * R i) ≤
      Real.sqrt (∑ i ∈ s, |G i| * u i) * Real.sqrt (∑ i ∈ s, |G i| * R i) := by
  have e : ∀ i ∈ s, |G i| * Real.sqrt (u i * R i) =
      Real.sqrt (|G i| * u i) * Real.sqrt (|G i| * R i) := by
    intro i hi
    rw [← Real.sqrt_mul (mul_nonneg (abs_nonneg _) (hu i hi))]
    have : |G i| * u i * (|G i| * R i) = |G i| ^ 2 * (u i * R i) := by ring
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]
  rw [sum_congr rfl e]
  refine (Real.sum_mul_le_sqrt_mul_sqrt s _ _).trans (le_of_eq ?_)
  congr 2
  · exact sum_congr rfl (fun i hi => Real.sq_sqrt (mul_nonneg (abs_nonneg _) (hu i hi)))
  · exact sum_congr rfl (fun i hi => Real.sq_sqrt (mul_nonneg (abs_nonneg _) (hR i hi)))

/-- **Per-packet bound** (5.3), absolute-value form. -/
theorem packet_bound (I : Finset ℕ) (ρ : ℕ → ℝ) {f c A L M r : ℕ} {B : ℤ}
    (hf : 0 < f) (hL : 0 < L) (hcf : Nat.Coprime c f) (z β : ℕ → ℝ)
    (hz : ∀ l, z l ≠ 0 → Nat.Coprime f l ∧ Nat.Coprime (A * B.natAbs) l)
    {Γ W Bβ : ℝ} (hW : 0 ≤ W) (hzW : ∀ l, |z l| ≤ |Γ| * W)
    (hβ : ∑ m ∈ Ico M (2 * M), β m ^ 2 ≤ Bβ) :
    |uremBlock I ρ f c A B L M r z β| ≤
      |Γ| * W * Real.sqrt Bβ * Real.sqrt (((M : ℝ) / f + L) * relEnergy I ρ f L) := by
  have hsq := urem_r_sq_le_relative_energy I ρ (A := A) (B := B) (M := M) (r := r) hf hL hcf
    z β hz
  have hΓW : 0 ≤ |Γ| * W := mul_nonneg (abs_nonneg _) hW
  have hz2 : ∑ l ∈ Ico L (2 * L), z l ^ 2 ≤ L * (|Γ| * W) ^ 2 := by
    calc ∑ l ∈ Ico L (2 * L), z l ^ 2 ≤ ∑ l ∈ Ico L (2 * L), (|Γ| * W) ^ 2 := by
          refine sum_le_sum (fun l _ => ?_)
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hzW l) 2
      _ = L * (|Γ| * W) ^ 2 := by
          rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
          congr 1
          rw [show 2 * L - L = L by omega]
  have hR := relEnergy_nonneg I ρ f L
  have hBβ : 0 ≤ Bβ := le_trans (sum_nonneg (fun _ _ => sq_nonneg _)) hβ
  have hfpos : (0 : ℝ) < f := by exact_mod_cast hf
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hb0 : 0 ≤ |Γ| * W * Real.sqrt Bβ * Real.sqrt (((M : ℝ) / f + L) * relEnergy I ρ f L) := by
    positivity
  rw [← sq_le_sq₀ (abs_nonneg _) hb0, sq_abs]
  rw [mul_pow, mul_pow, Real.sq_sqrt hBβ, Real.sq_sqrt (by positivity)]
  unfold uremBlock
  refine hsq.trans ?_
  have e : ((M : ℝ) / (f * L) + 1) * L = (M / f + L) := by field_simp
  have hβ0 : 0 ≤ ∑ m ∈ Ico M (2 * M), β m ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hq : 0 ≤ (M : ℝ) / (f * L) + 1 := by positivity
  calc (∑ l ∈ Ico L (2 * L), z l ^ 2) * (∑ m ∈ Ico M (2 * M), β m ^ 2) *
        ((M : ℝ) / (f * L) + 1) * relEnergy I ρ f L
      ≤ (L * (|Γ| * W) ^ 2) * Bβ * ((M : ℝ) / (f * L) + 1) * relEnergy I ρ f L := by
        gcongr
    _ = _ := by rw [← e]; ring

/-- **(4.2) Grouping of moduli** `q = f l`. -/
theorem energy_grouping (I : Finset ℕ) (ρ : ℕ → ℝ) (Fs : Finset ℕ) {F L K : ℕ}
    (hFs : ∀ f ∈ Fs, 0 < f ∧ f ≤ F) (hL : 0 < L) (a : ℕ → ℝ)
    {Ca : ℝ} (hCa : 0 ≤ Ca) (ha : ∀ f ∈ Fs, a f ≤ Ca * tau f ^ K) :
    ∑ f ∈ Fs, a f * relEnergy I ρ f L ≤ Ca * bdhEnergy I ρ (2 * F * L) K := by
  set D : ℕ → ℝ := fun q => ∑ b ∈ units q, disc I ρ q b ^ 2 with hD
  have hD0 : ∀ q, 0 ≤ D q := fun q => sum_nonneg (fun _ _ => sq_nonneg _)
  have htau0 : ∀ q, 0 ≤ tau q := fun q => Nat.cast_nonneg _
  set P := (Fs ×ˢ Ico L (2 * L)).filter (fun p => Nat.Coprime p.1 p.2) with hP
  have s1 : ∀ f ∈ Fs, a f * relEnergy I ρ f L ≤
      Ca * ∑ l ∈ (Ico L (2 * L)).filter (Nat.Coprime f), tau f ^ K * D (f * l) := by
    intro f hf
    have hR : relEnergy I ρ f L ≤ ∑ l ∈ (Ico L (2 * L)).filter (Nat.Coprime f), D (f * l) := by
      unfold relEnergy
      refine sum_le_sum (fun l hl => ?_)
      rw [mem_filter, mem_Ico] at hl
      exact relDisc_energy_le I ρ hl.2 (hFs f hf).1 (by omega)
    calc a f * relEnergy I ρ f L
        ≤ (Ca * tau f ^ K) * ∑ l ∈ (Ico L (2 * L)).filter (Nat.Coprime f), D (f * l) :=
          mul_le_mul (ha f hf) hR (relEnergy_nonneg _ _ _ _)
            (mul_nonneg hCa (pow_nonneg (htau0 _) _))
      _ = _ := by rw [mul_assoc, mul_sum]
  refine (sum_le_sum s1).trans ?_
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hCa
  have e2 : ∑ f ∈ Fs, ∑ l ∈ (Ico L (2 * L)).filter (Nat.Coprime f), tau f ^ K * D (f * l) =
      ∑ p ∈ P, tau p.1 ^ K * D (p.1 * p.2) := by
    rw [hP, sum_filter, sum_product]
    refine sum_congr rfl (fun f _ => ?_)
    rw [sum_filter]
  rw [e2]
  have hPmem : ∀ p ∈ P, (0 < p.1 ∧ p.1 ≤ F) ∧ L ≤ p.2 ∧ p.2 < 2 * L := by
    intro p hp
    rw [hP, mem_filter, mem_product, mem_Ico] at hp
    exact ⟨hFs _ hp.1.1, hp.1.2⟩
  have hmaps : ∀ p ∈ P, p.1 * p.2 ∈ range (2 * F * L) := by
    intro p hp
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hPmem p hp
    rw [mem_range]
    calc p.1 * p.2 ≤ F * p.2 := Nat.mul_le_mul_right _ h2
      _ < F * (2 * L) := Nat.mul_lt_mul_of_pos_left h4 (by omega)
      _ = 2 * F * L := by ring
  have htau : ∀ p ∈ P, tau p.1 ^ K * D (p.1 * p.2) ≤ tau (p.1 * p.2) ^ K * D (p.1 * p.2) := by
    intro p hp
    obtain ⟨⟨h1, -⟩, h3, -⟩ := hPmem p hp
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (htau0 _) ?_ _) (hD0 _)
    unfold tau
    exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd
      (Nat.mul_ne_zero (by omega) (by omega)) (dvd_mul_right _ _))
  refine (sum_le_sum htau).trans ?_
  rw [← sum_fiberwise_of_maps_to hmaps]
  unfold bdhEnergy
  refine sum_le_sum (fun q _ => ?_)
  have hfib : ∑ p ∈ P with p.1 * p.2 = q, tau (p.1 * p.2) ^ K * D (p.1 * p.2) =
      ((P.filter (fun p => p.1 * p.2 = q)).card : ℝ) * (tau q ^ K * D q) := by
    rw [← nsmul_eq_mul, ← sum_const]
    refine sum_congr rfl (fun p hp => ?_)
    rw [(mem_filter.1 hp).2]
  rw [hfib, pow_succ', mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (pow_nonneg (htau0 _) _) (hD0 _))
  unfold tau
  have hcard : (P.filter (fun p => p.1 * p.2 = q)).card ≤ q.divisors.card := by
    refine card_le_card_of_injOn (fun p => p.1) ?_ ?_
    · intro p hp
      rw [coe_filter] at hp
      obtain ⟨hpP, hpq⟩ := hp
      obtain ⟨⟨h1, -⟩, h3, -⟩ := hPmem p hpP
      rw [mem_coe, Nat.mem_divisors]
      refine ⟨⟨p.2, hpq.symm⟩, ?_⟩
      rw [← hpq]; exact Nat.mul_ne_zero (by omega) (by omega)
    · intro p hp p' hp' he
      rw [coe_filter] at hp hp'
      obtain ⟨hpP, hpq⟩ := hp
      obtain ⟨hpP', hpq'⟩ := hp'
      obtain ⟨⟨h1, -⟩, -, -⟩ := hPmem p hpP
      simp only at he
      have : p.2 = p'.2 := by
        rw [← he] at hpq'
        exact Nat.eq_of_mul_eq_mul_left h1 (hpq.trans hpq'.symm)
      exact Prod.ext he this
  exact_mod_cast hcard

/-- **The family Urem estimate, reduced to the BDH energy of the common sequence.** -/
theorem family_urem_le_bdhEnergy {ι : Type*} (Ξ : Finset ι) (I : Finset ℕ) (ρ : ℕ → ℝ)
    {L M F K r : ℕ} (hL : 0 < L) (f c A : ι → ℕ) (B : ι → ℤ) (Γ : ι → ℝ) (z β : ι → ℕ → ℝ)
    {W Bβ Ca : ℝ} (hW : 0 ≤ W) (hCa : 0 ≤ Ca)
    (hf : ∀ ξ ∈ Ξ, 0 < f ξ ∧ f ξ ≤ F) (hcf : ∀ ξ ∈ Ξ, Nat.Coprime (c ξ) (f ξ))
    (hz : ∀ ξ ∈ Ξ, ∀ l, z ξ l ≠ 0 → Nat.Coprime (f ξ) l ∧ Nat.Coprime (A ξ * (B ξ).natAbs) l)
    (hzW : ∀ ξ ∈ Ξ, ∀ l, |z ξ l| ≤ |Γ ξ| * W)
    (hβ : ∀ ξ ∈ Ξ, ∑ m ∈ Ico M (2 * M), β ξ m ^ 2 ≤ Bβ)
    (hmult : ∀ f0, ∑ ξ ∈ Ξ with f ξ = f0, |Γ ξ| ≤ Ca * tau f0 ^ K) :
    ∑ ξ ∈ Ξ, |uremBlock I ρ (f ξ) (c ξ) (A ξ) (B ξ) L M r (z ξ) (β ξ)| ≤
      W * Real.sqrt Bβ * Real.sqrt (∑ ξ ∈ Ξ, |Γ ξ| * ((M : ℝ) / f ξ + L)) *
        Real.sqrt (Ca * bdhEnergy I ρ (2 * F * L) K) := by
  have hBβ : ∀ ξ ∈ Ξ, 0 ≤ Bβ := fun ξ hξ =>
    le_trans (sum_nonneg (fun _ _ => sq_nonneg _)) (hβ ξ hξ)
  have hu : ∀ ξ ∈ Ξ, 0 ≤ (M : ℝ) / f ξ + L := fun ξ _ => by positivity
  have hblk : ∀ ξ ∈ Ξ, |uremBlock I ρ (f ξ) (c ξ) (A ξ) (B ξ) L M r (z ξ) (β ξ)| ≤
      (W * Real.sqrt Bβ) * (|Γ ξ| *
        Real.sqrt (((M : ℝ) / f ξ + L) * relEnergy I ρ (f ξ) L)) := by
    intro ξ hξ
    have := packet_bound I ρ (hf ξ hξ).1 hL (hcf ξ hξ) (z ξ) (β ξ) (hz ξ hξ) hW (hzW ξ hξ)
      (hβ ξ hξ) (r := r)
    linarith
  refine (sum_le_sum hblk).trans ?_
  rw [← mul_sum]
  have hc := weighted_cauchy Ξ Γ (fun ξ => (M : ℝ) / f ξ + L) (fun ξ => relEnergy I ρ (f ξ) L)
    hu (fun ξ _ => relEnergy_nonneg _ _ _ _)
  have hRsum : ∑ ξ ∈ Ξ, |Γ ξ| * relEnergy I ρ (f ξ) L ≤ Ca * bdhEnergy I ρ (2 * F * L) K := by
    rw [← sum_fiberwise_of_maps_to (g := f) (t := Ξ.image f) (fun ξ hξ => mem_image_of_mem f hξ)]
    have e : ∀ f0 ∈ Ξ.image f, ∑ ξ ∈ Ξ with f ξ = f0, |Γ ξ| * relEnergy I ρ (f ξ) L =
        (∑ ξ ∈ Ξ with f ξ = f0, |Γ ξ|) * relEnergy I ρ f0 L := by
      intro f0 _
      rw [sum_mul]
      refine sum_congr rfl (fun ξ hξ => ?_)
      rw [(mem_filter.1 hξ).2]
    rw [sum_congr rfl e]
    refine energy_grouping I ρ (Ξ.image f) ?_ hL _ hCa (fun f0 _ => hmult f0)
    intro f0 hf0
    obtain ⟨ξ, hξ, rfl⟩ := mem_image.1 hf0
    exact hf ξ hξ
  have hW' : 0 ≤ W * Real.sqrt Bβ := by positivity
  calc W * Real.sqrt Bβ * ∑ ξ ∈ Ξ, |Γ ξ| *
        Real.sqrt (((M : ℝ) / f ξ + L) * relEnergy I ρ (f ξ) L)
      ≤ W * Real.sqrt Bβ * (Real.sqrt (∑ ξ ∈ Ξ, |Γ ξ| * ((M : ℝ) / f ξ + L)) *
          Real.sqrt (∑ ξ ∈ Ξ, |Γ ξ| * relEnergy I ρ (f ξ) L)) :=
        mul_le_mul_of_nonneg_left hc hW'
    _ ≤ W * Real.sqrt Bβ * (Real.sqrt (∑ ξ ∈ Ξ, |Γ ξ| * ((M : ℝ) / f ξ + L)) *
          Real.sqrt (Ca * bdhEnergy I ρ (2 * F * L) K)) := by
        gcongr
    _ = _ := by ring

end Erdos287.Physical.TypeII.UremFamily
