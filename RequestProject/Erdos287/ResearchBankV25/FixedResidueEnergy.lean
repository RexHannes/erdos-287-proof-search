import Mathlib

/-!
# Erdős #287 — Research Bank V25 §3.3–3.4: conditioned residue energy (finite-group projection)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

All statements allow ARBITRARY complex residue masses `z_r`.  `‖w‖²` is written
`Complex.normSq w`.

**LEAN BANK.**

* `fibre_pythagoras` — abstract projection identity.  For a finite set of residues `R`, a
  fibre map `π : R → U` all of whose fibres have the same cardinality `k`, arbitrary masses `z`
  and an arbitrary centre `c` (e.g. the full average), with `D_r = z_r − c` and conditioned
  discrepancy `E_r = z_r − (1/k) Σ_{π s = π r} z_s`:

      Σ_r |E_r|² = Σ_r |D_r|² − (1/k) Σ_u |Σ_{π r = u} D_r|².

* `conditioned_energy_le` — hence conditioned energy ≤ full-modulus energy.
* `overlap_fibre_card` / `overlap_pythagoras` — the general overlapping-modulus instance: `R` is
  `(ℤ/m)^×` with `m` any multiple of `f` (e.g. `m = lcm(f,q)`), `π` the reduction to `(ℤ/f)^×`;
  every fibre (the compatible fibre `A_u`) has the same size `k` with `k · φ(f) = φ(m)`.
* `product_pythagoras` / `coprime_conditioned_energy_le` — the coprime instance on
  `(ℤ/f)^× × (ℤ/q)^×` (`g = 1`, `k = φ(q)`).
* `localized_discrepancy_eq` — for `α_u(n) = α(n) 1_{n ≡ u (f)}`, the literal localized
  discrepancy `Δ_{α_u}(q,a)` equals the conditioned discrepancy `E_{u,a}` of the residue masses
  `z(u,a) = Σ_{n ≡ u (f), n ≡ a (q)} α(n)`.
* `full_discrepancy_eq` — the literal full-modulus discrepancy `Δ_α(fq, r)` equals `D_{CRT(r)}`.
* **`localized_energy_le_full`** — `Σ_u Σ_a |Δ_{α_u}(q,a)|² ≤ Σ_r |Δ_α(fq,r)|²`.
* `divisor_reindexing` — `Σ_{q≤U} τ(q)^J S(q) ≤ Σ_{ℓ≤fU} τ(ℓ)^J T(ℓ)` whenever
  `S(q) ≤ T(fq)` and `T ≥ 0` (using `τ(q) ≤ τ(fq)`).

**Semantic firewall.**  `α_u` is NOT asserted to be globally Siegel–Walfisz anywhere; only the
full-modulus energy of `α` is ever consumed.  The final BDH saving for that energy is the
EXTERNAL PROVIDER `BDHEnergyProvider` of `LocalizationContract.lean`.
-/

namespace Erdos287
namespace ResearchBankV25
namespace FixedResidueEnergy

open Finset Complex

section Abstract

variable {R U : Type*} [Fintype R] [Fintype U] [DecidableEq U]

/-- One fibre: `Σ_{r∈s} |D_r − S/k|² = Σ_{r∈s} |D_r|² − |S|²/k` for `S = Σ_{r∈s} D_r`,
`k = #s`. -/
theorem fibre_one {ι : Type*} (s : Finset ι) (D : ι → ℂ) :
    ∑ r ∈ s, normSq (D r - (∑ t ∈ s, D t) / (s.card : ℂ)) =
      ∑ r ∈ s, normSq (D r) - normSq (∑ t ∈ s, D t) / (s.card : ℝ) := by
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · rw [Finset.card_eq_zero.1 h0]; simp
  set S := ∑ t ∈ s, D t
  set k : ℝ := (s.card : ℝ)
  have hk : (0 : ℝ) < k := by simp only [k]; exact_mod_cast hpos
  have hkc : ((s.card : ℂ)) = (k : ℂ) := by simp [k]
  simp_rw [normSq_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hre : ∑ r ∈ s, 2 * (D r * (starRingEnd ℂ) (S / (s.card : ℂ))).re =
      2 * normSq S / k := by
    rw [← Finset.mul_sum, ← Complex.re_sum, ← Finset.sum_mul, hkc, map_div₀,
      Complex.conj_ofReal, mul_div_assoc', Complex.div_ofReal_re, Complex.mul_conj,
      Complex.ofReal_re]
    ring
  rw [hre, hkc, Complex.normSq_div, Complex.normSq_ofReal]
  field_simp
  ring

/-- **Abstract projection identity** (LEAN BANK). -/
theorem fibre_pythagoras (π : R → U) (k : ℕ) (hk : ∀ u, (univ.filter fun r => π r = u).card = k)
    (z : R → ℂ) (c : ℂ) :
    ∑ r, normSq (z r - (∑ s ∈ univ.filter (fun s => π s = π r), z s) / (k : ℂ)) =
      ∑ r, normSq (z r - c) -
        (1 / (k : ℝ)) * ∑ u, normSq (∑ r ∈ univ.filter (fun r => π r = u), (z r - c)) := by
  rw [← Finset.sum_fiberwise univ π, ← Finset.sum_fiberwise univ π (fun r => normSq (z r - c)),
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hcard := hk u
  have key := fibre_one (univ.filter fun r => π r = u) (fun r => z r - c)
  rw [hcard] at key
  rw [← key.trans (by ring : _ = _ - 1 / (k : ℝ) * _)]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hru : π r = u := (Finset.mem_filter.1 hr).2
  congr 1
  rw [hru]
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · exfalso
    have : r ∈ univ.filter fun s => π s = u := hr
    rw [Finset.card_eq_zero.1 (hcard.trans h0)] at this
    simp at this
  · have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
    field_simp
    ring

/-- **Contraction: conditioned energy ≤ full energy** (LEAN BANK). -/
theorem conditioned_energy_le (π : R → U) (k : ℕ)
    (hk : ∀ u, (univ.filter fun r => π r = u).card = k) (z : R → ℂ) (c : ℂ) :
    ∑ r, normSq (z r - (∑ s ∈ univ.filter (fun s => π s = π r), z s) / (k : ℂ)) ≤
      ∑ r, normSq (z r - c) := by
  rw [fibre_pythagoras π k hk z c]
  have : 0 ≤ (1 / (k : ℝ)) * ∑ u, normSq (∑ r ∈ univ.filter (fun r => π r = u), (z r - c)) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => normSq_nonneg _)
  exact sub_le_self _ this

end Abstract

section Overlap

/-- **Overlapping moduli: all compatible fibres have the same size** (LEAN BANK).  For `f ∣ m`
(e.g. `m = lcm(f,q)`) the reduction `(ℤ/m)^× → (ℤ/f)^×` is surjective, so all fibres have the
common size `k` of the kernel, and `k · φ(f) = φ(m)`. -/
theorem overlap_fibre_card {f m : ℕ} [NeZero f] [NeZero m] (hfm : f ∣ m) :
    ∃ k : ℕ, (∀ u : (ZMod f)ˣ,
      (univ.filter fun r : (ZMod m)ˣ => ZMod.unitsMap hfm r = u).card = k) ∧
      k * f.totient = m.totient := by
  have hsurj := ZMod.unitsMap_surjective (n := f) (m := m) hfm
  refine ⟨(univ.filter fun r : (ZMod m)ˣ => ZMod.unitsMap hfm r = 1).card, fun u => ?_, ?_⟩
  · exact MonoidHom.card_fiber_eq_of_mem_range (ZMod.unitsMap hfm) (hsurj u) (hsurj 1)
  · have h1 := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (ZMod m)ˣ))
      (t := (univ : Finset (ZMod f)ˣ)) (f := ZMod.unitsMap hfm) (fun _ _ => Finset.mem_coe.2 (mem_univ _))
    have h2 : ∀ u : (ZMod f)ˣ, (univ.filter fun r : (ZMod m)ˣ => ZMod.unitsMap hfm r = u).card =
        (univ.filter fun r : (ZMod m)ˣ => ZMod.unitsMap hfm r = 1).card := fun u =>
      MonoidHom.card_fiber_eq_of_mem_range (ZMod.unitsMap hfm) (hsurj u) (hsurj 1)
    rw [Finset.sum_congr rfl fun u _ => h2 u, Finset.sum_const, Finset.card_univ,
      ZMod.card_units_eq_totient, smul_eq_mul, Finset.card_univ, ZMod.card_units_eq_totient] at h1
    rw [h1, mul_comm]

/-- **Overlapping-modulus Pythagorean identity** (LEAN BANK): arbitrary complex masses on
`(ℤ/m)^×`, conditioned on the residue modulo `f`. -/
theorem overlap_pythagoras {f m : ℕ} [NeZero f] [NeZero m] (hfm : f ∣ m) (z : (ZMod m)ˣ → ℂ)
    (c : ℂ) :
    ∃ k : ℕ, k * f.totient = m.totient ∧
      ∑ r, normSq (z r - (∑ s ∈ univ.filter
          (fun s => ZMod.unitsMap hfm s = ZMod.unitsMap hfm r), z s) / (k : ℂ)) =
        ∑ r, normSq (z r - c) - (1 / (k : ℝ)) *
          ∑ u, normSq (∑ r ∈ univ.filter (fun r => ZMod.unitsMap hfm r = u), (z r - c)) := by
  obtain ⟨k, hk, hkm⟩ := overlap_fibre_card hfm
  exact ⟨k, hkm, fibre_pythagoras _ k hk z c⟩

end Overlap

section Product

variable {U A : Type*} [Fintype U] [Fintype A] [DecidableEq U]

theorem prod_fibre_card (u : U) :
    (univ.filter fun r : U × A => r.1 = u).card = Fintype.card A := by
  rw [show (univ.filter fun r : U × A => r.1 = u) = ({u} : Finset U) ×ˢ (univ : Finset A) by
    ext ⟨a, b⟩; simp [eq_comm]]
  simp

theorem prod_fibre_sum (z : U × A → ℂ) (u : U) :
    ∑ s ∈ univ.filter (fun s : U × A => s.1 = u), z s = ∑ b, z (u, b) := by
  rw [show (univ.filter fun r : U × A => r.1 = u) = ({u} : Finset U) ×ˢ (univ : Finset A) by
    ext ⟨a, b⟩; simp [eq_comm], Finset.sum_product]
  simp

/-- **Coprime (product) Pythagorean identity** (LEAN BANK): `k = #A` (`= φ(q)`),
`E_{u,a} = z(u,a) − (1/k) Σ_b z(u,b)`. -/
theorem product_pythagoras (z : U × A → ℂ) (c : ℂ) :
    ∑ u, ∑ a, normSq (z (u, a) - (∑ b, z (u, b)) / (Fintype.card A : ℂ)) =
      ∑ u, ∑ a, normSq (z (u, a) - c) -
        (1 / (Fintype.card A : ℝ)) * ∑ u, normSq (∑ a, (z (u, a) - c)) := by
  have := fibre_pythagoras (R := U × A) Prod.fst (Fintype.card A) prod_fibre_card z c
  simp only [prod_fibre_sum] at this
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  convert this using 3

/-- **Coprime contraction** (LEAN BANK). -/
theorem coprime_conditioned_energy_le (z : U × A → ℂ) (c : ℂ) :
    ∑ u, ∑ a, normSq (z (u, a) - (∑ b, z (u, b)) / (Fintype.card A : ℂ)) ≤
      ∑ u, ∑ a, normSq (z (u, a) - c) := by
  rw [product_pythagoras]
  have : 0 ≤ (1 / (Fintype.card A : ℝ)) * ∑ u, normSq (∑ a, (z (u, a) - c)) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => normSq_nonneg _)
  exact sub_le_self _ this

end Product

section Sequence

variable {f q : ℕ} [NeZero f] [NeZero q]

/-- `Σ_{b ∈ G_q} 1_{x = b} c = 1_{x unit} c`. -/
theorem sum_units_ite (x : ZMod q) (c : ℂ) :
    ∑ b : (ZMod q)ˣ, (if x = (b : ZMod q) then c else 0) = if IsUnit x then c else 0 := by
  by_cases hx : IsUnit x
  · obtain ⟨u0, rfl⟩ := hx
    rw [if_pos ⟨u0, rfl⟩, Finset.sum_eq_single u0]
    · simp
    · intro b _ hb; rw [if_neg]; intro h; exact hb (Units.ext h.symm)
    · simp
  · rw [if_neg hx]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]; rintro rfl; exact hx b.isUnit

omit [NeZero f] [NeZero q] in
theorem sum_units_prod_ite [Fintype (ZMod f)ˣ] [Fintype (ZMod q)ˣ] (x : ZMod f) (y : ZMod q)
    (c : ℂ) :
    ∑ p : (ZMod f)ˣ × (ZMod q)ˣ, (if x = (p.1 : ZMod f) ∧ y = (p.2 : ZMod q) then c else 0) =
      if IsUnit x ∧ IsUnit y then c else 0 := by
  by_cases h : IsUnit x ∧ IsUnit y
  · obtain ⟨⟨u0, rfl⟩, ⟨a0, rfl⟩⟩ := h
    rw [if_pos ⟨u0.isUnit, a0.isUnit⟩, Finset.sum_eq_single (u0, a0)]
    · simp
    · rintro ⟨b1, b2⟩ _ hb
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hb (Prod.ext (Units.ext h1.symm) (Units.ext h2.symm))
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact h ⟨p.1.isUnit, p.2.isUnit⟩

/-- Residue masses `z(u,a) = Σ_{n ∈ Ns, n ≡ u (f), n ≡ a (q)} α(n)`. -/
noncomputable def zres (Ns : Finset ℕ) (α : ℕ → ℂ) (p : (ZMod f)ˣ × (ZMod q)ˣ) : ℂ :=
  ∑ n ∈ Ns, if (n : ZMod f) = p.1 ∧ (n : ZMod q) = p.2 then α n else 0

/-- The localized sequence `α_u(n) = α(n) 1_{n ≡ u (f)}`. -/
noncomputable def alphaLoc (α : ℕ → ℂ) (u : (ZMod f)ˣ) (n : ℕ) : ℂ :=
  if (n : ZMod f) = u then α n else 0

/-- Literal discrepancy `Δ_β(q,a) = Σ_{n ≡ a (q)} β(n) − (1/φ(q)) Σ_{(n,q)=1} β(n)`. -/
noncomputable def Disc (q : ℕ) (Ns : Finset ℕ) (β : ℕ → ℂ) (a : ZMod q) : ℂ :=
  (∑ n ∈ Ns, if (n : ZMod q) = a then β n else 0) -
    (1 / (q.totient : ℂ)) * ∑ n ∈ Ns, if Nat.Coprime n q then β n else 0

omit [NeZero f] [NeZero q] in
theorem coprime_iff_isUnit (n : ℕ) : Nat.Coprime n q ↔ IsUnit (n : ZMod q) :=
  (ZMod.isUnit_iff_coprime n q).symm

omit [NeZero f] in
/-- **The localized discrepancy is the conditioned discrepancy** (LEAN BANK). -/
theorem localized_discrepancy_eq (Ns : Finset ℕ) (α : ℕ → ℂ) (u : (ZMod f)ˣ) (a : (ZMod q)ˣ) :
    Disc q Ns (alphaLoc α u) a =
      zres Ns α (u, a) - (∑ b : (ZMod q)ˣ, zres Ns α (u, b)) / (Fintype.card (ZMod q)ˣ : ℂ) := by
  unfold Disc zres alphaLoc
  rw [ZMod.card_units_eq_totient]
  have h1 : (∑ n ∈ Ns, if (n : ZMod q) = a then (if (n : ZMod f) = u then α n else 0) else 0) =
      ∑ n ∈ Ns, if (n : ZMod f) = (u, a).1 ∧ (n : ZMod q) = (u, a).2 then α n else 0 := by
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h1 : (n : ZMod f) = u <;> by_cases h2 : (n : ZMod q) = a <;> simp [h1, h2]
  have h2 : (∑ n ∈ Ns, if Nat.Coprime n q then (if (n : ZMod f) = u then α n else 0) else 0) =
      ∑ b : (ZMod q)ˣ, ∑ n ∈ Ns,
        if (n : ZMod f) = (u, b).1 ∧ (n : ZMod q) = (u, b).2 then α n else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [coprime_iff_isUnit]
    by_cases h1 : (n : ZMod f) = u
    · simp only [h1, true_and, if_true]
      rw [sum_units_ite]
    · simp [h1]
  rw [h1, h2]
  ring

variable (hfq : Nat.Coprime f q)

instance : NeZero (f * q) := ⟨Nat.mul_ne_zero (NeZero.ne f) (NeZero.ne q)⟩

/-- The CRT isomorphism on units `(ℤ/fq)^× ≃ (ℤ/f)^× × (ℤ/q)^×`. -/
noncomputable def crtUnits : (ZMod (f * q))ˣ ≃* (ZMod f)ˣ × (ZMod q)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder hfq).toMulEquiv).trans MulEquiv.prodUnits

omit [NeZero f] [NeZero q] in
theorem crtUnits_val (r : (ZMod (f * q))ˣ) :
    (((crtUnits hfq r).1 : ZMod f), ((crtUnits hfq r).2 : ZMod q)) =
      ZMod.chineseRemainder hfq (r : ZMod (f * q)) := by
  rfl

omit [NeZero f] [NeZero q] in
theorem natCast_eq_iff (n : ℕ) (r : (ZMod (f * q))ˣ) :
    (n : ZMod (f * q)) = r ↔
      (n : ZMod f) = (crtUnits hfq r).1 ∧ (n : ZMod q) = (crtUnits hfq r).2 := by
  rw [← Prod.mk.injEq, crtUnits_val]
  constructor
  · intro h; rw [← h, map_natCast]; rfl
  · intro h
    apply (ZMod.chineseRemainder hfq).injective
    rw [← h, map_natCast]; rfl

/-- **The full-modulus discrepancy is `D` at the CRT pair** (LEAN BANK). -/
theorem full_discrepancy_eq (Ns : Finset ℕ) (α : ℕ → ℂ) (r : (ZMod (f * q))ˣ) :
    Disc (f * q) Ns α r =
      zres Ns α (crtUnits hfq r) -
        (∑ p : (ZMod f)ˣ × (ZMod q)ˣ, zres Ns α p) / (Fintype.card ((ZMod f)ˣ × (ZMod q)ˣ) : ℂ) := by
  unfold Disc zres
  rw [Fintype.card_prod, ZMod.card_units_eq_totient, ZMod.card_units_eq_totient,
    ← Nat.totient_mul hfq]
  have h1 : (∑ n ∈ Ns, if (n : ZMod (f * q)) = r then α n else 0) =
      ∑ n ∈ Ns, if (n : ZMod f) = (crtUnits hfq r).1 ∧ (n : ZMod q) = (crtUnits hfq r).2
        then α n else 0 := by
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [natCast_eq_iff hfq]
  have h2 : (∑ n ∈ Ns, if Nat.Coprime n (f * q) then α n else 0) =
      ∑ p : (ZMod f)ˣ × (ZMod q)ˣ, ∑ n ∈ Ns,
        if (n : ZMod f) = p.1 ∧ (n : ZMod q) = p.2 then α n else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Nat.coprime_mul_iff_right, coprime_iff_isUnit (q := f),
      coprime_iff_isUnit (q := q)]
    rw [sum_units_prod_ite]
  rw [h1, h2]
  ring

include hfq in
/-- **Localized energy ≤ full-modulus energy** (LEAN BANK):

    Σ_{u ∈ G_f} Σ_{a ∈ G_q} |Δ_{α_u}(q,a)|² ≤ Σ_{r ∈ G_{fq}} |Δ_α(fq,r)|². -/
theorem localized_energy_le_full (Ns : Finset ℕ) (α : ℕ → ℂ) :
    ∑ u : (ZMod f)ˣ, ∑ a : (ZMod q)ˣ, normSq (Disc q Ns (alphaLoc α u) a) ≤
      ∑ r : (ZMod (f * q))ˣ, normSq (Disc (f * q) Ns α r) := by
  simp_rw [localized_discrepancy_eq, full_discrepancy_eq hfq]
  set C : ℂ := (∑ p : (ZMod f)ˣ × (ZMod q)ˣ, zres Ns α p) /
    (Fintype.card ((ZMod f)ˣ × (ZMod q)ˣ) : ℂ)
  have hR : ∑ r : (ZMod (f * q))ˣ, normSq (zres Ns α (crtUnits hfq r) - C) =
      ∑ p : (ZMod f)ˣ × (ZMod q)ˣ, normSq (zres Ns α p - C) :=
    Fintype.sum_equiv (crtUnits hfq).toEquiv _ _ (fun r => rfl)
  rw [hR, Fintype.sum_prod_type]
  exact coprime_conditioned_energy_le (U := (ZMod f)ˣ) (A := (ZMod q)ˣ) (zres Ns α) C

end Sequence

section Reindex

/-- **Divisor-weighted reindexing** (LEAN BANK): `q ↦ fq` is injective from `[1,U]` into
`[1,fU]`, `τ(q) ≤ τ(fq)`, and the target terms are nonnegative. -/
theorem divisor_reindexing (f U J : ℕ) (hf : 0 < f) (S T : ℕ → ℝ)
    (hST : ∀ q, 1 ≤ q → S q ≤ T (f * q)) (hT : ∀ l, 0 ≤ T l) :
    ∑ q ∈ Finset.Icc 1 U, ((q.divisors.card : ℝ)) ^ J * S q ≤
      ∑ l ∈ Finset.Icc 1 (f * U), ((l.divisors.card : ℝ)) ^ J * T l := by
  have hinj : Set.InjOn (fun q => f * q) (Finset.Icc 1 U : Set ℕ) := fun a _ b _ h =>
    Nat.eq_of_mul_eq_mul_left hf h
  have hsub : (Finset.Icc 1 U).image (fun q => f * q) ⊆ Finset.Icc 1 (f * U) := by
    intro l hl
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hl
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hq
    exact Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hf.ne' (by omega)),
      Nat.mul_le_mul_left f h2⟩
  calc ∑ q ∈ Finset.Icc 1 U, ((q.divisors.card : ℝ)) ^ J * S q
      ≤ ∑ q ∈ Finset.Icc 1 U, (((f * q).divisors.card : ℝ)) ^ J * T (f * q) := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hq).1
        have hdiv : q.divisors.card ≤ (f * q).divisors.card :=
          Finset.card_le_card (Nat.divisors_subset_of_dvd (Nat.mul_ne_zero hf.ne' (by omega))
            (dvd_mul_left q f))
        have hdiv' : ((q.divisors.card : ℝ)) ^ J ≤ (((f * q).divisors.card : ℝ)) ^ J :=
          pow_le_pow_left₀ (by positivity) (by exact_mod_cast hdiv) J
        rcases le_or_gt 0 (S q) with hS | hS
        · exact mul_le_mul hdiv' (hST q hq1) hS (by positivity)
        · calc ((q.divisors.card : ℝ)) ^ J * S q ≤ 0 :=
                mul_nonpos_of_nonneg_of_nonpos (by positivity) hS.le
            _ ≤ _ := mul_nonneg (by positivity) (hT _)
    _ = ∑ l ∈ (Finset.Icc 1 U).image (fun q => f * q), ((l.divisors.card : ℝ)) ^ J * T l :=
        (Finset.sum_image (f := fun l => ((l.divisors.card : ℝ)) ^ J * T l) hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun l _ _ =>
        mul_nonneg (by positivity) (hT l)

end Reindex

end FixedResidueEnergy
end ResearchBankV25
end Erdos287
