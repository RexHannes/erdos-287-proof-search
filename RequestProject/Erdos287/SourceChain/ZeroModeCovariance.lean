import RequestProject.Erdos287.SourceChain.TypeIISplit

/-!
# Erdős #287 — V100R source chain: zero-mode covariance (§2.5)

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

For moduli `r₁, r₂ ≥ 1` with `g = (r₁,r₂)`, `L = [r₁,r₂]` and the centred indicators
`X_r^a(v) = 1_{v ≡ a (r)} - 1_{(v,r)=1}/φ(r)`, the complete finite-residue identity is

  `∑_{v mod L} X_{r₁}^{a₁}(v) X_{r₂}^{a₂}(v) = 1_{a₁ ≡ a₂ (g)} - 1/φ(g)`     (units `a₁, a₂`),

and, after inserting the tiny-base and `l` congruences (one class modulo the coprime
`q = fl`), the normalised version over a complete residue system modulo `flL` is

  `(1/(fl[r₁,r₂])) (1_{a₁ ≡ a₂ (g)} - 1/φ(g))`.

Kernel-proved:

* `primeFactors_lcm'`, `totient_lcm_mul_totient_gcd` — `φ([a,b]) φ((a,b)) = φ(a) φ(b)`;
* `unitsFibre_card_mul_totient` — for `r ∣ L` and a unit `a (mod r)`, the number of units
  modulo `L` reducing to `a` is `φ(L)/φ(r)` (via `ZMod.unitsMap_surjective`);
* `card_two_congr` — generalised CRT count: `#{v < L : v ≡ a₁ (r₁), v ≡ a₂ (r₂)} = 1_{a₁≡a₂ (g)}`;
* `zeroMode_covariance` — the identity above;
* `sum_crt_lift` and `zeroMode_covariance_full` — the normalised `1/(fl[r₁,r₂])` version.
-/

open scoped BigOperators
open Finset

namespace Erdos287.SourceChain

open Erdos287.CurrentTail

/-! ### Totient identities -/

theorem primeFactors_lcm' {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.lcm a b).primeFactors = a.primeFactors ∪ b.primeFactors := by
  ext p
  simp only [Finset.mem_union, Nat.mem_primeFactors, ne_eq, Nat.lcm_eq_zero_iff, ha, hb,
    or_self, not_false_eq_true, and_true]
  constructor
  · rintro ⟨hp, hd⟩
    have : p ∣ a * b := hd.trans (Nat.lcm_dvd_mul a b)
    exact (hp.dvd_mul.1 this).imp (fun h => ⟨hp, h⟩) (fun h => ⟨hp, h⟩)
  · rintro (⟨hp, h⟩ | ⟨hp, h⟩)
    · exact ⟨hp, h.trans (Nat.dvd_lcm_left a b)⟩
    · exact ⟨hp, h.trans (Nat.dvd_lcm_right a b)⟩

/-- `φ([a,b]) · φ((a,b)) = φ(a) · φ(b)`. -/
theorem totient_lcm_mul_totient_gcd {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.totient (Nat.lcm a b) * Nat.totient (Nat.gcd a b) = Nat.totient a * Nat.totient b := by
  have key : ((Nat.totient (Nat.lcm a b) * Nat.totient (Nat.gcd a b) : ℕ) : ℚ) =
      ((Nat.totient a * Nat.totient b : ℕ) : ℚ) := by
    push_cast
    rw [Nat.totient_eq_mul_prod_factors, Nat.totient_eq_mul_prod_factors,
      Nat.totient_eq_mul_prod_factors a, Nat.totient_eq_mul_prod_factors b,
      primeFactors_lcm' ha hb, Nat.primeFactors_gcd ha hb]
    have h1 := Finset.prod_union_inter (s₁ := a.primeFactors) (s₂ := b.primeFactors)
      (f := fun p : ℕ => (1 - (p : ℚ)⁻¹))
    have h2 : ((Nat.lcm a b : ℕ) : ℚ) * ((Nat.gcd a b : ℕ) : ℚ) = (a : ℚ) * b := by
      exact_mod_cast (by rw [mul_comm]; exact Nat.gcd_mul_lcm a b)
    calc _ = (((Nat.lcm a b : ℕ) : ℚ) * ((Nat.gcd a b : ℕ) : ℚ)) *
          ((∏ p ∈ a.primeFactors ∪ b.primeFactors, (1 - (p : ℚ)⁻¹)) *
            ∏ p ∈ a.primeFactors ∩ b.primeFactors, (1 - (p : ℚ)⁻¹)) := by ring
      _ = _ := by rw [h1, h2]; ring
  exact_mod_cast key

/-! ### Fibres of the unit reduction map -/

/-- For `r ∣ L` and a unit `a` modulo `r`, the units modulo `L` lying over `a` number
`φ(L)/φ(r)`. -/
theorem unitsFibre_card_mul_totient {r L : ℕ} (hL : 0 < L) (hrL : r ∣ L) {a : ℕ}
    (ha : Nat.Coprime a r) :
    ((range L).filter (fun v => Nat.Coprime v L ∧ v ≡ a [MOD r])).card * Nat.totient r =
      Nat.totient L := by
  haveI : NeZero L := ⟨hL.ne'⟩
  have hr : 0 < r := Nat.pos_of_dvd_of_pos hrL hL
  haveI : NeZero r := ⟨hr.ne'⟩
  classical
  have hfib : ∀ y : (ZMod r)ˣ,
      (univ.filter (fun g : (ZMod L)ˣ => ZMod.unitsMap hrL g = y)).card =
      (univ.filter (fun g : (ZMod L)ˣ => ZMod.unitsMap hrL g =
        ZMod.unitOfCoprime a ha)).card := fun y =>
    MonoidHom.card_fiber_eq_of_mem_range (ZMod.unitsMap hrL) (ZMod.unitsMap_surjective hrL y)
      (ZMod.unitsMap_surjective hrL _)
  have htot : (univ.filter (fun g : (ZMod L)ˣ => ZMod.unitsMap hrL g =
        ZMod.unitOfCoprime a ha)).card * Nat.totient r = Nat.totient L := by
    calc _ = ∑ y : (ZMod r)ˣ,
          (univ.filter (fun g : (ZMod L)ˣ => ZMod.unitsMap hrL g = y)).card := by
          rw [Finset.sum_congr rfl (fun y _ => hfib y), Finset.sum_const, smul_eq_mul,
            Finset.card_univ, ZMod.card_units_eq_totient, mul_comm]
      _ = (univ : Finset (ZMod L)ˣ).card :=
          (Finset.card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)).symm
      _ = _ := by rw [Finset.card_univ, ZMod.card_units_eq_totient]
  rw [← htot]
  congr 1
  refine Finset.card_bij (fun v hv => ZMod.unitOfCoprime v (Finset.mem_filter.1 hv).2.1)
    ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply Units.ext
    simp [ZMod.unitsMap_def, ZMod.unitOfCoprime]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 (Finset.mem_filter.1 hv).2.2
  · intro v hv w hw hvw
    have := congrArg (fun u : (ZMod L)ˣ => ((u : ZMod L)).val) hvw
    simp [ZMod.unitOfCoprime, ZMod.val_natCast] at this
    rwa [Nat.mod_eq_of_lt (Finset.mem_range.1 (Finset.mem_filter.1 hv).1),
      Nat.mod_eq_of_lt (Finset.mem_range.1 (Finset.mem_filter.1 hw).1)] at this
  · intro g hg
    refine ⟨(g : ZMod L).val, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨ZMod.val_lt _, ZMod.val_coe_unit_coprime g, ?_⟩
      have hg' := (Finset.mem_filter.1 hg).2
      have := congrArg (fun u : (ZMod r)ˣ => (u : ZMod r)) hg'
      simp [ZMod.unitsMap_def, ZMod.unitOfCoprime] at this
      rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.cast_natCast hrL, ZMod.natCast_zmod_val]
      exact this
    · apply Units.ext; simp [ZMod.unitOfCoprime]

/-! ### Generalised CRT count -/

/-- `#{v < [r₁,r₂] : v ≡ a₁ (r₁), v ≡ a₂ (r₂)} = 1_{a₁ ≡ a₂ (mod (r₁,r₂))}`. -/
theorem card_two_congr {r1 r2 : ℕ} (h1 : 0 < r1) (h2 : 0 < r2) (a1 a2 : ℕ) :
    (((range (Nat.lcm r1 r2)).filter (fun v => v ≡ a1 [MOD r1] ∧ v ≡ a2 [MOD r2])).card : ℝ) =
      ind (a1 ≡ a2 [MOD Nat.gcd r1 r2]) := by
  have hL : 0 < Nat.lcm r1 r2 := Nat.lcm_pos h1 h2
  unfold ind
  split_ifs with hc
  · obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder' (n := r1) (m := r2) hc
    have hk : (range (Nat.lcm r1 r2)).filter (fun v => v ≡ a1 [MOD r1] ∧ v ≡ a2 [MOD r2]) =
        {k % Nat.lcm r1 r2} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      have hkL1 : k % Nat.lcm r1 r2 ≡ k [MOD r1] :=
        Nat.ModEq.of_dvd (Nat.dvd_lcm_left r1 r2) (Nat.mod_modEq k _)
      have hkL2 : k % Nat.lcm r1 r2 ≡ k [MOD r2] :=
        Nat.ModEq.of_dvd (Nat.dvd_lcm_right r1 r2) (Nat.mod_modEq k _)
      constructor
      · rintro ⟨hv, hv1, hv2⟩
        have h := Nat.mod_lcm (hv1.trans (hkL1.trans hk1).symm) (hv2.trans (hkL2.trans hk2).symm)
        unfold Nat.ModEq at h
        rwa [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (Nat.mod_lt _ hL)] at h
      · rintro rfl
        exact ⟨Nat.mod_lt _ hL, hkL1.trans hk1, hkL2.trans hk2⟩
    rw [hk]; simp
  · have : (range (Nat.lcm r1 r2)).filter (fun v => v ≡ a1 [MOD r1] ∧ v ≡ a2 [MOD r2]) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro v - ⟨hv1, hv2⟩
      exact hc ((Nat.ModEq.of_dvd (Nat.gcd_dvd_left r1 r2) hv1).symm.trans
        (Nat.ModEq.of_dvd (Nat.gcd_dvd_right r1 r2) hv2))
    rw [this]; simp

/-! ### The zero-mode covariance identity -/

theorem coprime_iff_of_modEq {a b n : ℕ} (h : a ≡ b [MOD n]) :
    Nat.Coprime a n ↔ Nat.Coprime b n := by
  unfold Nat.Coprime; rw [h.gcd_eq]

/-- Centred indicator `X_r^a(v) = 1_{v ≡ a (r)} - 1_{(v,r)=1}/φ(r)`. -/
noncomputable def Xc (r a v : ℕ) : ℝ :=
  ind (v ≡ a [MOD r]) - ind (Nat.Coprime v r) / (Nat.totient r : ℝ)

theorem sum_ind_eq_card (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ∑ v ∈ s, ind (P v) = ((s.filter P).card : ℝ) := by
  unfold ind; rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, mul_one]

/-- Cross term: `∑_{v<L} 1_{v≡a (r)} 1_{(v,r')=1} = φ(L)/φ(r)` for a unit `a (mod r)`. -/
theorem cross_term {r r' L : ℕ} (hL : 0 < L) (hrL : r ∣ L)
    (hcop : ∀ v, Nat.Coprime v r ∧ Nat.Coprime v r' ↔ Nat.Coprime v L) {a : ℕ}
    (ha : Nat.Coprime a r) :
    ∑ v ∈ range L, ind (v ≡ a [MOD r]) * ind (Nat.Coprime v r') =
      (Nat.totient L : ℝ) / (Nat.totient r : ℝ) := by
  have hr : 0 < r := Nat.pos_of_dvd_of_pos hrL hL
  have hφ : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.2 hr
  have h := unitsFibre_card_mul_totient hL hrL ha
  have hcast : ((((range L).filter (fun v => Nat.Coprime v L ∧ v ≡ a [MOD r])).card : ℕ) : ℝ) *
      (Nat.totient r : ℝ) = (Nat.totient L : ℝ) := by exact_mod_cast h
  rw [eq_div_iff hφ.ne', ← hcast]
  have : ∑ v ∈ range L, ind (v ≡ a [MOD r]) * ind (Nat.Coprime v r') =
      ∑ v ∈ range L, ind (Nat.Coprime v L ∧ v ≡ a [MOD r]) := by
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [← ind_and]
    refine ind_congr ⟨fun ⟨h1, h2⟩ => ⟨(hcop v).1 ⟨(coprime_iff_of_modEq h1).2 ha, h2⟩, h1⟩,
      fun ⟨h1, h2⟩ => ⟨h2, ((hcop v).2 h1).2⟩⟩
  rw [this, sum_ind_eq_card]

/-- **§2.5 Zero-mode covariance (complete finite-residue identity).**
For units `a₁ (mod r₁)`, `a₂ (mod r₂)`:
`∑_{v mod [r₁,r₂]} X_{r₁}^{a₁}(v) X_{r₂}^{a₂}(v) = 1_{a₁ ≡ a₂ ((r₁,r₂))} - 1/φ((r₁,r₂))`. -/
theorem zeroMode_covariance {r1 r2 : ℕ} (h1 : 0 < r1) (h2 : 0 < r2) {a1 a2 : ℕ}
    (ha1 : Nat.Coprime a1 r1) (ha2 : Nat.Coprime a2 r2) :
    ∑ v ∈ range (Nat.lcm r1 r2), Xc r1 a1 v * Xc r2 a2 v =
      ind (a1 ≡ a2 [MOD Nat.gcd r1 r2]) - 1 / (Nat.totient (Nat.gcd r1 r2) : ℝ) := by
  set L := Nat.lcm r1 r2
  set g := Nat.gcd r1 r2
  have hL : 0 < L := Nat.lcm_pos h1 h2
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ h1
  have hcop : ∀ v, Nat.Coprime v r1 ∧ Nat.Coprime v r2 ↔ Nat.Coprime v L := fun v => by
    constructor
    · rintro ⟨a, b⟩
      exact Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul r1 r2) (Nat.Coprime.mul_right a b)
    · intro h; exact ⟨Nat.Coprime.coprime_dvd_right (Nat.dvd_lcm_left r1 r2) h,
        Nat.Coprime.coprime_dvd_right (Nat.dvd_lcm_right r1 r2) h⟩
  have hcop' : ∀ v, Nat.Coprime v r2 ∧ Nat.Coprime v r1 ↔ Nat.Coprime v L :=
    fun v => and_comm.trans (hcop v)
  have hA : ∑ v ∈ range L, ind (v ≡ a1 [MOD r1]) * ind (v ≡ a2 [MOD r2]) =
      ind (a1 ≡ a2 [MOD g]) := by
    rw [← card_two_congr h1 h2, ← sum_ind_eq_card]
    exact Finset.sum_congr rfl (fun v _ => (ind_and _ _).symm)
  have hB := cross_term hL (Nat.dvd_lcm_left r1 r2) hcop ha1
  have hC := cross_term hL (Nat.dvd_lcm_right r1 r2) hcop' ha2
  have hD : ∑ v ∈ range L, ind (Nat.Coprime v r1) * ind (Nat.Coprime v r2) =
      (Nat.totient L : ℝ) := by
    rw [show ∑ v ∈ range L, ind (Nat.Coprime v r1) * ind (Nat.Coprime v r2) =
        ∑ v ∈ range L, ind (Nat.Coprime L v) from Finset.sum_congr rfl (fun v _ => by
          rw [← ind_and]; exact ind_congr ((hcop v).trans Nat.coprime_comm)),
      sum_ind_eq_card, Nat.totient_eq_card_coprime]
  have hφ1 : (0 : ℝ) < Nat.totient r1 := by exact_mod_cast Nat.totient_pos.2 h1
  have hφ2 : (0 : ℝ) < Nat.totient r2 := by exact_mod_cast Nat.totient_pos.2 h2
  have hφg : (0 : ℝ) < Nat.totient g := by exact_mod_cast Nat.totient_pos.2 hg
  have hid : (Nat.totient L : ℝ) * Nat.totient g = Nat.totient r1 * Nat.totient r2 := by
    exact_mod_cast totient_lcm_mul_totient_gcd h1.ne' h2.ne'
  have expand : ∑ v ∈ range L, Xc r1 a1 v * Xc r2 a2 v =
      ∑ v ∈ range L, ind (v ≡ a1 [MOD r1]) * ind (v ≡ a2 [MOD r2]) -
        (∑ v ∈ range L, ind (v ≡ a1 [MOD r1]) * ind (Nat.Coprime v r2)) / Nat.totient r2 -
        (∑ v ∈ range L, ind (v ≡ a2 [MOD r2]) * ind (Nat.Coprime v r1)) / Nat.totient r1 +
        (∑ v ∈ range L, ind (Nat.Coprime v r1) * ind (Nat.Coprime v r2)) /
          (Nat.totient r1 * Nat.totient r2) := by
    simp only [Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    unfold Xc; ring
  have hg' : 1 / (Nat.totient g : ℝ) = Nat.totient L / (Nat.totient r1 * Nat.totient r2) := by
    rw [div_eq_div_iff hφg.ne' (by positivity), one_mul, ← hid]
  rw [expand, hA, hB, hC, hD, hg']
  field_simp
  ring

/-! ### Normalised version over a complete system modulo `q L` (`q = fl`) -/

/-- Lifting through one class modulo a coprime `q`: for `L`-periodic `F`,
`∑_{v < qL, v ≡ c (q)} F(v) = ∑_{u < L} F(u)`. -/
theorem sum_crt_lift {q L : ℕ} (hq : 0 < q) (hL : 0 < L) (hqL : Nat.Coprime q L) (c : ℕ)
    (F : ℕ → ℝ) (hF : ∀ v, F v = F (v % L)) :
    ∑ v ∈ (range (q * L)).filter (fun v => v ≡ c [MOD q]), F v = ∑ u ∈ range L, F u := by
  refine Finset.sum_nbij' (fun v => v % L) (fun u => (Nat.chineseRemainder hqL c u : ℕ))
    ?_ ?_ ?_ ?_ ?_
  · intro v _; simp only [Finset.mem_range]; exact Nat.mod_lt _ hL
  · intro u _
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.chineseRemainder_lt_mul hqL c u hq.ne' hL.ne',
      (Nat.chineseRemainder hqL c u).2.1⟩
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_range] at hv
    have h1 := (Nat.chineseRemainder hqL c (v % L)).2
    have h := (Nat.modEq_and_modEq_iff_modEq_mul hqL).1
      ⟨h1.1.trans hv.2.symm, h1.2.trans (Nat.mod_modEq v L)⟩
    unfold Nat.ModEq at h
    simp only
    rwa [Nat.mod_eq_of_lt (Nat.chineseRemainder_lt_mul hqL c _ hq.ne' hL.ne'),
      Nat.mod_eq_of_lt hv.1] at h
  · intro u hu
    simp only [Finset.mem_range] at hu
    have h2 := (Nat.chineseRemainder hqL c u).2.2
    simp only
    unfold Nat.ModEq at h2
    rw [h2, Nat.mod_eq_of_lt hu]
  · intro v _; exact hF v

theorem Xc_periodic {r a L : ℕ} (hrL : r ∣ L) (v : ℕ) : Xc r a v = Xc r a (v % L) := by
  have h : v % L ≡ v [MOD r] := Nat.ModEq.of_dvd hrL (Nat.mod_modEq v L)
  unfold Xc
  rw [ind_congr (show v ≡ a [MOD r] ↔ v % L ≡ a [MOD r] from ⟨h.trans, h.symm.trans⟩),
    ind_congr (show Nat.Coprime v r ↔ Nat.Coprime (v % L) r from
      (coprime_iff_of_modEq h).symm)]

/-- **§2.5, normalised form.**  Averaging over a complete residue system modulo
`fl[r₁,r₂]`, restricted to one class modulo `q = fl` (coprime to `[r₁,r₂]`):
`(1/(q[r₁,r₂])) ∑ X_{r₁}^{a₁} X_{r₂}^{a₂} = (1/(q[r₁,r₂])) (1_{a₁≡a₂ (g)} - 1/φ(g))`. -/
theorem zeroMode_covariance_full {f l r1 r2 : ℕ} (hf : 0 < f) (hl : 0 < l) (h1 : 0 < r1)
    (h2 : 0 < r2) (hcop : Nat.Coprime (f * l) (Nat.lcm r1 r2)) (c : ℕ) {a1 a2 : ℕ}
    (ha1 : Nat.Coprime a1 r1) (ha2 : Nat.Coprime a2 r2) :
    (1 / ((f * l * Nat.lcm r1 r2 : ℕ) : ℝ)) *
        ∑ v ∈ (range (f * l * Nat.lcm r1 r2)).filter (fun v => v ≡ c [MOD f * l]),
          Xc r1 a1 v * Xc r2 a2 v =
      (1 / ((f * l * Nat.lcm r1 r2 : ℕ) : ℝ)) *
        (ind (a1 ≡ a2 [MOD Nat.gcd r1 r2]) - 1 / (Nat.totient (Nat.gcd r1 r2) : ℝ)) := by
  rw [sum_crt_lift (Nat.mul_pos hf hl) (Nat.lcm_pos h1 h2) hcop c _
    (fun v => by
      rw [Xc_periodic (Nat.dvd_lcm_left r1 r2) v, Xc_periodic (Nat.dvd_lcm_right r1 r2) v]),
    zeroMode_covariance h1 h2 ha1 ha2]

end Erdos287.SourceChain
