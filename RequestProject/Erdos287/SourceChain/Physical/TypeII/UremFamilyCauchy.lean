import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilyResidue

/-!
# Erdős #287 — occupancy and the per-packet Cauchy step of the family Urem estimate

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

* `sum_occupancy_le` — (5.2): `m ↦ (c m̄ mod f, B (A m)⁻¹ mod l)` sends unit classes mod `f l`
  injectively to unit pairs, so each pair is hit at most `M/(f l) + 1` times in `[M, 2M)`;
* `urem_r_sq_le_relative_energy` — (5.3): for one packet and one `r`,
  `|∑_{l ∼ L} z_l ∑_{m ∼ M} β_m 1_{(m,flr)=1} Δ(f, c m̄, l, B(Am)⁻¹)|²
     ≤ (∑_l z_l²)(∑_m β_m²)(M/(fL) + 1) R_r(f)`
  where `R_r(f) = ∑_{l ∼ L, (f,l)=1} ∑*_{c'} ∑*_{a'} Δ(f,c',l,a')²` is the **relative energy**; it
  depends on the packet only through `f`.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII.UremFamily

open Erdos287.Physical.TypeII

lemma zmod_eq_of_mul_inv_eq {n : ℕ} {w u v : ZMod n} (hw : IsUnit w) (hu : IsUnit u)
    (hv : IsUnit v) (h : w * u⁻¹ = w * v⁻¹) : u = v := by
  have h1 : u⁻¹ = v⁻¹ := by
    have := congrArg (fun x => w⁻¹ * x) h
    simp only at this
    rwa [← mul_assoc, ← mul_assoc, ZMod.inv_mul_of_unit w hw, one_mul, one_mul] at this
  calc u = u * (v * v⁻¹) := by rw [ZMod.mul_inv_of_unit v hv, mul_one]
    _ = u * (v * u⁻¹) := by rw [h1]
    _ = v * (u * u⁻¹) := by ring
    _ = v := by rw [ZMod.mul_inv_of_unit u hu, mul_one]

lemma isUnit_int_of_coprime {l : ℕ} {B : ℤ} (h : Nat.Coprime B.natAbs l) : IsUnit (B : ZMod l) := by
  rcases Int.natAbs_eq B with e | e
  · rw [e, Int.cast_natCast]; exact (ZMod.isUnit_iff_coprime _ _).2 h
  · rw [e, Int.cast_neg, Int.cast_natCast]; exact ((ZMod.isUnit_iff_coprime _ _).2 h).neg

lemma isUnit_inv_of_isUnit {n : ℕ} {u : ZMod n} (hu : IsUnit u) : IsUnit u⁻¹ :=
  IsUnit.of_mul_eq_one_right u (ZMod.mul_inv_of_unit u hu)

lemma coprime_val_of_isUnit {n : ℕ} [NeZero n] {x : ZMod n} (h : IsUnit x) :
    Nat.Coprime n x.val := by
  rw [Nat.coprime_comm, ← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]; exact h

/-- The residue pair map lands in unit pairs. -/
lemma resPair_mem {f c l A m : ℕ} {B : ℤ} (hf : 0 < f) (hl : 0 < l) (hcf : Nat.Coprime c f)
    (hAB : Nat.Coprime (A * B.natAbs) l) (hm : Nat.Coprime m (f * l)) :
    (cRes f c m, aRes l A B m) ∈ units f ×ˢ units l := by
  haveI : NeZero f := ⟨hf.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  rw [Nat.coprime_mul_iff_right] at hm
  have hA : Nat.Coprime A l := Nat.Coprime.coprime_mul_right hAB
  have hBn : Nat.Coprime B.natAbs l := Nat.Coprime.coprime_mul_left hAB
  simp only [mem_product, units, mem_filter, mem_range, cRes, aRes]
  refine ⟨⟨ZMod.val_lt _, coprime_val_of_isUnit ?_⟩, ⟨ZMod.val_lt _, coprime_val_of_isUnit ?_⟩⟩
  · exact ((ZMod.isUnit_iff_coprime c f).2 hcf).mul
      (isUnit_inv_of_isUnit ((ZMod.isUnit_iff_coprime m f).2 hm.1))
  · exact (isUnit_int_of_coprime hBn).mul
      (isUnit_inv_of_isUnit ((ZMod.isUnit_iff_coprime _ l).2 (Nat.Coprime.mul_left hA hm.2)))

/-- Equal residue pairs force congruence modulo `f l`. -/
lemma modEq_of_resPair_eq {f c l A m m' : ℕ} {B : ℤ} (hf : 0 < f) (hl : 0 < l)
    (hfl : Nat.Coprime f l) (hcf : Nat.Coprime c f) (hAB : Nat.Coprime (A * B.natAbs) l)
    (hm : Nat.Coprime m (f * l)) (hm' : Nat.Coprime m' (f * l))
    (h1 : cRes f c m = cRes f c m') (h2 : aRes l A B m = aRes l A B m') :
    m ≡ m' [MOD f * l] := by
  haveI : NeZero f := ⟨hf.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  rw [Nat.coprime_mul_iff_right] at hm hm'
  have hA : Nat.Coprime A l := Nat.Coprime.coprime_mul_right hAB
  have hBn : Nat.Coprime B.natAbs l := Nat.Coprime.coprime_mul_left hAB
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hfl]
  constructor
  · rw [← ZMod.natCast_eq_natCast_iff]
    exact zmod_eq_of_mul_inv_eq ((ZMod.isUnit_iff_coprime c f).2 hcf)
      ((ZMod.isUnit_iff_coprime m f).2 hm.1) ((ZMod.isUnit_iff_coprime m' f).2 hm'.1)
      (ZMod.val_injective f h1)
  · rw [← ZMod.natCast_eq_natCast_iff]
    have e := zmod_eq_of_mul_inv_eq (isUnit_int_of_coprime hBn)
      ((ZMod.isUnit_iff_coprime _ l).2 (Nat.Coprime.mul_left hA hm.2))
      ((ZMod.isUnit_iff_coprime _ l).2 (Nat.Coprime.mul_left hA hm'.2))
      (ZMod.val_injective l h2)
    push_cast at e
    have hAu := (ZMod.isUnit_iff_coprime A l).2 hA
    have := congrArg (fun x => (A : ZMod l)⁻¹ * x) e
    simp only at this
    rwa [← mul_assoc, ← mul_assoc, ZMod.inv_mul_of_unit _ hAu, one_mul, one_mul] at this

/-- **(5.2) Occupancy of the residue-pair map.** -/
theorem sum_occupancy_le {f c l A : ℕ} {B : ℤ} (hf : 0 < f) (hl : 0 < l)
    (hfl : Nat.Coprime f l) (hcf : Nat.Coprime c f) (hAB : Nat.Coprime (A * B.natAbs) l)
    (g : ℕ → ℕ → ℝ) (hg : ∀ x y, 0 ≤ g x y) (M : ℕ) :
    ∑ m ∈ Ico M (2 * M), copInd m (f * l) * g (cRes f c m) (aRes l A B m) ≤
      ((M : ℝ) / (f * l : ℕ) + 1) * ∑ c' ∈ units f, ∑ a' ∈ units l, g c' a' := by
  set S := (Ico M (2 * M)).filter (fun m => Nat.Coprime m (f * l)) with hS
  have hL : ∑ m ∈ Ico M (2 * M), copInd m (f * l) * g (cRes f c m) (aRes l A B m) =
      ∑ m ∈ S, g (cRes f c m) (aRes l A B m) := by
    rw [hS, sum_filter]
    refine sum_congr rfl (fun m _ => ?_)
    unfold copInd; split_ifs <;> simp
  rw [hL]
  set φ : ℕ → ℕ × ℕ := fun m => (cRes f c m, aRes l A B m) with hφ
  have hmaps : ∀ m ∈ S, φ m ∈ units f ×ˢ units l := by
    intro m hm
    rw [hS, mem_filter] at hm
    exact resPair_mem hf hl hcf hAB hm.2
  rw [← sum_fiberwise_of_maps_to hmaps, ← sum_product']
  rw [mul_sum]
  refine sum_le_sum (fun p hp => ?_)
  have hfib : ∑ m ∈ S with φ m = p, g (cRes f c m) (aRes l A B m) =
      ((S.filter (fun m => φ m = p)).card : ℝ) * g p.1 p.2 := by
    rw [← nsmul_eq_mul, ← sum_const]
    refine sum_congr rfl (fun m hm => ?_)
    rw [mem_filter] at hm
    have := hm.2
    simp only [hφ] at this
    rw [← this]
  rw [hfib]
  refine mul_le_mul_of_nonneg_right ?_ (hg _ _)
  rcases (S.filter (fun m => φ m = p)).eq_empty_or_nonempty with he | ⟨m0, hm0⟩
  · rw [he, card_empty, Nat.cast_zero]; positivity
  · have hsub : S.filter (fun m => φ m = p) ⊆
        (Ico M (2 * M)).filter (fun m => m ≡ m0 [MOD f * l]) := by
      intro m hm
      rw [mem_filter] at hm hm0 ⊢
      rw [hS, mem_filter] at hm hm0
      refine ⟨hm.1.1, ?_⟩
      have e : φ m = φ m0 := hm.2.trans hm0.2.symm
      simp only [hφ, Prod.mk.injEq] at e
      exact modEq_of_resPair_eq hf hl hfl hcf hAB hm.1.2 hm0.1.2 e.1 e.2
    calc ((S.filter (fun m => φ m = p)).card : ℝ)
        ≤ (((Ico M (2 * M)).filter (fun m => m ≡ m0 [MOD f * l])).card : ℝ) := by
          exact_mod_cast card_le_card hsub
      _ ≤ (M : ℝ) / (f * l : ℕ) + 1 := count_Ico_modEq_le _ _ _

/-- The relative energy `R_r(f) = ∑_{l ∼ L, (f,l)=1} ∑*_{c' mod f} ∑*_{a' mod l} Δ^{f,c'}_ρ(l,a')²`. -/
noncomputable def relEnergy (I : Finset ℕ) (ρ : ℕ → ℝ) (f L : ℕ) : ℝ :=
  ∑ l ∈ (Ico L (2 * L)).filter (Nat.Coprime f),
    ∑ c' ∈ units f, ∑ a' ∈ units l, relDisc I ρ f c' l a' ^ 2

lemma relEnergy_nonneg (I : Finset ℕ) (ρ : ℕ → ℝ) (f L : ℕ) : 0 ≤ relEnergy I ρ f L := by
  unfold relEnergy; positivity

/-- One row of the Cauchy step: the `m`-sum of squared relative discrepancies at the packet's
residue pair, for one `l`. -/
lemma row_le {I : Finset ℕ} {ρ : ℕ → ℝ} {f c l A L r M : ℕ} {B : ℤ} (hf : 0 < f) (hL : 0 < L)
    (hLl : L ≤ l) (hfl : Nat.Coprime f l) (hcf : Nat.Coprime c f)
    (hAB : Nat.Coprime (A * B.natAbs) l) :
    ∑ m ∈ Ico M (2 * M), (copInd m (f * l * r) *
        relDisc I ρ f (cRes f c m) l (aRes l A B m)) ^ 2 ≤
      ((M : ℝ) / (f * L) + 1) * ∑ c' ∈ units f, ∑ a' ∈ units l, relDisc I ρ f c' l a' ^ 2 := by
  have hl : 0 < l := lt_of_lt_of_le hL hLl
  have h1 : ∀ m ∈ Ico M (2 * M), (copInd m (f * l * r) *
        relDisc I ρ f (cRes f c m) l (aRes l A B m)) ^ 2 ≤
      copInd m (f * l) * (fun x y => relDisc I ρ f x l y ^ 2) (cRes f c m) (aRes l A B m) := by
    intro m _
    simp only
    unfold copInd
    rw [mul_pow]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd (Nat.Coprime.coprime_mul_right_right h1) h2
    · simp; positivity
    · simp
  refine (sum_le_sum h1).trans ?_
  refine (sum_occupancy_le hf hl hfl hcf hAB (fun x y => relDisc I ρ f x l y ^ 2)
    (fun _ _ => sq_nonneg _) M).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have : (M : ℝ) / ((f * l : ℕ) : ℝ) ≤ (M : ℝ) / (f * L) := by
    push_cast
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
    · have : (0 : ℝ) < f := by exact_mod_cast hf
      have : (0 : ℝ) < L := by exact_mod_cast hL
      positivity
    · have : (L : ℝ) ≤ l := by exact_mod_cast hLl
      have : (0 : ℝ) ≤ f := by positivity
      nlinarith
  linarith

/-- **(5.3) Per-packet Cauchy step for one `r`.** -/
theorem urem_r_sq_le_relative_energy (I : Finset ℕ) (ρ : ℕ → ℝ) {f c A L M r : ℕ} {B : ℤ}
    (hf : 0 < f) (hL : 0 < L) (hcf : Nat.Coprime c f) (z β : ℕ → ℝ)
    (hz : ∀ l, z l ≠ 0 → Nat.Coprime f l ∧ Nat.Coprime (A * B.natAbs) l) :
    (∑ l ∈ Ico L (2 * L), z l * ∑ m ∈ Ico M (2 * M), β m * copInd m (f * l * r) *
        relDisc I ρ f (cRes f c m) l (aRes l A B m)) ^ 2 ≤
      (∑ l ∈ Ico L (2 * L), z l ^ 2) * (∑ m ∈ Ico M (2 * M), β m ^ 2) *
        ((M : ℝ) / (f * L) + 1) * relEnergy I ρ f L := by
  set b : ℕ × ℕ → ℝ := fun p => if z p.1 = 0 then 0 else
    copInd p.2 (f * p.1 * r) * relDisc I ρ f (cRes f c p.2) p.1 (aRes p.1 A B p.2) with hb
  have eL : ∑ l ∈ Ico L (2 * L), z l * ∑ m ∈ Ico M (2 * M), β m * copInd m (f * l * r) *
        relDisc I ρ f (cRes f c m) l (aRes l A B m) =
      ∑ p ∈ Ico L (2 * L) ×ˢ Ico M (2 * M), (z p.1 * β p.2) * b p := by
    rw [sum_product]
    refine sum_congr rfl (fun l _ => ?_)
    rw [mul_sum]
    refine sum_congr rfl (fun m _ => ?_)
    simp only [hb]
    split_ifs with h
    · simp [h]
    · ring
  rw [eL]
  refine (sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
  have e1 : ∑ p ∈ Ico L (2 * L) ×ˢ Ico M (2 * M), (z p.1 * β p.2) ^ 2 =
      (∑ l ∈ Ico L (2 * L), z l ^ 2) * (∑ m ∈ Ico M (2 * M), β m ^ 2) := by
    rw [sum_product, sum_mul_sum]
    refine sum_congr rfl (fun l _ => sum_congr rfl (fun m _ => ?_))
    ring
  have e2 : ∑ p ∈ Ico L (2 * L) ×ˢ Ico M (2 * M), b p ^ 2 ≤
      ((M : ℝ) / (f * L) + 1) * relEnergy I ρ f L := by
    rw [sum_product]
    unfold relEnergy
    rw [sum_filter, mul_sum]
    refine sum_le_sum (fun l hl => ?_)
    by_cases hzl : z l = 0
    · simp only [hb, hzl, if_true]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero]
      have : (0 : ℝ) ≤ (M : ℝ) / (f * L) + 1 := by positivity
      split_ifs
      · positivity
      · simp
    · obtain ⟨h1, h2⟩ := hz l hzl
      simp only [hb, hzl, if_false, if_pos h1]
      exact row_le hf hL (mem_Ico.1 hl).1 h1 hcf h2
  rw [e1]
  calc (∑ l ∈ Ico L (2 * L), z l ^ 2) * (∑ m ∈ Ico M (2 * M), β m ^ 2) *
        ∑ p ∈ Ico L (2 * L) ×ˢ Ico M (2 * M), b p ^ 2
      ≤ (∑ l ∈ Ico L (2 * L), z l ^ 2) * (∑ m ∈ Ico M (2 * M), β m ^ 2) *
        (((M : ℝ) / (f * L) + 1) * relEnergy I ρ f L) :=
        mul_le_mul_of_nonneg_left e2 (by positivity)
    _ = _ := by ring

end Erdos287.Physical.TypeII.UremFamily
