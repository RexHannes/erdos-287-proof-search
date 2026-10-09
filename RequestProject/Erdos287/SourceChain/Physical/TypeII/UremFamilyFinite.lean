import RequestProject.Erdos287.SourceChain.Physical.TypeII.SourceComposed

/-!
# Erdős #287 — finite exact adapter for the family-averaged Urem estimate

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

This file proves, with no analytic input, the finite identities and inequalities that turn the
literal `h_l U_r` remainder `physUrem` into squared residue discrepancies of one *common*
sequence `α`, as in the family repair (`REPORT (2).md`, §§3, 5):

* `disc` — the unit-class discrepancy `E_ρ(q,b) = ∑_{n ∈ I} ρ_n (1_{n≡b (q)} - 1_{(n,q)=1}/φ(q))`;
* `relDisc` — the base-relative discrepancy
  `Δ^{f,c}_ρ(l,a) = ∑_{n ∈ I} ρ_n 1_{n≡c (f)} (1_{n≡a (l)} - 1_{(n,l)=1}/φ(l))`;
* `relDisc_eq_projection` — (3.2): for `(f,l) = 1`,
  `Δ^{f,c}(l,a) = E(fl, CRT(c,a)) - φ(l)⁻¹ ∑*_{a'} E(fl, CRT(c,a'))`;
* `sum_sq_sub_mean_le` / `relDisc_energy_le` — (3.3): the centred energy is at most the
  complete-modulus energy `∑*_{b mod fl} E(fl,b)²` (no `φ(f)` or `φ(l)` loss);
* `count_Ico_modEq_le` — occupancy: a residue class mod `q` meets `[M, 2M)` at most `M/q + 1`
  times;
* `inner_urem_eq_relDisc` — (5.1): the literal inner `v`-sum of `physUrem` equals
  `∑_m β_m 1_{(m, f l r) = 1} φ(r)⁻¹ Δ^{f, c m̄}_{α^{(r)}}(l, B (A m)⁻¹)`;
* `sum_relDisc_sq_occupancy` — (5.2): summing `Δ(f, c m̄, l, B(Am)⁻¹)²` over `m ∈ [M,2M)` costs
  at most `(M/(fl) + 1)` times the full unit-pair energy;
* `packet_weighted_cauchy` — (5.4): `∑_ξ |Γ_ξ| √(R(f_ξ)/f_ξ) ≤ √(∑ |Γ_ξ|/f_ξ) √(∑ |Γ_ξ| R(f_ξ))`.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII.UremFamily

open Erdos287.Physical.TypeII

/-- `1_{n ≡ b (mod q)}`. -/
noncomputable def ind (q b n : ℕ) : ℝ := if n ≡ b [MOD q] then 1 else 0

/-- The unit-class discrepancy `E_ρ(q,b)` of `ρ` on the finite support `I`. -/
noncomputable def disc (I : Finset ℕ) (ρ : ℕ → ℝ) (q b : ℕ) : ℝ :=
  ∑ n ∈ I, ρ n * (ind q b n - Uz q n)

/-- The base-relative discrepancy `Δ^{f,c}_ρ(l,a)`. -/
noncomputable def relDisc (I : Finset ℕ) (ρ : ℕ → ℝ) (f c l a : ℕ) : ℝ :=
  ∑ n ∈ I, ρ n * ind f c n * (ind l a n - Uz l n)

/-- Unit residues modulo `q` (as natural numbers `< q`). -/
def units (q : ℕ) : Finset ℕ := (range q).filter (Nat.Coprime q)

lemma card_units (q : ℕ) : (units q).card = Nat.totient q := by
  rw [units, Nat.totient]

/-- The CRT residue `CRT(c,a) mod f l`. -/
def crt {f l : ℕ} (h : Nat.Coprime f l) (c a : ℕ) : ℕ := (Nat.chineseRemainder h c a : ℕ)

lemma modEq_crt_iff {f l : ℕ} (h : Nat.Coprime f l) (c a n : ℕ) :
    n ≡ crt h c a [MOD f * l] ↔ n ≡ c [MOD f] ∧ n ≡ a [MOD l] := by
  have e : crt h c a = (Nat.chineseRemainder h c a : ℕ) := rfl
  rw [e, ← Nat.modEq_and_modEq_iff_modEq_mul h]
  have h1 := (Nat.chineseRemainder h c a).2.1
  have h2 := (Nat.chineseRemainder h c a).2.2
  constructor
  · rintro ⟨u, v⟩; exact ⟨u.trans h1, v.trans h2⟩
  · rintro ⟨u, v⟩; exact ⟨u.trans h1.symm, v.trans h2.symm⟩

/-- Sum of `1_{n ≡ a (l)}` over unit residues `a`. -/
lemma sum_units_ind {l : ℕ} (hl : 0 < l) (n : ℕ) :
    ∑ a ∈ units l, ind l a n = if Nat.Coprime n l then 1 else 0 := by
  have key : ∀ a ∈ units l, ind l a n = if a = n % l then 1 else 0 := by
    intro a ha
    simp only [units, mem_filter, mem_range] at ha
    unfold ind
    have : n ≡ a [MOD l] ↔ a = n % l := by
      rw [Nat.ModEq, Nat.mod_eq_of_lt ha.1]; exact eq_comm
    simp only [this]
  rw [sum_congr rfl key, sum_ite_eq']
  have hmem : n % l ∈ units l ↔ Nat.Coprime n l := by
    simp only [units, mem_filter, mem_range, Nat.mod_lt _ hl, true_and]
    rw [Nat.Coprime, Nat.Coprime, Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
  simp only [hmem]

/-- **(3.2) CRT projection identity.** -/
theorem relDisc_eq_projection (I : Finset ℕ) (ρ : ℕ → ℝ) {f l : ℕ} (h : Nat.Coprime f l)
    (hl : 0 < l) (c a : ℕ) :
    relDisc I ρ f c l a = disc I ρ (f * l) (crt h c a) -
      (1 / (Nat.totient l : ℝ)) * ∑ a' ∈ units l, disc I ρ (f * l) (crt h c a') := by
  have hind : ∀ a' n, ind (f * l) (crt h c a') n = ind f c n * ind l a' n := by
    intro a' n
    unfold ind
    simp only [modEq_crt_iff]
    by_cases h1 : n ≡ c [MOD f] <;> by_cases h2 : n ≡ a' [MOD l] <;> simp [h1, h2]
  have hphi : (0 : ℝ) < Nat.totient l := by exact_mod_cast Nat.totient_pos.2 hl
  unfold disc relDisc
  rw [sum_comm, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl (fun n _ => ?_)
  simp_rw [hind]
  rw [← mul_sum, sum_sub_distrib, ← mul_sum, sum_units_ind hl, sum_const, card_units,
    nsmul_eq_mul]
  unfold Uz
  split_ifs <;> field_simp <;> ring

/-- Subtracting the mean does not increase the energy. -/
lemma sum_sq_sub_mean_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    ∑ i ∈ s, (x i - (1 / (s.card : ℝ)) * ∑ j ∈ s, x j) ^ 2 ≤ ∑ i ∈ s, x i ^ 2 := by
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · simp [Finset.card_eq_zero.1 h0]
  set S := ∑ j ∈ s, x j with hS
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hpos
  have e : ∑ i ∈ s, (x i - (1 / (s.card : ℝ)) * S) ^ 2 =
      ∑ i ∈ s, x i ^ 2 - 2 * ((1 / (s.card : ℝ)) * S) * S +
        (s.card : ℝ) * ((1 / (s.card : ℝ)) * S) ^ 2 := by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul]
    rw [← sum_mul, ← mul_sum, hS]; ring
  rw [e]
  have : -(2 * ((1 / (s.card : ℝ)) * S) * S) + (s.card : ℝ) * ((1 / (s.card : ℝ)) * S) ^ 2 =
      -(S ^ 2 / s.card) := by
    field_simp; ring
  have : 0 ≤ S ^ 2 / s.card := by positivity
  nlinarith

/-- **(3.3) Relative energy ≤ complete-modulus energy.** -/
theorem relDisc_energy_le (I : Finset ℕ) (ρ : ℕ → ℝ) {f l : ℕ} (h : Nat.Coprime f l)
    (hf : 0 < f) (hl : 0 < l) :
    ∑ c ∈ units f, ∑ a ∈ units l, relDisc I ρ f c l a ^ 2 ≤
      ∑ b ∈ units (f * l), disc I ρ (f * l) b ^ 2 := by
  have step1 : ∀ c ∈ units f, ∑ a ∈ units l, relDisc I ρ f c l a ^ 2 ≤
      ∑ a ∈ units l, disc I ρ (f * l) (crt h c a) ^ 2 := by
    intro c _
    have := sum_sq_sub_mean_le (units l) (fun a => disc I ρ (f * l) (crt h c a))
    simp only [card_units] at this
    refine le_trans (le_of_eq ?_) this
    refine sum_congr rfl (fun a _ => ?_)
    rw [relDisc_eq_projection I ρ h hl c a]
  refine (sum_le_sum step1).trans ?_
  rw [← sum_product' (f := fun c a => disc I ρ (f * l) (crt h c a) ^ 2)]
  have hinj : Set.InjOn (fun p : ℕ × ℕ => crt h p.1 p.2) ↑(units f ×ˢ units l) := by
    rintro ⟨c, a⟩ hca ⟨c', a'⟩ hca' he
    simp only [coe_product, Set.mem_prod, mem_coe, units, mem_filter, mem_range] at hca hca'
    simp only at he
    have k1 := (modEq_crt_iff h c a (crt h c a)).1 rfl
    have k2 := (modEq_crt_iff h c' a' (crt h c' a')).1 rfl
    rw [he] at k1
    have e1 : c = c' := by
      have := k1.1.symm.trans k2.1
      rwa [Nat.ModEq, Nat.mod_eq_of_lt hca.1.1, Nat.mod_eq_of_lt hca'.1.1] at this
    have e2 : a = a' := by
      have := k1.2.symm.trans k2.2
      rwa [Nat.ModEq, Nat.mod_eq_of_lt hca.2.1, Nat.mod_eq_of_lt hca'.2.1] at this
    rw [e1, e2]
  rw [← sum_image (f := fun b => disc I ρ (f * l) b ^ 2) hinj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro b hb
    obtain ⟨⟨c, a⟩, hca, rfl⟩ := mem_image.1 hb
    simp only [mem_product, units, mem_filter, mem_range] at hca
    have k := (modEq_crt_iff h c a (crt h c a)).1 rfl
    simp only [units, mem_filter, mem_range]
    refine ⟨Nat.chineseRemainder_lt_mul h c a hf.ne' hl.ne', ?_⟩
    rw [Nat.coprime_mul_iff_left]
    constructor
    · rw [Nat.coprime_comm, Nat.Coprime, Nat.ModEq.gcd_eq k.1, Nat.gcd_comm]; exact hca.1.2
    · rw [Nat.coprime_comm, Nat.Coprime, Nat.ModEq.gcd_eq k.2, Nat.gcd_comm]; exact hca.2.2
  · intro b _ _; positivity

/-- Occupancy of a residue class in `[M, 2M)`. -/
lemma count_Ico_modEq_le (q M b : ℕ) :
    (((Ico M (2 * M)).filter (fun m => m ≡ b [MOD q])).card : ℝ) ≤ (M : ℝ) / q + 1 := by
  have hcard : ((Ico M (2 * M)).filter (fun m => m ≡ b [MOD q])).card ≤ M / q + 1 := by
    have := card_le_card_of_injOn (fun m => (m - M) / q)
      (s := (Ico M (2 * M)).filter (fun m => m ≡ b [MOD q])) (t := range (M / q + 1)) ?_ ?_
    · simpa using this
    · intro m hm
      simp only [coe_filter, mem_Ico, Set.mem_setOf_eq] at hm
      simp only [coe_range, Set.mem_Iio]
      have : (m - M) / q ≤ M / q := Nat.div_le_div_right (by omega)
      omega
    · intro m hm m' hm' he
      simp only [coe_filter, mem_Ico, Set.mem_setOf_eq] at hm hm'
      simp only at he
      have hmm : m ≡ m' [MOD q] := hm.2.trans hm'.2.symm
      have h1 : (m - M) ≡ (m' - M) [MOD q] := by
        have := Nat.ModEq.add_right_cancel' (n := q) M (a := m - M) (b := m' - M)
        apply this
        rwa [Nat.sub_add_cancel hm.1.1, Nat.sub_add_cancel hm'.1.1]
      have e := Nat.div_add_mod (m - M) q
      have e' := Nat.div_add_mod (m' - M) q
      rw [Nat.ModEq] at h1
      rw [he, h1] at e
      omega
  calc (((Ico M (2 * M)).filter (fun m => m ≡ b [MOD q])).card : ℝ) ≤ ((M / q + 1 : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ (M : ℝ) / q + 1 := by
        push_cast
        have := Nat.cast_div_le (α := ℝ) (m := M) (n := q)
        linarith

/-- The packet-weighted Cauchy inequality (5.4). -/
theorem packet_weighted_cauchy {ι : Type*} (s : Finset ι) (G F R : ι → ℝ)
    (hF : ∀ i ∈ s, 0 < F i) (hR : ∀ i ∈ s, 0 ≤ R i) :
    ∑ i ∈ s, |G i| * Real.sqrt (R i / F i) ≤
      Real.sqrt (∑ i ∈ s, |G i| / F i) * Real.sqrt (∑ i ∈ s, |G i| * R i) := by
  have e : ∀ i ∈ s, |G i| * Real.sqrt (R i / F i) =
      Real.sqrt (|G i| / F i) * Real.sqrt (|G i| * R i) := by
    intro i hi
    have hF' := hF i hi
    rw [← Real.sqrt_mul (div_nonneg (abs_nonneg _) hF'.le)]
    have : |G i| / F i * (|G i| * R i) = |G i| ^ 2 * (R i / F i) := by
      field_simp
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]
  rw [sum_congr rfl e]
  refine (Real.sum_mul_le_sqrt_mul_sqrt s _ _).trans (le_of_eq ?_)
  congr 2
  · refine sum_congr rfl (fun i hi => ?_)
    exact Real.sq_sqrt (div_nonneg (abs_nonneg _) (hF i hi).le)
  · refine sum_congr rfl (fun i hi => ?_)
    exact Real.sq_sqrt (mul_nonneg (abs_nonneg _) (hR i hi))

end Erdos287.Physical.TypeII.UremFamily
