import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V8 §2C: selected-window / rough-multiplier algebra

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Purely arithmetic / combinatorial pieces of the repaired window machinery, all kernel-proved:

* `rough_multiplier_unique` — if every prime factor of `t₁, t₂` exceeds `v`, `1 ≤ a₁, a₂ ≤ v`
  and `t₁ a₁ = t₂ a₂`, then `a₁ = a₂` and `t₁ = t₂`;
* `rough_supports_disjoint` — hence the supports `t • B` (`B ⊆ [1,v]`) are disjoint for distinct
  rough labels;
* `rough_labels_not_pairwise_coprime` — **firewall**: rough labels need *not* be pairwise coprime
  (`3` and `9` are both `2`-rough);
* `grid_glue_lcm` — gcd-aware rational-grid gluing: a sum of grid points of steps `1/d₁`, `1/d₂`
  lies on the grid of step `1/lcm(d₁,d₂)`;
* `lcm_not_product` — **firewall**: the shared denominator is the LCM, not the product;
* `grid_point_common_iff` / `common_grid_points_card` — endpoint-loss formula: of the `d₁+1`
  points `k/d₁ ∈ [0,1]`, exactly `gcd(d₁,d₂)+1` also lie on the `1/d₂` grid;
* `fresh_prime_lcm` — fresh-prime lifting: `lcm(D, p) = D p` when the prime `p ∤ D`.

External inputs (Croot reciprocal subset sums, sieve abundance of rough labels, mesoscopic ROW
theorem, asymptotic deletion) are **external interfaces** (`RoughLabelSupply`,
`LocalDeletionInput`), never inhabited.  The internal theorem `sharedGridOutput_of_inputs` is the
implication `RoughLabelSupply → LocalDeletionInput → SharedGridOutput`, with every premise
visible in its type.
-/

open scoped BigOperators

namespace Erdos287
namespace ResearchBankV8
namespace RoughWindow

/-! ## 1.  Rough multipliers -/

/-- `t` is `v`-rough: every prime factor of `t` exceeds `v`. -/
def Rough (v t : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ t → v < p

/-- A number in `[1, v]` is coprime to every `v`-rough number. -/
theorem coprime_of_rough {v t a : ℕ} (ht : Rough v t) (ha0 : 0 < a) (ha : a ≤ v) :
    Nat.Coprime a t := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra h
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h
  have hpa : p ∣ a := hpd.trans (Nat.gcd_dvd_left a t)
  have hpt : p ∣ t := hpd.trans (Nat.gcd_dvd_right a t)
  have hvp := ht p hp hpt
  have := Nat.le_of_dvd ha0 hpa
  omega

/-- **Rough multiplier uniqueness.** -/
theorem rough_multiplier_unique {v t₁ t₂ a₁ a₂ : ℕ} (h₁ : Rough v t₁) (h₂ : Rough v t₂)
    (ha₁ : 1 ≤ a₁) (ha₁v : a₁ ≤ v) (ha₂ : 1 ≤ a₂) (ha₂v : a₂ ≤ v)
    (heq : t₁ * a₁ = t₂ * a₂) : a₁ = a₂ ∧ t₁ = t₂ := by
  have c₁ : Nat.Coprime a₁ t₂ := coprime_of_rough h₂ ha₁ ha₁v
  have c₂ : Nat.Coprime a₂ t₁ := coprime_of_rough h₁ ha₂ ha₂v
  have d₁ : a₁ ∣ a₂ := c₁.dvd_of_dvd_mul_left ⟨t₁, by rw [← heq]; ring⟩
  have d₂ : a₂ ∣ a₁ := c₂.dvd_of_dvd_mul_left ⟨t₂, by rw [heq]; ring⟩
  have hae : a₁ = a₂ := Nat.dvd_antisymm d₁ d₂
  refine ⟨hae, ?_⟩
  subst hae
  exact Nat.eq_of_mul_eq_mul_right (by omega) heq

/-- The support `t · B` of a label `t` on a block `B`. -/
def support (t : ℕ) (B : Finset ℕ) : Finset ℕ := B.image fun a => t * a

/-- **Distinct rough labels have disjoint supports.** -/
theorem rough_supports_disjoint {v t₁ t₂ : ℕ} {B : Finset ℕ} (hB : ∀ a ∈ B, 1 ≤ a ∧ a ≤ v)
    (h₁ : Rough v t₁) (h₂ : Rough v t₂) (hne : t₁ ≠ t₂) :
    Disjoint (support t₁ B) (support t₂ B) := by
  rw [Finset.disjoint_left]
  intro n hn1 hn2
  simp only [support, Finset.mem_image] at hn1 hn2
  obtain ⟨a₁, ha₁, rfl⟩ := hn1
  obtain ⟨a₂, ha₂, he⟩ := hn2
  exact hne (rough_multiplier_unique h₁ h₂ (hB a₁ ha₁).1 (hB a₁ ha₁).2 (hB a₂ ha₂).1
    (hB a₂ ha₂).2 he.symm).2

/-- The map `a ↦ t a` is injective on `B` for `t > 0`, so `|t · B| = |B|`. -/
theorem support_card {t : ℕ} (ht : 0 < t) (B : Finset ℕ) : (support t B).card = B.card :=
  Finset.card_image_of_injective _ fun _ _ h => Nat.eq_of_mul_eq_mul_left ht h

/-- **Firewall: rough labels need not be pairwise coprime.** -/
theorem rough_labels_not_pairwise_coprime :
    ∃ v t₁ t₂ : ℕ, Rough v t₁ ∧ Rough v t₂ ∧ t₁ ≠ t₂ ∧ ¬ Nat.Coprime t₁ t₂ := by
  refine ⟨2, 3, 9, ?_, ?_, by decide, by decide⟩
  · intro p hp hd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd
    omega
  · intro p hp hd
    have h3 : p ∣ 3 ^ 2 := by simpa using hd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
    omega

/-- The (false) strengthening "distinct rough labels are coprime" is refuted. -/
theorem not_forall_rough_coprime :
    ¬ ∀ v t₁ t₂ : ℕ, Rough v t₁ → Rough v t₂ → t₁ ≠ t₂ → Nat.Coprime t₁ t₂ := by
  intro h
  obtain ⟨v, t₁, t₂, h₁, h₂, hne, hc⟩ := rough_labels_not_pairwise_coprime
  exact hc (h v t₁ t₂ h₁ h₂ hne)

/-! ## 2.  Gcd-aware rational-grid gluing -/

/-- `q` lies on the grid of step `1/d`. -/
def OnGrid (d : ℕ) (q : ℚ) : Prop := ∃ k : ℤ, q = k / d

/-- **Gluing uses the LCM.**  A sum of a `1/d₁`-grid point and a `1/d₂`-grid point lies on the
`1/lcm(d₁,d₂)` grid. -/
theorem grid_glue_lcm {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) {q₁ q₂ : ℚ}
    (hq₁ : OnGrid d₁ q₁) (hq₂ : OnGrid d₂ q₂) : OnGrid (Nat.lcm d₁ d₂) (q₁ + q₂) := by
  obtain ⟨k₁, rfl⟩ := hq₁
  obtain ⟨k₂, rfl⟩ := hq₂
  obtain ⟨u, hu⟩ := Nat.dvd_lcm_left d₁ d₂
  obtain ⟨w, hw⟩ := Nat.dvd_lcm_right d₁ d₂
  refine ⟨k₁ * u + k₂ * w, ?_⟩
  have hu0 : (u : ℚ) ≠ 0 := by
    intro h; simp at h; subst h; simp at hu; omega
  have hw0 : (w : ℚ) ≠ 0 := by
    intro h; simp at h; subst h; simp at hw; omega
  rw [hu] at *
  have hd₁ : (d₁ : ℚ) ≠ 0 := by positivity
  have hd₂ : (d₂ : ℚ) ≠ 0 := by positivity
  have hlw : ((d₁ * u : ℕ) : ℚ) = d₂ * w := by exact_mod_cast hw
  push_cast at hlw ⊢
  field_simp
  linear_combination (k₂ : ℚ) * hlw

/-- Grid-membership is preserved by coarsening to a multiple. -/
theorem onGrid_of_dvd {d e : ℕ} (hd : d ∣ e) (he : 0 < e) {q : ℚ} (hq : OnGrid d q) :
    OnGrid e q := by
  obtain ⟨k, rfl⟩ := hq
  obtain ⟨c, rfl⟩ := hd
  refine ⟨k * c, ?_⟩
  have hc : (c : ℚ) ≠ 0 := by intro h; simp at h; subst h; simp at he
  have hdd : (d : ℚ) ≠ 0 := by intro h; simp at h; subst h; simp at he
  push_cast; field_simp

/-- `lcm(d₁,d₂) · gcd(d₁,d₂) = d₁ d₂`. -/
theorem lcm_mul_gcd (d₁ d₂ : ℕ) : Nat.lcm d₁ d₂ * Nat.gcd d₁ d₂ = d₁ * d₂ := by
  rw [mul_comm]; exact Nat.gcd_mul_lcm d₁ d₂

/-- **Firewall: the shared denominator is the LCM, not the product.** -/
theorem lcm_not_product : Nat.lcm 4 6 = 12 ∧ 4 * 6 = 24 ∧ Nat.lcm 4 6 ≠ 4 * 6 := by decide

/-- A concrete gluing whose exact denominator is the LCM `12`, strictly below the product `24`. -/
theorem glue_example : (1 : ℚ) / 4 + 1 / 6 = 5 / 12 := by norm_num

/-- **Endpoint-loss formula, pointwise form.**  `k/d₁` lies on the `1/d₂` grid iff
`d₁ / gcd(d₁,d₂) ∣ k`. -/
theorem grid_point_common_iff {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) (k : ℕ) :
    (∃ j : ℕ, (k : ℚ) / d₁ = j / d₂) ↔ d₁ / Nat.gcd d₁ d₂ ∣ k := by
  set g := Nat.gcd d₁ d₂ with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ h₁
  obtain ⟨a, ha⟩ : g ∣ d₁ := Nat.gcd_dvd_left _ _
  obtain ⟨b, hb⟩ : g ∣ d₂ := Nat.gcd_dvd_right _ _
  have hcop : Nat.Coprime a b := by
    have := Nat.coprime_div_gcd_div_gcd (m := d₁) (n := d₂) hg0
    rw [← hg] at this
    rwa [ha, Nat.mul_div_cancel_left _ hg0, hb, Nat.mul_div_cancel_left _ hg0] at this
  have hda : d₁ / g = a := by rw [ha, Nat.mul_div_cancel_left _ hg0]
  rw [hda]
  have ha0 : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at ha; omega)
  have hb0 : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hb; omega)
  constructor
  · rintro ⟨j, hj⟩
    have : (k : ℚ) * d₂ = j * d₁ := by
      field_simp at hj; linarith
    have h' : k * b = j * a := by
      rw [ha, hb] at this
      have : ((k * b : ℕ) : ℚ) * g = ((j * a : ℕ) : ℚ) * g := by
        push_cast at this ⊢; linarith
      have hg' : (g : ℚ) ≠ 0 := by positivity
      exact_mod_cast mul_right_cancel₀ hg' this
    exact hcop.dvd_of_dvd_mul_right ⟨j, by rw [h']; ring⟩
  · rintro ⟨c, rfl⟩
    refine ⟨c * b, ?_⟩
    rw [ha, hb]
    push_cast
    have : (a : ℚ) ≠ 0 := by positivity
    have : (b : ℚ) ≠ 0 := by positivity
    have : (g : ℚ) ≠ 0 := by positivity
    field_simp

/-- **Endpoint-loss formula, counting form.**  Among the grid points `k/d₁`, `0 ≤ k ≤ d₁`, exactly
`gcd(d₁,d₂) + 1` lie on the `1/d₂` grid. -/
theorem common_grid_points_card {d₁ d₂ : ℕ} (h₁ : 0 < d₁) :
    ((Finset.range (d₁ + 1)).filter fun k => d₁ / Nat.gcd d₁ d₂ ∣ k).card =
      Nat.gcd d₁ d₂ + 1 := by
  set g := Nat.gcd d₁ d₂
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ h₁
  obtain ⟨a, ha⟩ : g ∣ d₁ := Nat.gcd_dvd_left _ _
  have hda : d₁ / g = a := by rw [ha, Nat.mul_div_cancel_left _ hg0]
  rw [hda]
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · simp [h] at ha; omega
    · exact h
  have : (Finset.range (d₁ + 1)).filter (fun k => a ∣ k) =
      (Finset.range (g + 1)).image fun c => a * c := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, c, rfl⟩
      refine ⟨c, ?_, rfl⟩
      by_contra hc
      have : a * (g + 1) ≤ a * c := Nat.mul_le_mul_left _ (by omega)
      rw [ha] at hk
      nlinarith
    · rintro ⟨c, hc, rfl⟩
      refine ⟨?_, dvd_mul_right _ _⟩
      rw [ha]
      have : a * c ≤ a * g := Nat.mul_le_mul_left _ (by omega)
      nlinarith
  rw [this, Finset.card_image_of_injective _ fun x y h => Nat.eq_of_mul_eq_mul_left ha0 h]
  simp

/-! ## 3.  Fresh-prime lifting -/

/-- **Fresh-prime lifting.**  If the prime `p` does not divide `D`, then `lcm(D, p) = D p`. -/
theorem fresh_prime_lcm {D p : ℕ} (hp : p.Prime) (hpD : ¬ p ∣ D) : Nat.lcm D p = D * p :=
  Nat.Coprime.lcm_eq_mul ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpD))

/-- Fresh-prime lifting, grid form: a fresh prime `p` contributes a genuinely new grid factor. -/
theorem fresh_prime_new_grid {D p : ℕ} (hp : p.Prime) (hpD : ¬ p ∣ D) (hD : 0 < D) :
    ¬ Nat.lcm D p ∣ D := by
  rw [fresh_prime_lcm hp hpD]
  intro h
  have := Nat.le_of_dvd hD h
  have := hp.two_le
  nlinarith

/-! ## 4.  External interfaces and the internal gluing implication -/

/-- **External interface (sieve abundance of rough labels) — never inhabited here.**  There are
`K` distinct `v`-rough labels in `[X, 2X]`. -/
def RoughLabelSupply (v X K : ℕ) : Prop :=
  ∃ T : Finset ℕ, T.card = K ∧ ∀ t ∈ T, Rough v t ∧ X ≤ t ∧ t ≤ 2 * X

/-- **External interface (Croot-type local deletion / reciprocal subset sums) — never inhabited
here.**  For every label `t` in `T`, there is a sub-block `S_t ⊆ B` whose reciprocal sum on the
support `t · S_t` equals a prescribed target `τ t`. -/
def LocalDeletionInput (B : Finset ℕ) (T : Finset ℕ) (τ : ℕ → ℚ) : Prop :=
  ∀ t ∈ T, ∃ S ⊆ B, ∑ a ∈ S, (1 : ℚ) / (t * a) = τ t

/-- The glued output: one set of denominators, a disjoint union of label supports, whose total
reciprocal sum is `∑_t τ t`. -/
def SharedGridOutput (T : Finset ℕ) (τ : ℕ → ℚ) : Prop :=
  ∃ D : Finset ℕ, ∑ n ∈ D, (1 : ℚ) / n = ∑ t ∈ T, τ t

/-- **Internal gluing theorem** (the analytic premises are explicit arguments):
`RoughLabelSupply → LocalDeletionInput → SharedGridOutput`.  The disjointness of the supports is
the kernel-proved rough multiplier uniqueness. -/
theorem sharedGridOutput_of_inputs {v X K : ℕ} (hX : 1 ≤ X) {B : Finset ℕ}
    (hB : ∀ a ∈ B, 1 ≤ a ∧ a ≤ v) {τ : ℕ → ℚ} (hsupply : RoughLabelSupply v X K)
    (hdel : ∀ T : Finset ℕ, (∀ t ∈ T, Rough v t ∧ X ≤ t ∧ t ≤ 2 * X) →
      LocalDeletionInput B T τ) :
    ∃ T : Finset ℕ, T.card = K ∧ SharedGridOutput T τ := by
  obtain ⟨T, hTK, hT⟩ := hsupply
  refine ⟨T, hTK, ?_⟩
  have hloc := hdel T hT
  choose! S hSB hS using hloc
  refine ⟨T.biUnion fun t => support t (S t), ?_⟩
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun t ht => ?_
    have ht0 : 0 < t := by have := (hT t ht).2.1; omega
    rw [← hS t ht, support, Finset.sum_image]
    · push_cast; rfl
    · intro a _ b _ h
      exact Nat.eq_of_mul_eq_mul_left ht0 h
  · intro t₁ ht₁ t₂ ht₂ hne
    exact Finset.disjoint_of_subset_left (Finset.image_subset_image (hSB t₁ ht₁))
      (Finset.disjoint_of_subset_right (Finset.image_subset_image (hSB t₂ ht₂))
        (rough_supports_disjoint hB (hT t₁ ht₁).1 (hT t₂ ht₂).1 hne))

end RoughWindow
end ResearchBankV8
end Erdos287
