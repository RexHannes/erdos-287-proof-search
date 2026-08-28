import Mathlib
import RequestProject.Erdos287.Exponent3221Ledger

/-!
# V17, Phase D — the `(e,h)` no-wrap sector and a **hostile audit** of the ratio-fibre energy

`3221-EH-NOWRAP-ENERGY45`.

## §12–§13.  Modular collision and integer rigidity

* `ratio_eq_iff_cross` — on a genuine unit sector, `h₁ e₁^{-1} = h₂ e₂^{-1}` **iff**
  `h₁ e₂ = h₂ e₁`; every inverse-domain hypothesis is explicit (the `e`'s are units).
* `nowrap_eq_of_dvd_of_abs_lt` — the generic integer rigidity: a multiple of `q` of absolute
  value `< |q|` vanishes.  This is *not* inferred from exponent inequalities; the literal
  size hypothesis is a hypothesis.
* The exponent capacity `E H = X^{16/35} < X^{21/35} = Q` with margin `1/7` is banked
  separately in `Erdos287.Ledger3221` and is **only** a capacity statement.

## §14.  Hostile audit of `3221-EH-NOWRAP-ENERGY45`

The Pro run claims `∑_λ |∑_{h e^{-1} = λ} a_e b_h|² ≪ E H X^{o(1)}`.  It is *not* banked as
stated.  Instead the collision quadruples are counted honestly:

* `ratioCollision_samePrime` — for `e₁ = e₂` the relation forces `h₁ = h₂`;
* `ratioCollision_distinctPrimes_param` — for distinct primes `e₁ ≠ e₂` coprimality forces
  `h₁ = c e₁`, `h₂ = c e₂` for a common integer `c`;
* `ratioCollision_card_bound` — hence

  `#{collisions} ≤ #E · #H + (#E)² · #C`,  `C = [-H_max/E_min, H_max/E_min]`;

* `ehRatioEnergy_bound` / `ehRatioEnergy_le_explicit` — the energy is at most the collision
  count, hence at most `#E · #H + (#E)² · #C`.

**Audit verdict.**  With `E = X^{1/7}`, `H = X^{11/35}` one has `#C ≈ H/E`, so the second
term is `≈ #E · H`, and the total is of the claimed order `E H` — with **no** divisor factor
and **no** `X^{o(1)}` loss.  The claim is therefore *confirmed in the finite form proved
here*, but only **conditionally on the no-wrap hypothesis** `|h₁e₂ - h₂e₁| < |q|`, which is
a literal size hypothesis of every statement below and is nowhere derived from the exponent
ledger.  Status: `CONDITIONAL_FINITE`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace Erdos287
namespace EHNoWrap3221

/-! ## §12. The modular collision criterion -/

/-- **Modular collision.**  On a unit sector, `h₁ e₁^{-1} = h₂ e₂^{-1}` iff
`h₁ e₂ = h₂ e₁`.  Stated in an arbitrary commutative ring with the `e`'s literal units, so
no inverse is ever formed outside its domain. -/
theorem ratio_eq_iff_cross {R : Type*} [CommRing R] (h1 h2 : R) (u1 u2 : Rˣ) :
    h1 * ((u1⁻¹ : Rˣ) : R) = h2 * ((u2⁻¹ : Rˣ) : R) ↔ h1 * (u2 : R) = h2 * (u1 : R) := by
  have i1 : ((u1⁻¹ : Rˣ) : R) * (u1 : R) = 1 := u1.inv_mul
  have i2 : ((u2⁻¹ : Rˣ) : R) * (u2 : R) = 1 := u2.inv_mul
  have k1 : (h1 * ((u1⁻¹ : Rˣ) : R)) * ((u1 : R) * (u2 : R)) = h1 * (u2 : R) := by
    calc (h1 * ((u1⁻¹ : Rˣ) : R)) * ((u1 : R) * (u2 : R))
        = h1 * (((u1⁻¹ : Rˣ) : R) * (u1 : R)) * (u2 : R) := by ring
      _ = h1 * (u2 : R) := by rw [i1]; ring
  have k2 : (h2 * ((u2⁻¹ : Rˣ) : R)) * ((u1 : R) * (u2 : R)) = h2 * (u1 : R) := by
    calc (h2 * ((u2⁻¹ : Rˣ) : R)) * ((u1 : R) * (u2 : R))
        = h2 * (((u2⁻¹ : Rˣ) : R) * (u2 : R)) * (u1 : R) := by ring
      _ = h2 * (u1 : R) := by rw [i2]; ring
  have k3 : (h1 * (u2 : R)) * (((u1⁻¹ : Rˣ) : R) * ((u2⁻¹ : Rˣ) : R))
      = h1 * ((u1⁻¹ : Rˣ) : R) := by
    calc (h1 * (u2 : R)) * (((u1⁻¹ : Rˣ) : R) * ((u2⁻¹ : Rˣ) : R))
        = h1 * ((u2 : R) * ((u2⁻¹ : Rˣ) : R)) * ((u1⁻¹ : Rˣ) : R) := by ring
      _ = h1 * ((u1⁻¹ : Rˣ) : R) := by rw [u2.mul_inv]; ring
  have k4 : (h2 * (u1 : R)) * (((u1⁻¹ : Rˣ) : R) * ((u2⁻¹ : Rˣ) : R))
      = h2 * ((u2⁻¹ : Rˣ) : R) := by
    calc (h2 * (u1 : R)) * (((u1⁻¹ : Rˣ) : R) * ((u2⁻¹ : Rˣ) : R))
        = h2 * ((u1 : R) * ((u1⁻¹ : Rˣ) : R)) * ((u2⁻¹ : Rˣ) : R) := by ring
      _ = h2 * ((u2⁻¹ : Rˣ) : R) := by rw [u1.mul_inv]; ring
  constructor
  · intro h; rw [← k1, ← k2, h]
  · intro h; rw [← k3, ← k4, h]

/-- The `ZMod q` instance of the collision criterion. -/
theorem ratio_eq_iff_cross_zmod (q : ℕ) (h1 h2 : ZMod q) (u1 u2 : (ZMod q)ˣ) :
    h1 * ((u1⁻¹ : (ZMod q)ˣ) : ZMod q) = h2 * ((u2⁻¹ : (ZMod q)ˣ) : ZMod q)
      ↔ h1 * (u2 : ZMod q) = h2 * (u1 : ZMod q) :=
  ratio_eq_iff_cross h1 h2 u1 u2

/-! ## §13. Integer no-wrap rigidity -/

/-- **No-wrap rigidity.**  If `q ∣ a - b` and `|a - b| < |q|` then `a = b`.  The size
hypothesis is literal; it is *not* deduced from any exponent inequality. -/
theorem nowrap_eq_of_dvd_of_abs_lt {q a b : ℤ} (hdvd : q ∣ a - b) (hlt : |a - b| < |q|) :
    a = b := by
  rcases eq_or_ne (a - b) 0 with h | h
  · linarith [sub_eq_zero.mp h]
  · have := Int.le_of_dvd (abs_pos.mpr h) ((abs_dvd _ _).mpr ((dvd_abs _ _).mpr hdvd))
    omega

/-- The physical instance: a modular cross-relation with a genuine no-wrap size bound gives
the **integer** cross-relation. -/
theorem nowrap_cross_eq {q : ℤ} {h1 h2 e1 e2 : ℤ}
    (hcong : h1 * e2 ≡ h2 * e1 [ZMOD q]) (hsize : |h1 * e2 - h2 * e1| < |q|) :
    h1 * e2 = h2 * e1 :=
  nowrap_eq_of_dvd_of_abs_lt (Int.ModEq.dvd hcong.symm) hsize

/-- Exponent capacity, restated: `E H = X^{16/35} < X^{21/35} = Q`, margin `1/7`.
**Capacity only** — it does not by itself discharge the size hypothesis above. -/
theorem eh_lt_q_capacity :
    Erdos287.Ledger3221.Eexp + Erdos287.Ledger3221.Hexp < Erdos287.Ledger3221.Qexp :=
  Erdos287.Ledger3221.Eexp_add_Hexp_lt_Qexp

/-! ## §14. Hostile audit: the ratio-fibre collision count -/

/-- **Same-prime collisions.**  If `e ≠ 0` and `h₁ e = h₂ e` then `h₁ = h₂`. -/
theorem ratioCollision_samePrime {e : ℕ} {h1 h2 : ℤ} (he : e ≠ 0)
    (heq : h1 * (e : ℤ) = h2 * (e : ℤ)) : h1 = h2 := by
  have he' : (e : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr he
  exact mul_right_cancel₀ he' heq

/-- **Distinct-prime collisions.**  For distinct primes `e₁ ≠ e₂`, the relation
`h₁ e₂ = h₂ e₁` forces `h₁ = c e₁`, `h₂ = c e₂` with the *same* integer `c`. -/
theorem ratioCollision_distinctPrimes_param {e1 e2 : ℕ} {h1 h2 : ℤ}
    (hp1 : e1.Prime) (hp2 : e2.Prime) (hne : e1 ≠ e2)
    (heq : h1 * (e2 : ℤ) = h2 * (e1 : ℤ)) :
    ∃ c : ℤ, h1 = c * e1 ∧ h2 = c * e2 := by
  have hcop : Nat.Coprime e1 e2 := (Nat.coprime_primes hp1 hp2).mpr hne
  have hcopZ : IsCoprime (e1 : ℤ) (e2 : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hdvd : (e1 : ℤ) ∣ h1 * e2 := ⟨h2, by rw [heq]; ring⟩
  obtain ⟨c, hc⟩ := hcopZ.dvd_of_dvd_mul_right hdvd
  have he1 : (e1 : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp1.ne_zero
  refine ⟨c, by rw [hc]; ring, ?_⟩
  have : h2 * (e1 : ℤ) = (c * e2) * e1 := by rw [← heq, hc]; ring
  exact mul_right_cancel₀ he1 this

/-- The explicit collision parameter `c = h₁ / e₁`, with both exact divisions. -/
theorem ratioCollision_param_div {e1 e2 : ℕ} {h1 h2 : ℤ}
    (hp1 : e1.Prime) (hp2 : e2.Prime) (hne : e1 ≠ e2)
    (heq : h1 * (e2 : ℤ) = h2 * (e1 : ℤ)) :
    h1 = (h1 / (e1 : ℤ)) * e1 ∧ h2 = (h1 / (e1 : ℤ)) * e2 := by
  obtain ⟨c, hc1, hc2⟩ := ratioCollision_distinctPrimes_param hp1 hp2 hne heq
  have he1 : (e1 : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp1.ne_zero
  have hcdiv : h1 / (e1 : ℤ) = c := by
    rw [hc1, Int.mul_ediv_cancel _ he1]
  rw [hcdiv]
  exact ⟨hc1, hc2⟩

/-- The collision quadruples: pairs `((e₁,h₁),(e₂,h₂))` with `h₁ e₂ = h₂ e₁`. -/
def collisionSet (Ebox : Finset ℕ) (Hbox : Finset ℤ) : Finset ((ℕ × ℤ) × (ℕ × ℤ)) :=
  ((Ebox ×ˢ Hbox) ×ˢ (Ebox ×ˢ Hbox)).filter
    (fun z => z.1.2 * (z.2.1 : ℤ) = z.2.2 * (z.1.1 : ℤ))

/-- The `c`-box: the range of the collision parameter. -/
def cBox (Hmax Emin : ℤ) : Finset ℤ := Finset.Icc (-(Hmax / Emin)) (Hmax / Emin)

/-- The cardinality of the `c`-box. -/
theorem cBox_card (Hmax Emin : ℤ) :
    (cBox Hmax Emin).card = (2 * (Hmax / Emin) + 1).toNat := by
  rw [cBox, Int.card_Icc]
  congr 1
  ring

/-- **The honest collision count.**

`#{((e₁,h₁),(e₂,h₂)) : h₁e₂ = h₂e₁} ≤ #E · #H + (#E)² · #C`,

with the diagonal part `e₁ = e₂` contributing `#E · #H` and the distinct-prime part
contributing at most `(#E)² · #C`, `C` the `c`-range. -/
theorem ratioCollision_card_bound (Ebox : Finset ℕ) (Hbox : Finset ℤ) {Hmax Emin : ℤ}
    (hEmin : 0 < Emin) (hprime : ∀ e ∈ Ebox, e.Prime) (hE : ∀ e ∈ Ebox, Emin ≤ (e : ℤ))
    (hH : ∀ h ∈ Hbox, |h| ≤ Hmax) :
    (collisionSet Ebox Hbox).card
      ≤ Ebox.card * Hbox.card + Ebox.card * Ebox.card * (cBox Hmax Emin).card := by
  classical
  have hsplit :
      ((collisionSet Ebox Hbox).filter (fun z => z.1.1 = z.2.1)).card
        + ((collisionSet Ebox Hbox).filter (fun z => ¬ z.1.1 = z.2.1)).card
        = (collisionSet Ebox Hbox).card :=
    Finset.card_filter_add_card_filter_not _
  have hA : ((collisionSet Ebox Hbox).filter (fun z => z.1.1 = z.2.1)).card
      ≤ Ebox.card * Hbox.card := by
    have : ((collisionSet Ebox Hbox).filter (fun z => z.1.1 = z.2.1)).card
        ≤ (Ebox ×ˢ Hbox).card := by
      refine Finset.card_le_card_of_injOn (fun z => z.1) ?_ ?_
      · intro z hz
        obtain ⟨hz1, -⟩ := Finset.mem_filter.mp hz
        exact (Finset.mem_product.mp (Finset.mem_filter.mp hz1).1).1
      · intro z hz w hw hzw
        obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
        obtain ⟨hw1, hw2⟩ := Finset.mem_filter.mp hw
        obtain ⟨hzmem, hzrel⟩ := Finset.mem_filter.mp hz1
        obtain ⟨hwmem, hwrel⟩ := Finset.mem_filter.mp hw1
        have hze : z.1.1 ≠ 0 :=
          (hprime z.1.1 (Finset.mem_product.mp (Finset.mem_product.mp hzmem).1).1).ne_zero
        have hwe : w.1.1 ≠ 0 :=
          (hprime w.1.1 (Finset.mem_product.mp (Finset.mem_product.mp hwmem).1).1).ne_zero
        -- second coordinates are forced
        have hz2' : z.2.2 = z.1.2 := by
          have h := hzrel
          rw [← hz2] at h
          exact (ratioCollision_samePrime hze h).symm
        have hw2' : w.2.2 = w.1.2 := by
          have h := hwrel
          rw [← hw2] at h
          exact (ratioCollision_samePrime hwe h).symm
        have h1 : z.1 = w.1 := hzw
        have h2 : z.2 = w.2 := by
          have e1 : z.2.1 = w.2.1 := by rw [← hz2, ← hw2, h1]
          have e2 : z.2.2 = w.2.2 := by rw [hz2', hw2', h1]
          exact Prod.ext e1 e2
        exact Prod.ext h1 h2
    simpa [Finset.card_product] using this
  have hB : ((collisionSet Ebox Hbox).filter (fun z => ¬ z.1.1 = z.2.1)).card
      ≤ Ebox.card * Ebox.card * (cBox Hmax Emin).card := by
    have : ((collisionSet Ebox Hbox).filter (fun z => ¬ z.1.1 = z.2.1)).card
        ≤ ((Ebox ×ˢ Ebox) ×ˢ (cBox Hmax Emin)).card := by
      refine Finset.card_le_card_of_injOn
        (fun z => ((z.1.1, z.2.1), z.1.2 / (z.1.1 : ℤ))) ?_ ?_
      · intro z hz
        obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
        obtain ⟨hzmem, hzrel⟩ := Finset.mem_filter.mp hz1
        obtain ⟨hz11, hz12⟩ := Finset.mem_product.mp hzmem
        obtain ⟨hze1, hzh1⟩ := Finset.mem_product.mp hz11
        obtain ⟨hze2, hzh2⟩ := Finset.mem_product.mp hz12
        have hp1 := hprime _ hze1
        have hp2 := hprime _ hze2
        obtain ⟨hc1, -⟩ := ratioCollision_param_div hp1 hp2 hz2 hzrel
        refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hze1, hze2⟩, ?_⟩
        -- the parameter is in the `c`-box
        set c : ℤ := z.1.2 / (z.1.1 : ℤ) with hcdef
        have he1pos : (0 : ℤ) < (z.1.1 : ℤ) := by exact_mod_cast hp1.pos
        have habs : |c| * Emin ≤ Hmax := by
          have h1 : |c| * Emin ≤ |c| * (z.1.1 : ℤ) :=
            mul_le_mul_of_nonneg_left (hE _ hze1) (abs_nonneg c)
          have h2 : |c| * (z.1.1 : ℤ) = |z.1.2| := by
            rw [hc1, abs_mul, abs_of_pos he1pos]
          have h3 : |z.1.2| ≤ Hmax := hH _ hzh1
          omega
        have : |c| ≤ Hmax / Emin := (Int.le_ediv_iff_mul_le hEmin).mpr habs
        rw [cBox, Finset.mem_Icc]
        exact ⟨(abs_le.mp this).1, (abs_le.mp this).2⟩
      · intro z hz w hw hzw
        obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
        obtain ⟨hzmem, hzrel⟩ := Finset.mem_filter.mp hz1
        obtain ⟨hz11, hz12⟩ := Finset.mem_product.mp hzmem
        obtain ⟨hze1, hzh1⟩ := Finset.mem_product.mp hz11
        obtain ⟨hze2, hzh2⟩ := Finset.mem_product.mp hz12
        obtain ⟨hw1, hw2⟩ := Finset.mem_filter.mp hw
        obtain ⟨hwmem, hwrel⟩ := Finset.mem_filter.mp hw1
        obtain ⟨hw11, hw12⟩ := Finset.mem_product.mp hwmem
        obtain ⟨hwe1, hwh1⟩ := Finset.mem_product.mp hw11
        obtain ⟨hwe2, hwh2⟩ := Finset.mem_product.mp hw12
        obtain ⟨hzc1, hzc2⟩ :=
          ratioCollision_param_div (hprime _ hze1) (hprime _ hze2) hz2 hzrel
        obtain ⟨hwc1, hwc2⟩ :=
          ratioCollision_param_div (hprime _ hwe1) (hprime _ hwe2) hw2 hwrel
        simp only [Prod.mk.injEq] at hzw
        obtain ⟨⟨he1, he2⟩, hc⟩ := hzw
        have hh1 : z.1.2 = w.1.2 := by rw [hzc1, hwc1, hc, he1]
        have hh2 : z.2.2 = w.2.2 := by rw [hzc2, hwc2, hc, he2]
        exact Prod.ext (Prod.ext he1 hh1) (Prod.ext he2 hh2)
    simpa [Finset.card_product, mul_assoc] using this
  omega

/-! ### Ratio-fibre energy -/

/-- Counting identity: the sum of squared fibre cardinalities is the number of colliding
pairs. -/
theorem card_collision_eq_sum_sq {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (Lam : Finset κ) (r : ι → κ) (hr : ∀ i ∈ S, r i ∈ Lam) :
    ∑ l ∈ Lam, ((S.filter (fun i => r i = l)).card) ^ 2
      = (((S ×ˢ S).filter (fun z => r z.1 = r z.2)).card) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun z => r z.1) (t := Lam) ?_]
  · refine Finset.sum_congr rfl (fun l _ => ?_)
    have hset : ((S ×ˢ S).filter (fun z => r z.1 = r z.2)).filter (fun z => r z.1 = l)
        = (S.filter (fun i => r i = l)) ×ˢ (S.filter (fun i => r i = l)) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        exact ⟨⟨h1, h4⟩, ⟨h2, by rw [← h3, h4]⟩⟩
      · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
        exact ⟨⟨⟨h1, h3⟩, by rw [h2, h4]⟩, h2⟩
    rw [hset, Finset.card_product, sq]
  · intro z hz
    exact hr z.1 (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1

/-- **Ratio-fibre energy ≤ collision count** for unimodular coefficients. -/
theorem energy_le_collision_card {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (Lam : Finset κ) (r : ι → κ) (hr : ∀ i ∈ S, r i ∈ Lam)
    (c : ι → ℂ) (hc : ∀ i ∈ S, ‖c i‖ ≤ 1) :
    ∑ l ∈ Lam, ‖∑ i ∈ S.filter (fun i => r i = l), c i‖ ^ 2
      ≤ ((((S ×ˢ S).filter (fun z => r z.1 = r z.2)).card : ℝ)) := by
  classical
  rw [← card_collision_eq_sum_sq S Lam r hr]
  push_cast
  refine Finset.sum_le_sum (fun l _ => ?_)
  have h1 : ‖∑ i ∈ S.filter (fun i => r i = l), c i‖
      ≤ ((S.filter (fun i => r i = l)).card : ℝ) := by
    calc ‖∑ i ∈ S.filter (fun i => r i = l), c i‖
        ≤ ∑ i ∈ S.filter (fun i => r i = l), ‖c i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ S.filter (fun i => r i = l), (1 : ℝ) :=
          Finset.sum_le_sum (fun i hi => hc i (Finset.mem_filter.mp hi).1)
      _ = _ := by simp
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-- **The audited `(e,h)` ratio-fibre energy bound.**

If the ratio map `r` has the no-wrap property — collisions of `r` on the source box imply
the *integer* cross-relation `h₁ e₂ = h₂ e₁`, which is exactly what §12 + §13 supply — then
for unimodular coefficients

`∑_λ |∑_{r(e,h) = λ} a_e b_h|² ≤ #E · #H + (#E)² · #C`.

No divisor factor and no `X^{o(1)}` appear.  The bound is `CONDITIONAL_FINITE`: it holds
under the explicit no-wrap hypothesis `hnowrap`. -/
theorem ehRatioEnergy_le_explicit {κ : Type*} [DecidableEq κ]
    (Ebox : Finset ℕ) (Hbox : Finset ℤ) (Lam : Finset κ) (r : ℕ × ℤ → κ)
    {Hmax Emin : ℤ} (hEmin : 0 < Emin)
    (hprime : ∀ e ∈ Ebox, e.Prime) (hE : ∀ e ∈ Ebox, Emin ≤ (e : ℤ))
    (hH : ∀ h ∈ Hbox, |h| ≤ Hmax)
    (hr : ∀ x ∈ Ebox ×ˢ Hbox, r x ∈ Lam)
    (hnowrap : ∀ x ∈ Ebox ×ˢ Hbox, ∀ y ∈ Ebox ×ˢ Hbox,
      r x = r y → x.2 * (y.1 : ℤ) = y.2 * (x.1 : ℤ))
    (a : ℕ → ℂ) (b : ℤ → ℂ) (ha : ∀ e ∈ Ebox, ‖a e‖ ≤ 1) (hb : ∀ h ∈ Hbox, ‖b h‖ ≤ 1) :
    ∑ l ∈ Lam, ‖∑ x ∈ (Ebox ×ˢ Hbox).filter (fun x => r x = l), a x.1 * b x.2‖ ^ 2
      ≤ ((Ebox.card * Hbox.card + Ebox.card * Ebox.card * (cBox Hmax Emin).card : ℕ) : ℝ) := by
  classical
  set S := Ebox ×ˢ Hbox with hS
  have hcoef : ∀ x ∈ S, ‖a x.1 * b x.2‖ ≤ 1 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
    rw [norm_mul]
    exact mul_le_one₀ (ha _ hx1) (norm_nonneg _) (hb _ hx2)
  have h1 := energy_le_collision_card S Lam r hr (fun x => a x.1 * b x.2) hcoef
  have hsub : (S ×ˢ S).filter (fun z => r z.1 = r z.2) ⊆ collisionSet Ebox Hbox := by
    intro z hz
    obtain ⟨hzmem, hzrel⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hzmem
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz1, hz2⟩, ?_⟩
    exact hnowrap _ hz1 _ hz2 hzrel
  have h2 : (((S ×ˢ S).filter (fun z => r z.1 = r z.2)).card : ℝ)
      ≤ ((collisionSet Ebox Hbox).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have h3 := ratioCollision_card_bound Ebox Hbox hEmin hprime hE hH
  have h3' : ((collisionSet Ebox Hbox).card : ℝ)
      ≤ ((Ebox.card * Hbox.card + Ebox.card * Ebox.card * (cBox Hmax Emin).card : ℕ) : ℝ) := by
    exact_mod_cast h3
  linarith

end EHNoWrap3221
end Erdos287
