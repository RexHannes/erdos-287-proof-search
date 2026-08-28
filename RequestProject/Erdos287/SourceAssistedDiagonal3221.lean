import Mathlib
import RequestProject.Erdos287.Exponent3221Ledger
import RequestProject.Erdos287.BalancedSeven3221Grouping

/-!
# V17, Phase B — the finite source-assisted first diagonal

`3221-SOURCE-ASSISTED-DIAGONAL45 : PROVED_FINITE + CAPACITY_ONLY`.

Three genuinely finite ingredients, with **no** asymptotics, **no** `X^{o(1)}` and **no**
analytic discrepancy anywhere:

* §7 `fiberwise_energy_le` — the exact pushforward energy inequality
  `∑_w |u(w)|² ≤ F_max · ∑ |c|²`, where `F_max` bounds the fibre cardinality of the
  pushforward map.  `productFibre_card_le` supplies the arithmetic fibre bound for the
  triple product `e·n·ℓ = w`, namely `τ(w)²` (this repository contains no fixed-depth
  divisor majorant to reuse, so the honest `τ²` bound is proved from scratch here).
* §8 `modulus_divisor_count_le` — for a nonzero integer `d`, at most `τ(|d|)` moduli in any
  box divide `d`; `modulus_count_zero_case` is the load-bearing guard showing that the
  degenerate case `d = 0` must be routed separately: there the count is the *whole* box.
* §9 `diagonal_parent_bound` — the finite diagonal parent
  `∑_{q,m,w} |u(w)|² 1_{m w ≡ a (q)}` is bounded by `D_max · #Mbox · ∑_w |u(w)|²` whenever
  `D_max` bounds the modulus count, and `sourceAssisted_diagonal_finite` composes this with
  the pushforward energy.

The exponent-level consequence `M √(Q E N L) = X √(Q/(E N L))` and the resulting exponent
`1 - 2/35` are in `Erdos287.Ledger3221` (`diagonal_exponent_identity`,
`diagonal_exponent_value`).

**Status caveat.**  `D_max` and `F_max` are *inputs*: they are hypotheses of the finite
theorems, not analytic theorems proved here.  Therefore the diagonal is banked as
`PROVED_FINITE + CAPACITY_ONLY`, never as an unconditional analytic estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace Erdos287
namespace Diagonal3221

/-! ## §7. Pushforward energy -/

/-- **Exact fibrewise energy inequality.**  If every fibre of `g` over `t` has at most `F`
elements, then the `ℓ²` energy of the pushforward `j ↦ ∑_{g i = j} c i` is at most
`F · ∑_i |c i|²`.  No asymptotics: this is Cauchy–Schwarz on each fibre. -/
theorem fiberwise_energy_le {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ)
    (g : ι → κ) (hg : ∀ i ∈ s, g i ∈ t) (c : ι → ℂ) (F : ℝ)
    (hF : ∀ j ∈ t, ((s.filter (fun i => g i = j)).card : ℝ) ≤ F) :
    ∑ j ∈ t, ‖∑ i ∈ s with g i = j, c i‖ ^ 2 ≤ F * ∑ i ∈ s, ‖c i‖ ^ 2 := by
  classical
  have key : ∀ j ∈ t, ‖∑ i ∈ s with g i = j, c i‖ ^ 2
      ≤ F * ∑ i ∈ s with g i = j, ‖c i‖ ^ 2 := by
    intro j hj
    have h1 : ‖∑ i ∈ s with g i = j, c i‖ ^ 2
        ≤ (((s.filter (fun i => g i = j)).card : ℝ)) * ∑ i ∈ s with g i = j, ‖c i‖ ^ 2 := by
      calc ‖∑ i ∈ s with g i = j, c i‖ ^ 2 ≤ (∑ i ∈ s with g i = j, ‖c i‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ _ := sq_sum_le_card_mul_sum_sq
    have h2 : (0 : ℝ) ≤ ∑ i ∈ s with g i = j, ‖c i‖ ^ 2 :=
      Finset.sum_nonneg (fun i _ => by positivity)
    exact h1.trans (mul_le_mul_of_nonneg_right (hF j hj) h2)
  calc ∑ j ∈ t, ‖∑ i ∈ s with g i = j, c i‖ ^ 2
      ≤ ∑ j ∈ t, F * ∑ i ∈ s with g i = j, ‖c i‖ ^ 2 := Finset.sum_le_sum key
    _ = F * ∑ j ∈ t, ∑ i ∈ s with g i = j, ‖c i‖ ^ 2 := by rw [Finset.mul_sum]
    _ = F * ∑ i ∈ s, ‖c i‖ ^ 2 := by
        rw [Finset.sum_fiberwise_of_maps_to hg]

/-- **Product-fibre bound.**  For `w ≠ 0`, the number of triples `(e,n,ℓ)` in any box with
`e n ℓ = w` is at most `τ(w)²`. -/
theorem productFibre_card_le (T : Finset (ℕ × ℕ × ℕ)) {w : ℕ} (hw : w ≠ 0) :
    (T.filter (fun x => x.1 * x.2.1 * x.2.2 = w)).card ≤ w.divisors.card ^ 2 := by
  classical
  have hsub : (T.filter (fun x => x.1 * x.2.1 * x.2.2 = w)).card
      ≤ (w.divisors ×ˢ w.divisors).card := by
    refine Finset.card_le_card_of_injOn (fun x => (x.1, x.2.1)) ?_ ?_
    · rintro ⟨e, n, l⟩ hx
      obtain ⟨-, hprod⟩ := Finset.mem_filter.mp hx
      simp only at hprod
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · exact Nat.mem_divisors.mpr ⟨⟨n * l, by rw [← hprod]; ring⟩, hw⟩
      · exact Nat.mem_divisors.mpr ⟨⟨e * l, by rw [← hprod]; ring⟩, hw⟩
    · rintro ⟨e, n, l⟩ hx ⟨e', n', l'⟩ hy hxy
      obtain ⟨-, hp1⟩ := Finset.mem_filter.mp hx
      obtain ⟨-, hp2⟩ := Finset.mem_filter.mp hy
      simp only at hp1 hp2
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨he, hn⟩ := hxy
      subst he; subst hn
      have h1 : e * n * l = e * n * l' := by rw [hp1, hp2]
      have hen : 0 < e * n := by
        rcases Nat.eq_zero_or_pos (e * n) with h | h
        · rw [h, zero_mul] at hp1; exact absurd hp1.symm hw
        · exact h
      have hl : l = l' := Nat.eq_of_mul_eq_mul_left hen h1
      simp [hl]
  simpa [Finset.card_product, sq] using hsub

/-- The pushforward `u(w) = ∑_{e n ℓ = w} η(e) β(n) γ(ℓ)` of a triple-box coefficient. -/
noncomputable def pushforward (T : Finset (ℕ × ℕ × ℕ)) (c : ℕ × ℕ × ℕ → ℂ) (w : ℕ) : ℂ :=
  ∑ x ∈ T with x.1 * x.2.1 * x.2.2 = w, c x

/-- **Triple-product energy.**  If every value `w` in the target box is nonzero and its
divisor count is at most `Dv`, then `∑_w |u(w)|² ≤ Dv² · ∑ |c|²`. -/
theorem pushforward_energy_le (T : Finset (ℕ × ℕ × ℕ)) (Wset : Finset ℕ)
    (c : ℕ × ℕ × ℕ → ℂ) (Dv : ℝ)
    (hmaps : ∀ x ∈ T, x.1 * x.2.1 * x.2.2 ∈ Wset)
    (hzero : ∀ w ∈ Wset, w ≠ 0)
    (hdiv : ∀ w ∈ Wset, (w.divisors.card : ℝ) ≤ Dv) :
    ∑ w ∈ Wset, ‖pushforward T c w‖ ^ 2 ≤ Dv ^ 2 * ∑ x ∈ T, ‖c x‖ ^ 2 := by
  classical
  refine fiberwise_energy_le T Wset (fun x => x.1 * x.2.1 * x.2.2) hmaps c (Dv ^ 2) ?_
  intro w hw
  have h1 := productFibre_card_le T (hzero w hw)
  have h2 : (((T.filter (fun x => x.1 * x.2.1 * x.2.2 = w)).card : ℝ)) ≤ ((w.divisors.card : ℝ)) ^ 2 := by
    exact_mod_cast h1
  have h3 : (0 : ℝ) ≤ (w.divisors.card : ℝ) := by positivity
  exact h2.trans (pow_le_pow_left₀ h3 (hdiv w hw) 2)

/-! ## §8. Counting moduli: the exact divisor injection and its zero-case guard -/

/-- **Modulus divisor count.**  For a nonzero integer `d`, at most `τ(|d|)` moduli of any
box divide `d`. -/
theorem modulus_divisor_count_le (Qbox : Finset ℕ) {d : ℤ} (hd : d ≠ 0) :
    ((Qbox.filter (fun q : ℕ => (q : ℤ) ∣ d))).card ≤ d.natAbs.divisors.card := by
  classical
  refine Finset.card_le_card ?_
  intro q hq
  simp only [Finset.mem_filter] at hq
  have hqd : q ∣ d.natAbs := by
    have : (q : ℤ).natAbs ∣ d.natAbs := Int.natAbs_dvd_natAbs.mpr hq.2
    simpa using this
  exact Nat.mem_divisors.mpr ⟨hqd, Int.natAbs_ne_zero.mpr hd⟩

/-- **The load-bearing zero guard.**  If the shifted product vanishes, *every* modulus of
the box occurs, so the divisor bound is unavailable and the case must be routed
separately. -/
theorem modulus_count_zero_case (Qbox : Finset ℕ) {d : ℤ} (hd : d = 0) :
    (Qbox.filter (fun q : ℕ => (q : ℤ) ∣ d)) = Qbox := by
  classical
  subst hd
  exact Finset.filter_true_of_mem (fun q _ => dvd_zero _)

/-- The physical instance: `m w ≡ a (mod q)` iff `q ∣ m w - a`. -/
theorem congr_iff_dvd (m w : ℕ) (a : ℤ) (q : ℕ) :
    ((m * w : ℤ) ≡ a [ZMOD (q : ℤ)]) ↔ (q : ℤ) ∣ ((m * w : ℤ) - a) :=
  Int.modEq_iff_dvd.trans dvd_sub_comm

/-- Modulus count for the physical shifted product, nonzero case. -/
theorem modulus_count_physical_le (Qbox : Finset ℕ) (m w : ℕ) (a : ℤ)
    (hne : (m * w : ℤ) ≠ a) :
    ((Qbox.filter (fun q : ℕ => (q : ℤ) ∣ ((m * w : ℤ) - a)))).card
      ≤ ((m * w : ℤ) - a).natAbs.divisors.card :=
  modulus_divisor_count_le Qbox (sub_ne_zero_of_ne hne)

/-! ## §9. The finite diagonal parent -/

/-- The expanded diagonal contribution
`∑_{q ∈ Qbox} ∑_{m ∈ Mbox} ∑_{w ∈ Wset} |u(w)|² 1_{m w ≡ a (q)}`. -/
noncomputable def diagonalParent (Qbox Mbox Wset : Finset ℕ) (u : ℕ → ℂ) (a : ℤ) : ℝ :=
  ∑ q ∈ Qbox, ∑ m ∈ Mbox, ∑ w ∈ Wset,
    ‖u w‖ ^ 2 * (if (q : ℤ) ∣ ((m * w : ℤ) - a) then 1 else 0)

/-- Rewriting the diagonal parent as an energy weighted by the modulus count. -/
theorem diagonalParent_eq (Qbox Mbox Wset : Finset ℕ) (u : ℕ → ℂ) (a : ℤ) :
    diagonalParent Qbox Mbox Wset u a
      = ∑ m ∈ Mbox, ∑ w ∈ Wset,
          ‖u w‖ ^ 2 * (((Qbox.filter (fun q : ℕ => (q : ℤ) ∣ ((m * w : ℤ) - a)))).card : ℝ) := by
  classical
  rw [diagonalParent, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [← Finset.mul_sum, Finset.sum_boole]

/-- **Finite diagonal bound.**  If `Dmax` bounds the modulus count uniformly on the boxes
(this is exactly where the zero guard of §8 has to have been discharged), then

`∑_{q,m,w} |u(w)|² 1_{m w ≡ a (q)} ≤ Dmax · #Mbox · ∑_w |u(w)|²`. -/
theorem diagonal_parent_bound (Qbox Mbox Wset : Finset ℕ) (u : ℕ → ℂ) (a : ℤ) (Dmax : ℝ)
    (hD : ∀ m ∈ Mbox, ∀ w ∈ Wset,
      ((((Qbox.filter (fun q : ℕ => (q : ℤ) ∣ ((m * w : ℤ) - a)))).card : ℝ)) ≤ Dmax) :
    diagonalParent Qbox Mbox Wset u a
      ≤ Dmax * (Mbox.card : ℝ) * ∑ w ∈ Wset, ‖u w‖ ^ 2 := by
  classical
  rw [diagonalParent_eq]
  have step : ∀ m ∈ Mbox,
      (∑ w ∈ Wset, ‖u w‖ ^ 2 * (((Qbox.filter (fun q : ℕ => (q : ℤ) ∣ ((m * w : ℤ) - a)))).card : ℝ))
        ≤ Dmax * ∑ w ∈ Wset, ‖u w‖ ^ 2 := by
    intro m hm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun w hw => ?_)
    rw [mul_comm Dmax]
    exact mul_le_mul_of_nonneg_left (hD m hm w hw) (by positivity)
  calc ∑ m ∈ Mbox, ∑ w ∈ Wset,
          ‖u w‖ ^ 2 * (((Qbox.filter (fun q : ℕ => (q : ℤ) ∣ ((m * w : ℤ) - a)))).card : ℝ)
      ≤ ∑ _m ∈ Mbox, Dmax * ∑ w ∈ Wset, ‖u w‖ ^ 2 := Finset.sum_le_sum step
    _ = Dmax * (Mbox.card : ℝ) * ∑ w ∈ Wset, ‖u w‖ ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **The composed finite source-assisted diagonal.**  Pushforward energy (§7) together
with the modulus count (§8–§9) gives, for the triple-product source,

`∑_{q,m,w} |u(w)|² 1_{m w ≡ a (q)} ≤ Dmax · #Mbox · Dv² · ∑_{e,n,ℓ} |c(e,n,ℓ)|²`.

Every factor is an explicit finite input; nothing is asymptotic. -/
theorem sourceAssisted_diagonal_finite (Qbox Mbox Wset : Finset ℕ)
    (T : Finset (ℕ × ℕ × ℕ)) (c : ℕ × ℕ × ℕ → ℂ) (a : ℤ) (Dmax Dv : ℝ)
    (hDmax : 0 ≤ Dmax)
    (hmaps : ∀ x ∈ T, x.1 * x.2.1 * x.2.2 ∈ Wset)
    (hzero : ∀ w ∈ Wset, w ≠ 0)
    (hdiv : ∀ w ∈ Wset, (w.divisors.card : ℝ) ≤ Dv)
    (hD : ∀ m ∈ Mbox, ∀ w ∈ Wset,
      ((((Qbox.filter (fun q : ℕ => (q : ℤ) ∣ ((m * w : ℤ) - a)))).card : ℝ)) ≤ Dmax) :
    diagonalParent Qbox Mbox Wset (pushforward T c) a
      ≤ Dmax * (Mbox.card : ℝ) * (Dv ^ 2 * ∑ x ∈ T, ‖c x‖ ^ 2) := by
  have h1 := diagonal_parent_bound Qbox Mbox Wset (pushforward T c) a Dmax hD
  have h2 := pushforward_energy_le T Wset c Dv hmaps hzero hdiv
  refine h1.trans ?_
  have hnn : (0 : ℝ) ≤ Dmax * (Mbox.card : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left h2 hnn

/-! ## Exponent-level consequence (capacity only)

See `Erdos287.Ledger3221.diagonal_exponent_identity` and `diagonal_exponent_value`. -/

/-- The exponent identity `M √(Q E N L) = X √(Q/(E N L))`, restated here. -/
theorem diagonal_exponent_identity :
    Erdos287.Ledger3221.Mexp
        + (Erdos287.Ledger3221.Qexp + Erdos287.Ledger3221.Eexp + Erdos287.Ledger3221.Nexp
            + Erdos287.Ledger3221.Lexp) / 2
      = 1 + (Erdos287.Ledger3221.Qexp - Erdos287.Ledger3221.Wexp) / 2 :=
  Erdos287.Ledger3221.diagonal_exponent_identity

/-- The diagonal exponent value `1 - 2/35`. -/
theorem diagonal_exponent_value :
    1 + (Erdos287.Ledger3221.Qexp - Erdos287.Ledger3221.Wexp) / 2 = 1 - 2 / 35 :=
  Erdos287.Ledger3221.diagonal_exponent_value

end Diagonal3221
end Erdos287
