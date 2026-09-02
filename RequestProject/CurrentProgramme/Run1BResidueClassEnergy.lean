import RequestProject.CurrentProgramme.Run1BFiniteFourierMatrix

/-!
# RUN1B / d*wp provider — §4  residue-class energy

```
class multiplicity  #{d ≤ D : d ≡ c (r♯)} ≤ 1 + D/r♯   : KERNEL-PROVED
inverse-residue pushforwards X(u), Y(v)                 : DEFINED
ℓ² invariance of the pushforward under u ↦ u⁻¹          : KERNEL-PROVED
|S| ≤ √r♯ ‖X‖₂ ‖Y‖₂                                     : KERNEL-PROVED (finite form)
```

The finite `L²` inequality is proved outright from the §3 operator norm; the *analytic*
coefficient-energy hypotheses (what `‖X‖₂`, `‖Y‖₂` actually are for the physical `α`, `β`)
are never assumed here — they enter the §5 compiler as explicit hypotheses.

This module is **append-only** and project-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Run1B
namespace ResidueEnergy

open Run1B.Characters Run1B.EffectiveModulus Run1B.FourierMatrix

/-! ## §4.1  Class multiplicities -/

/-- The residue class `{d ∈ S : d ≡ c (mod n)}`. -/
def residueFiber (S : Finset ℕ) (n c : ℕ) : Finset ℕ := S.filter (fun d => d % n = c)

/-- **`residueFiber_card_le`.**  `KERNEL-PROVED`.  Elementary multiplicity bound
`#{d < D : d ≡ c (mod n)} ≤ D/n + 1`, in exact natural-number division. -/
theorem residueFiber_card_le (n D c : ℕ) :
    (residueFiber (Finset.range D) n c).card ≤ D / n + 1 := by
  have hinj : Set.InjOn (fun d => d / n) (residueFiber (Finset.range D) n c) := by
    intro d hd d' hd' h
    simp only [residueFiber, Finset.coe_filter, Set.mem_setOf_eq] at hd hd'
    have hd1 : d % n = c := hd.2
    have hd2 : d' % n = c := hd'.2
    have hq : d / n = d' / n := h
    calc d = n * (d / n) + d % n := (Nat.div_add_mod d n).symm
      _ = n * (d' / n) + d' % n := by rw [hq, hd1, hd2]
      _ = d' := Nat.div_add_mod d' n
  have hmaps : Set.MapsTo (fun d => d / n) (residueFiber (Finset.range D) n c : Set ℕ)
      (Finset.range (D / n + 1) : Set ℕ) := by
    intro d hd
    simp only [residueFiber, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (le_of_lt hd.1))
  have hcard := Finset.card_le_card_of_injOn (fun d => d / n) hmaps hinj
  simpa using hcard

/-- **`residueFiber_card_le_real`.**  `KERNEL-PROVED`.  The displayed real form
`#class_d ≤ 1 + D/r♯`. -/
theorem residueFiber_card_le_real (n D c : ℕ) :
    ((residueFiber (Finset.range D) n c).card : ℝ) ≤ 1 + (D : ℝ) / (n : ℝ) := by
  have h := residueFiber_card_le n D c
  have h1 : ((residueFiber (Finset.range D) n c).card : ℝ) ≤ ((D / n : ℕ) : ℝ) + 1 := by
    exact_mod_cast h
  have h2 : ((D / n : ℕ) : ℝ) ≤ (D : ℝ) / (n : ℝ) := Nat.cast_div_le
  linarith

/-- **`residueFiber_card_le_of_subset`.**  `KERNEL-PROVED`.  The same bound for any support
contained in `[0, D)`, which is the form used for the `d`- and `w'`-variables. -/
theorem residueFiber_card_le_of_subset {n : ℕ} {S : Finset ℕ} {D : ℕ}
    (hS : S ⊆ Finset.range D) (c : ℕ) :
    ((residueFiber S n c).card : ℝ) ≤ 1 + (D : ℝ) / (n : ℝ) := by
  have hsub : residueFiber S n c ⊆ residueFiber (Finset.range D) n c :=
    Finset.filter_subset_filter _ hS
  have := Finset.card_le_card hsub
  have h2 := residueFiber_card_le_real n D c
  have h1 : ((residueFiber S n c).card : ℝ) ≤ ((residueFiber (Finset.range D) n c).card : ℝ) := by
    exact_mod_cast this
  linarith

/-! ## §4.2  Inverse-residue pushforwards -/

/-- The inverse-residue pushforward of a coefficient sequence: `X(u) = ∑_{d⁻¹ ≡ u} α_d`,
indexed by the units of `ZMod n`. -/
noncomputable def pushforward (S : Finset ℕ) (coef : ℕ → ℂ) (n : ℕ) (u : (ZMod n)ˣ) : ℂ :=
  ∑ d ∈ S.filter (fun d : ℕ => ((d : ℕ) : ZMod n) = ((u⁻¹ : (ZMod n)ˣ) : ZMod n)), coef d

/-- **`pushforward_l2_inversion_invariant`.**  `KERNEL-PROVED`.  Inversion permutes the unit
group, so the `ℓ²` energy of the inverse-residue pushforward equals that of the direct
residue pushforward: no energy is created or destroyed by passing to inverses. -/
theorem pushforward_l2_inversion_invariant {n : ℕ} [NeZero n] (F : (ZMod n)ˣ → ℝ) :
    ∑ u : (ZMod n)ˣ, F u⁻¹ = ∑ u : (ZMod n)ˣ, F u :=
  Fintype.sum_bijective _ (inv_involutive.bijective) _ _ (fun _ => rfl)

/-! ## §4.3  The finite `L²` bilinear inequality -/

/-- **`Kmat_symm`.**  `KERNEL-PROVED`. -/
theorem Kmat_symm (n : ℕ) (a u v : ℤ) : Kmat n a u v = Kmat n a v u := by
  unfold Kmat
  congr 1
  ring

/-- **`bilinear_l2_bound`.**  `KERNEL-PROVED`.  The exact finite `L²` inequality

```
|S| ≤ √r♯ · ‖X‖₂ · ‖Y‖₂,
```

for `S = ∑_{u,v} X(u) Y(v) K(u,v)`, with the **unnormalised** kernel of §3.  Only the finite
orthogonality of `K` and Cauchy–Schwarz are used. -/
theorem bilinear_l2_bound {n : ℕ} (hn : 0 < n) {a : ℤ} (ha : Int.gcd a (n : ℤ) = 1)
    (X Y : ℕ → ℂ) :
    ‖∑ u ∈ Finset.range n, ∑ v ∈ Finset.range n, X u * Y v * Kmat n a (u : ℤ) (v : ℤ)‖
      ≤ Real.sqrt (n : ℝ) * Real.sqrt (∑ u ∈ Finset.range n, ‖X u‖ ^ 2) *
          Real.sqrt (∑ v ∈ Finset.range n, ‖Y v‖ ^ 2) := by
  set Z : ℕ → ℂ := fun u => ∑ v ∈ Finset.range n, Kmat n a (v : ℤ) (u : ℤ) * Y v with hZ
  have hrow : ∀ u ∈ Finset.range n,
      (∑ v ∈ Finset.range n, X u * Y v * Kmat n a (u : ℤ) (v : ℤ)) = X u * Z u := by
    intro u _
    rw [hZ, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Kmat_symm]
    ring
  rw [Finset.sum_congr rfl hrow]
  have hstep1 : ‖∑ u ∈ Finset.range n, X u * Z u‖ ≤ ∑ u ∈ Finset.range n, ‖X u‖ * ‖Z u‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    exact Finset.sum_le_sum (fun u _ => le_of_eq (norm_mul _ _))
  have hCS : ∑ u ∈ Finset.range n, ‖X u‖ * ‖Z u‖
      ≤ Real.sqrt (∑ u ∈ Finset.range n, ‖X u‖ ^ 2) *
          Real.sqrt (∑ u ∈ Finset.range n, ‖Z u‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hZnorm : ∑ u ∈ Finset.range n, ‖Z u‖ ^ 2 = (n : ℝ) * ∑ v ∈ Finset.range n, ‖Y v‖ ^ 2 :=
    Kmat_operator_norm_sqrt hn ha Y
  have hsqrt : Real.sqrt (∑ u ∈ Finset.range n, ‖Z u‖ ^ 2)
      = Real.sqrt (n : ℝ) * Real.sqrt (∑ v ∈ Finset.range n, ‖Y v‖ ^ 2) := by
    rw [hZnorm, Real.sqrt_mul (Nat.cast_nonneg n)]
  calc ‖∑ u ∈ Finset.range n, X u * Z u‖
      ≤ ∑ u ∈ Finset.range n, ‖X u‖ * ‖Z u‖ := hstep1
    _ ≤ Real.sqrt (∑ u ∈ Finset.range n, ‖X u‖ ^ 2) *
          Real.sqrt (∑ u ∈ Finset.range n, ‖Z u‖ ^ 2) := hCS
    _ = Real.sqrt (n : ℝ) * Real.sqrt (∑ u ∈ Finset.range n, ‖X u‖ ^ 2) *
          Real.sqrt (∑ v ∈ Finset.range n, ‖Y v‖ ^ 2) := by rw [hsqrt]; ring

end ResidueEnergy
end Run1B
