import RequestProject.CurrentProgramme.Run1BLargeModulusCompiler

/-!
# RUN1B / d*wp provider — §6  the small-effective-modulus Fourier expansion

```
periodic reciprocal phase u ↦ e_{r♯}(A u⁻¹)      : DEFINED, periodicity KERNEL-PROVED
finite additive Fourier expansion (inversion)    : KERNEL-PROVED
Parseval                                         : KERNEL-PROVED
L¹ ≤ √r♯ · L²                                    : KERNEL-PROVED
Möbius polynomial-phase estimate                 : PAPER_CLOSED_EXTERNAL input (uninhabited here)
input + expansion → small-modulus estimate       : CONDITIONAL KERNEL-PROVED
```

The Möbius polynomial-phase theorem is **not** proved here and is **not** an axiom: it is an
explicit hypothesis (a structure carrying the literal estimate) that appears in the assumption
chain of the compiler theorem.  A counterguard shows the hypothesis is a genuine constraint.

This module is **append-only** and project-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Run1B
namespace SmallModulus

open Run1B.Characters Run1B.EffectiveModulus Run1B.FourierMatrix Run1B.Source

/-! ## §6.1  The finite additive Fourier expansion -/

/-- The finite additive Fourier coefficient at modulus `n`:
`f̂(h) = (1/n) ∑_{u mod n} f(u) e_n(−h u)`. -/
noncomputable def fourierCoeff (n : ℕ) (f : ℕ → ℂ) (h : ℕ) : ℂ :=
  (1 / (n : ℂ)) * ∑ u ∈ Finset.range n, f u * eAdd n (-((h : ℤ) * (u : ℤ)))

/-- **`fourier_inversion`.**  `KERNEL-PROVED`.  Exact finite Fourier inversion. -/
theorem fourier_inversion {n : ℕ} (hn : 0 < n) (f : ℕ → ℂ) {u : ℕ} (hu : u < n) :
    ∑ h ∈ Finset.range n, fourierCoeff n f h * eAdd n ((h : ℤ) * (u : ℤ)) = f u := by
  have hnC : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have key : ∀ h ∈ Finset.range n, fourierCoeff n f h * eAdd n ((h : ℤ) * (u : ℤ))
      = ∑ u' ∈ Finset.range n,
          (1 / (n : ℂ)) * f u' * eAdd n (((u : ℤ) - (u' : ℤ)) * (h : ℤ)) := by
    intro h _
    rw [fourierCoeff, mul_assoc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u' _ => ?_)
    have he : eAdd n (-((h : ℤ) * (u' : ℤ))) * eAdd n ((h : ℤ) * (u : ℤ))
        = eAdd n (((u : ℤ) - (u' : ℤ)) * (h : ℤ)) := by
      rw [← eAdd_add]
      congr 1
      ring
    calc (1 / (n : ℂ)) * (f u' * eAdd n (-((h : ℤ) * (u' : ℤ))) * eAdd n ((h : ℤ) * (u : ℤ)))
        = (1 / (n : ℂ)) * f u' *
            (eAdd n (-((h : ℤ) * (u' : ℤ))) * eAdd n ((h : ℤ) * (u : ℤ))) := by ring
      _ = (1 / (n : ℂ)) * f u' * eAdd n (((u : ℤ) - (u' : ℤ)) * (h : ℤ)) := by rw [he]
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  have inner : ∀ u' ∈ Finset.range n,
      ∑ h ∈ Finset.range n, (1 / (n : ℂ)) * f u' * eAdd n (((u : ℤ) - (u' : ℤ)) * (h : ℤ))
        = (1 / (n : ℂ)) * f u' * (if (n : ℤ) ∣ ((u : ℤ) - (u' : ℤ)) then (n : ℂ) else 0) := by
    intro u' _
    rw [← Finset.mul_sum, eAdd_orthogonality hn]
  rw [Finset.sum_congr rfl inner, Finset.sum_eq_single u]
  · rw [if_pos (by simp)]
    field_simp
  · intro u' hu' hne
    rw [if_neg (not_dvd_sub_of_lt hu (Finset.mem_range.1 hu') (Ne.symm hne)), mul_zero]
  · intro hcon
    exact absurd (Finset.mem_range.2 hu) hcon

/-- **`fourier_parseval`.**  `KERNEL-PROVED`.  Parseval at modulus `n`, in the convention in
which the coefficients carry the `1/n`:  `∑_u |f(u)|² = n ∑_h |f̂(h)|²`. -/
theorem fourier_parseval {n : ℕ} (hn : 0 < n) (f : ℕ → ℂ) :
    ∑ u ∈ Finset.range n, ‖f u‖ ^ 2
      = (n : ℝ) * ∑ h ∈ Finset.range n, ‖fourierCoeff n f h‖ ^ 2 := by
  have hgcd : Int.gcd (-1 : ℤ) (n : ℤ) = 1 := by simp
  have hK : ∀ h u : ℕ, Kmat n (-1 : ℤ) (h : ℤ) (u : ℤ) = eAdd n ((h : ℤ) * (u : ℤ)) := by
    intro h u
    unfold Kmat
    congr 1
    ring
  have hiso := Kmat_operator_norm_sqrt hn hgcd (fourierCoeff n f)
  have hleft : ∀ u ∈ Finset.range n,
      ‖∑ h ∈ Finset.range n, Kmat n (-1 : ℤ) (h : ℤ) (u : ℤ) * fourierCoeff n f h‖ ^ 2
        = ‖f u‖ ^ 2 := by
    intro u hu
    congr 1
    have : ∑ h ∈ Finset.range n, Kmat n (-1 : ℤ) (h : ℤ) (u : ℤ) * fourierCoeff n f h
        = ∑ h ∈ Finset.range n, fourierCoeff n f h * eAdd n ((h : ℤ) * (u : ℤ)) := by
      refine Finset.sum_congr rfl (fun h _ => ?_)
      rw [hK]
      ring
    rw [this, fourier_inversion hn f (Finset.mem_range.1 hu)]
  rw [← Finset.sum_congr rfl hleft]
  exact hiso

/-- **`fourier_l1_le_sqrt_l2`.**  `KERNEL-PROVED`.  `L¹ ≤ √n · L²` for the finite Fourier
coefficients. -/
theorem fourier_l1_le_sqrt_l2 (n : ℕ) (f : ℕ → ℂ) :
    ∑ h ∈ Finset.range n, ‖fourierCoeff n f h‖
      ≤ Real.sqrt (n : ℝ) * Real.sqrt (∑ h ∈ Finset.range n, ‖fourierCoeff n f h‖ ^ 2) := by
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range n) (fun _ => (1 : ℝ))
    (fun h => ‖fourierCoeff n f h‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hCS
  exact hCS

/-! ## §6.2  The periodic reciprocal phase -/

/-- The periodic reciprocal phase `u ↦ e_n(A u⁻¹)`. -/
noncomputable def recipPhase (n : ℕ) (A : ℤ) (u : ℕ) : ℂ := eAdd n (A * invMod n u)

/-- **`recipPhase_periodic`.**  `KERNEL-PROVED`.  The reciprocal phase is `n`-periodic. -/
theorem recipPhase_periodic (n : ℕ) (A : ℤ) (u : ℕ) :
    recipPhase n A (u + n) = recipPhase n A u := by
  unfold recipPhase invMod
  congr 3
  push_cast
  simp

/-- **`recipPhase_mod`.**  `KERNEL-PROVED`.  Only the residue of `u` matters. -/
theorem recipPhase_mod (n : ℕ) (A : ℤ) (u : ℕ) : recipPhase n A (u % n) = recipPhase n A u := by
  unfold recipPhase invMod
  congr 3
  rw [ZMod.natCast_mod]

/-- **`recipPhase_expansion`.**  `KERNEL-PROVED`.  The finite additive Fourier expansion of
the periodic reciprocal phase. -/
theorem recipPhase_expansion {n : ℕ} (hn : 0 < n) (A : ℤ) {u : ℕ} (hu : u < n) :
    ∑ h ∈ Finset.range n, fourierCoeff n (recipPhase n A) h * eAdd n ((h : ℤ) * (u : ℤ))
      = recipPhase n A u :=
  fourier_inversion hn (recipPhase n A) hu

/-! ## §6.3  The external Möbius polynomial-phase input -/

/-- **`MobiusPolynomialPhaseInput`** — `PAPER_CLOSED_EXTERNAL`.

The literal Möbius polynomial-phase cancellation statement, carried as an explicit
hypothesis.  It is **not** proved in this repository and it is **not** an axiom: every
theorem that uses it keeps it visible in its assumption chain. -/
structure MobiusPolynomialPhaseInput (Xr n : ℕ) (bound : ℝ) : Prop where
  /-- Cancellation of the Möbius function against every additive phase mod `n`. -/
  cancellation : ∀ h : ℕ, h < n →
    ‖∑ m ∈ Finset.range Xr,
      ((ArithmeticFunction.moebius m : ℤ) : ℂ) * eAdd n ((h : ℤ) * (m : ℤ))‖ ≤ bound

/-- **`mobiusPolyPhase_is_a_genuine_constraint`.**  `KERNEL-PROVED` counterguard.  The input
is not a `True`-like proposition: it fails for a negative bound. -/
theorem mobiusPolyPhase_is_a_genuine_constraint :
    ¬ MobiusPolynomialPhaseInput 1 1 (-1 : ℝ) := by
  intro h
  have hc := h.cancellation 0 Nat.one_pos
  exact absurd hc (not_le.mpr (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (norm_nonneg _)))

/-- **`smallModulus_compiler`.**  `CONDITIONAL KERNEL-PROVED`.

From the external Möbius polynomial-phase input and the kernel-proved finite Fourier
expansion, the twisted Möbius sum against **any** `n`-periodic weight `f` obeys

```
‖∑_{m < X} μ(m) f(m mod n)‖  ≤  (∑_h |f̂(h)|) · bound,
```

which combined with `fourier_l1_le_sqrt_l2` gives the `√n L²` form.  The analytic input is an
explicit hypothesis. -/
theorem smallModulus_compiler {Xr n : ℕ} (hn : 0 < n) {bound : ℝ}
    (paper : MobiusPolynomialPhaseInput Xr n bound) (f : ℕ → ℂ) :
    ‖∑ m ∈ Finset.range Xr, ((ArithmeticFunction.moebius m : ℤ) : ℂ) * f (m % n)‖
      ≤ (∑ h ∈ Finset.range n, ‖fourierCoeff n f h‖) * bound := by
  have hexp : ∀ m : ℕ, f (m % n)
      = ∑ h ∈ Finset.range n, fourierCoeff n f h * eAdd n ((h : ℤ) * ((m % n : ℕ) : ℤ)) := by
    intro m
    exact (fourier_inversion hn f (Nat.mod_lt m hn)).symm
  have hphase : ∀ (h m : ℕ), eAdd n ((h : ℤ) * ((m % n : ℕ) : ℤ)) = eAdd n ((h : ℤ) * (m : ℤ)) := by
    intro h m
    refine eAdd_congr_of_modEq hn ?_
    have hm : (n : ℤ) ∣ (((m % n : ℕ) : ℤ) - (m : ℤ)) := by
      have h2 := Nat.div_add_mod m n
      have h3 : ((n : ℤ)) * ((m / n : ℕ) : ℤ) + ((m % n : ℕ) : ℤ) = (m : ℤ) := by
        exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) h2
      exact ⟨-((m / n : ℕ) : ℤ), by linarith⟩
    have hrw : (h : ℤ) * ((m % n : ℕ) : ℤ) - (h : ℤ) * (m : ℤ)
        = (h : ℤ) * (((m % n : ℕ) : ℤ) - (m : ℤ)) := by ring
    rw [hrw]
    exact Dvd.dvd.mul_left hm _
  have hswap : ∑ m ∈ Finset.range Xr, ((ArithmeticFunction.moebius m : ℤ) : ℂ) * f (m % n)
      = ∑ h ∈ Finset.range n, fourierCoeff n f h *
          ∑ m ∈ Finset.range Xr,
            ((ArithmeticFunction.moebius m : ℤ) : ℂ) * eAdd n ((h : ℤ) * (m : ℤ)) := by
    have hterm : ∀ m ∈ Finset.range Xr,
        ((ArithmeticFunction.moebius m : ℤ) : ℂ) * f (m % n)
          = ∑ h ∈ Finset.range n, fourierCoeff n f h *
              (((ArithmeticFunction.moebius m : ℤ) : ℂ) * eAdd n ((h : ℤ) * (m : ℤ))) := by
      intro m _
      rw [hexp m, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun h _ => ?_)
      rw [hphase h m]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun h _ => (Finset.mul_sum _ _ _).symm)
  rw [hswap]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun h hh => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (paper.cancellation h (Finset.mem_range.1 hh)) (norm_nonneg _)

end SmallModulus
end Run1B
