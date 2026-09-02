import RequestProject.CurrentProgramme.Run1BEffectiveModulus

/-!
# RUN1B / d*wp provider — §3  the finite Fourier matrix at the effective modulus

```
K(u,v) = e_{r♯}(−A♯ u v)                        : DEFINED (unnormalised)
row / column permutation by invertible A♯       : KERNEL-PROVED
exact finite orthogonality                      : KERNEL-PROVED
‖K x‖₂² = r♯ ‖x‖₂²   (operator norm √r♯)        : KERNEL-PROVED
```

**Normalisation is explicit and is not hidden.**  In this file the matrix carries *no*
`1/√r♯` factor, so `K` is `√r♯` times a unitary matrix: the full-period orthogonality sum is
`r♯`, and the operator norm of `K` is exactly `√r♯`.

This module is **append-only** and project-neutral: no analytic input, no analytic output.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Run1B
namespace FourierMatrix

open Run1B.Characters Run1B.EffectiveModulus

/-- The finite Fourier matrix at modulus `n` with invertible numerator `a`, in the
**unnormalised** convention: `K(u, v) = exp(2 π i (−a u v)/n)`. -/
noncomputable def Kmat (n : ℕ) (a : ℤ) (u v : ℤ) : ℂ := eAdd n (-(a * u * v))

/-! ## §3.1  Multiplication by an invertible `a` permutes rows and columns -/

/-- **`Kmat_row_scaling`.**  `KERNEL-PROVED`.  The `a`-matrix is the standard Fourier matrix
with its rows relabelled by `u ↦ a u`. -/
theorem Kmat_row_scaling (n : ℕ) (a u v : ℤ) : Kmat n a u v = Kmat n 1 (a * u) v := by
  unfold Kmat
  congr 1
  ring

/-- **`Kmat_col_scaling`.**  `KERNEL-PROVED`.  Likewise for the columns. -/
theorem Kmat_col_scaling (n : ℕ) (a u v : ℤ) : Kmat n a u v = Kmat n 1 u (a * v) := by
  unfold Kmat
  congr 1
  ring

/-- **`mulLeft_bijective_of_coprime`.**  `KERNEL-PROVED`.  Multiplication by an invertible
residue is a permutation of `ZMod n`. -/
theorem mulLeft_bijective_of_coprime {n : ℕ} {a : ℤ} (ha : Int.gcd a (n : ℤ) = 1) :
    Function.Bijective (fun z : ZMod n => (a : ZMod n) * z) := by
  obtain ⟨b, hb⟩ : ∃ b : ZMod n, (a : ZMod n) * b = 1 := by
    obtain ⟨p, q, hpq⟩ := Int.isCoprime_iff_gcd_eq_one.mpr ha
    refine ⟨(p : ZMod n), ?_⟩
    have h : ((p * a + q * (n : ℤ) : ℤ) : ZMod n) = ((1 : ℤ) : ZMod n) := by rw [hpq]
    push_cast at h
    rw [ZMod.natCast_self] at h
    simpa [mul_comm] using h
  refine ⟨fun z z' hzz => ?_, fun w => ⟨b * w, ?_⟩⟩
  · have h' : (a : ZMod n) * z = (a : ZMod n) * z' := hzz
    calc z = (b * (a : ZMod n)) * z := by rw [mul_comm b, hb, one_mul]
      _ = b * ((a : ZMod n) * z) := by ring
      _ = b * ((a : ZMod n) * z') := by rw [h']
      _ = (b * (a : ZMod n)) * z' := by ring
      _ = z' := by rw [mul_comm b, hb, one_mul]
  · show (a : ZMod n) * (b * w) = w
    rw [← mul_assoc, hb, one_mul]

/-- **`sum_reindex_by_invertible`.**  `KERNEL-PROVED`.  Consequently, summing a function of
the row index over a full period is invariant under `u ↦ a u`: the rows of `K` really are a
permutation of the standard rows. -/
theorem sum_reindex_by_invertible {n : ℕ} [NeZero n] {a : ℤ} (ha : Int.gcd a (n : ℤ) = 1)
    (f : ZMod n → ℂ) : ∑ z : ZMod n, f ((a : ZMod n) * z) = ∑ z : ZMod n, f z :=
  Fintype.sum_bijective _ (mulLeft_bijective_of_coprime ha) _ _ (fun _ => rfl)

/-- **`not_dvd_sub_of_lt`.**  `KERNEL-PROVED`.  Two distinct residues of a full period are
never congruent. -/
theorem not_dvd_sub_of_lt {n u u' : ℕ} (hu : u < n) (hu' : u' < n) (hne : u ≠ u') :
    ¬ (n : ℤ) ∣ (u : ℤ) - (u' : ℤ) := by
  rintro ⟨k, hk⟩
  have hnZ : (0 : ℤ) < (n : ℤ) := by exact_mod_cast (by omega : 0 < n)
  have huZ : (u : ℤ) < (n : ℤ) := by exact_mod_cast hu
  have hu'Z : (u' : ℤ) < (n : ℤ) := by exact_mod_cast hu'
  have hu0 : (0 : ℤ) ≤ (u : ℤ) := Int.natCast_nonneg u
  have hu'0 : (0 : ℤ) ≤ (u' : ℤ) := Int.natCast_nonneg u'
  have hne' : (u : ℤ) ≠ (u' : ℤ) := by exact_mod_cast hne
  rcases lt_trichotomy k 0 with h | h | h
  · have hle : (n : ℤ) * k ≤ (n : ℤ) * (-1) :=
      mul_le_mul_of_nonneg_left (by omega) (le_of_lt hnZ)
    rw [mul_neg_one] at hle
    linarith
  · rw [h, mul_zero] at hk
    exact hne' (by linarith)
  · have hle : (n : ℤ) * 1 ≤ (n : ℤ) * k :=
      mul_le_mul_of_nonneg_left (by omega) (le_of_lt hnZ)
    rw [mul_one] at hle
    linarith

/-! ## §3.2  Exact finite orthogonality -/

/-- **`Kmat_row_orthogonality`.**  `KERNEL-PROVED`.  The exact orthogonality relation of the
rows of `K`, in the unnormalised convention: the diagonal value is `n`, not `1`. -/
theorem Kmat_row_orthogonality {n : ℕ} (hn : 0 < n) {a : ℤ} (ha : Int.gcd a (n : ℤ) = 1)
    (u u' : ℤ) :
    ∑ v ∈ Finset.range n, Kmat n a u v * (starRingEnd ℂ) (Kmat n a u' v)
      = if (n : ℤ) ∣ u - u' then (n : ℂ) else 0 := by
  have hterm : ∀ v ∈ Finset.range n,
      Kmat n a u v * (starRingEnd ℂ) (Kmat n a u' v) = eAdd n ((a * (u' - u)) * (v : ℤ)) := by
    intro v _
    unfold Kmat
    rw [eAdd_conj, ← eAdd_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl hterm, eAdd_orthogonality hn]
  by_cases h : (n : ℤ) ∣ u - u'
  · have h' : (n : ℤ) ∣ a * (u' - u) := by
      have h2 : (n : ℤ) ∣ u' - u := by simpa [neg_sub] using (dvd_neg.mpr h)
      exact Dvd.dvd.mul_left h2 a
    rw [if_pos h', if_pos h]
  · have h' : ¬ (n : ℤ) ∣ a * (u' - u) := by
      intro hc
      have hcop : Int.gcd (n : ℤ) a = 1 := by rw [Int.gcd_comm]; exact ha
      have h2 : (n : ℤ) ∣ (u' - u) := by
        refine Int.dvd_of_dvd_mul_left_of_gcd_one ?_ hcop
        simpa [mul_comm] using hc
      exact h (by simpa [neg_sub] using (dvd_neg.mpr h2))
    rw [if_neg h', if_neg h]

/-- **`Kmat_orthogonality_diagonal`.**  `KERNEL-PROVED`.  The diagonal case, stated
separately so that the normalisation is unmistakable. -/
theorem Kmat_orthogonality_diagonal {n : ℕ} (hn : 0 < n) {a : ℤ} (ha : Int.gcd a (n : ℤ) = 1)
    (u : ℤ) : ∑ v ∈ Finset.range n, Kmat n a u v * (starRingEnd ℂ) (Kmat n a u v) = (n : ℂ) := by
  rw [Kmat_row_orthogonality hn ha u u, if_pos (by simp)]

/-! ## §3.3  The operator norm is exactly `√n` -/

/-- **`Kmat_scaled_isometry`.**  `KERNEL-PROVED`.  The exact Plancherel identity for the
unnormalised matrix `K`:

```
∑_v |(K x)(v)|²  =  n · ∑_u |x(u)|².
```

Equivalently `K = √n · (unitary)`, i.e. the operator norm of `K` is exactly `√n`. -/
theorem Kmat_scaled_isometry {n : ℕ} (hn : 0 < n) {a : ℤ} (ha : Int.gcd a (n : ℤ) = 1)
    (x : ℕ → ℂ) :
    ∑ v ∈ Finset.range n,
        (∑ u ∈ Finset.range n, Kmat n a (u : ℤ) (v : ℤ) * x u) *
          (starRingEnd ℂ) (∑ u ∈ Finset.range n, Kmat n a (u : ℤ) (v : ℤ) * x u)
      = (n : ℂ) * ∑ u ∈ Finset.range n, x u * (starRingEnd ℂ) (x u) := by
  have expand : ∀ v ∈ Finset.range n,
      (∑ u ∈ Finset.range n, Kmat n a (u : ℤ) (v : ℤ) * x u) *
          (starRingEnd ℂ) (∑ u ∈ Finset.range n, Kmat n a (u : ℤ) (v : ℤ) * x u)
        = ∑ u ∈ Finset.range n, ∑ u' ∈ Finset.range n,
            (Kmat n a (u : ℤ) (v : ℤ) * x u) *
              (starRingEnd ℂ) (Kmat n a (u' : ℤ) (v : ℤ) * x u') := by
    intro v _
    rw [map_sum, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl expand, Finset.sum_comm]
  have inner : ∀ u ∈ Finset.range n,
      ∑ v ∈ Finset.range n, ∑ u' ∈ Finset.range n,
          (Kmat n a (u : ℤ) (v : ℤ) * x u) *
            (starRingEnd ℂ) (Kmat n a (u' : ℤ) (v : ℤ) * x u')
        = x u * (starRingEnd ℂ) (x u) * (n : ℂ) := by
    intro u hu
    rw [Finset.sum_comm]
    have step : ∀ u' ∈ Finset.range n,
        ∑ v ∈ Finset.range n, (Kmat n a (u : ℤ) (v : ℤ) * x u) *
            (starRingEnd ℂ) (Kmat n a (u' : ℤ) (v : ℤ) * x u')
          = (x u * (starRingEnd ℂ) (x u')) *
              (if (n : ℤ) ∣ (u : ℤ) - (u' : ℤ) then (n : ℂ) else 0) := by
      intro u' _
      rw [← Kmat_row_orthogonality hn ha (u : ℤ) (u' : ℤ), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [map_mul]
      ring
    rw [Finset.sum_congr rfl step]
    rw [Finset.sum_eq_single u]
    · rw [if_pos (by simp)]
    · intro u' hu' hne
      have hdvd : ¬ (n : ℤ) ∣ (u : ℤ) - (u' : ℤ) :=
        not_dvd_sub_of_lt (Finset.mem_range.1 hu) (Finset.mem_range.1 hu') (Ne.symm hne)
      rw [if_neg hdvd, mul_zero]
    · intro hcon
      exact absurd hu hcon
  rw [Finset.sum_congr rfl inner, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun u _ => by ring)

/-- **`Kmat_operator_norm_sqrt`.**  `KERNEL-PROVED`.  The real form of the previous identity:

```
∑_v ‖(K x)(v)‖²  =  n · ∑_u ‖x(u)‖²,
```

so the operator norm of the unnormalised matrix `K` is exactly `√n`. -/
theorem Kmat_operator_norm_sqrt {n : ℕ} (hn : 0 < n) {a : ℤ} (ha : Int.gcd a (n : ℤ) = 1)
    (x : ℕ → ℂ) :
    ∑ v ∈ Finset.range n, ‖∑ u ∈ Finset.range n, Kmat n a (u : ℤ) (v : ℤ) * x u‖ ^ 2
      = (n : ℝ) * ∑ u ∈ Finset.range n, ‖x u‖ ^ 2 := by
  have key := Kmat_scaled_isometry hn ha x
  have hL : ((∑ v ∈ Finset.range n,
      ‖∑ u ∈ Finset.range n, Kmat n a (u : ℤ) (v : ℤ) * x u‖ ^ 2 : ℝ) : ℂ)
      = ∑ v ∈ Finset.range n,
        (∑ u ∈ Finset.range n, Kmat n a (u : ℤ) (v : ℤ) * x u) *
          (starRingEnd ℂ) (∑ u ∈ Finset.range n, Kmat n a (u : ℤ) (v : ℤ) * x u) := by
    push_cast
    exact Finset.sum_congr rfl (fun v _ => (RCLike.mul_conj _).symm)
  have hR : (((n : ℝ) * ∑ u ∈ Finset.range n, ‖x u‖ ^ 2 : ℝ) : ℂ)
      = (n : ℂ) * ∑ u ∈ Finset.range n, x u * (starRingEnd ℂ) (x u) := by
    push_cast
    congr 1
    exact Finset.sum_congr rfl (fun u _ => (RCLike.mul_conj _).symm)
  have : ((∑ v ∈ Finset.range n,
      ‖∑ u ∈ Finset.range n, Kmat n a (u : ℤ) (v : ℤ) * x u‖ ^ 2 : ℝ) : ℂ)
      = (((n : ℝ) * ∑ u ∈ Finset.range n, ‖x u‖ ^ 2 : ℝ) : ℂ) := by
    rw [hL, hR, key]
  exact_mod_cast this

/-- **`Kmat_normalisation_is_explicit`.**  `KERNEL-PROVED` counterguard.  With `n ≥ 2` the
matrix is *not* an isometry: the identity above genuinely carries the factor `n`, so no
normalisation has been silently absorbed. -/
theorem Kmat_normalisation_is_explicit {n : ℕ} (hn : 1 < n) {a : ℤ}
    (ha : Int.gcd a (n : ℤ) = 1) :
    ∑ v ∈ Finset.range n,
        ‖∑ u ∈ Finset.range n, Kmat n a (u : ℤ) (v : ℤ) * (if u = 0 then (1 : ℂ) else 0)‖ ^ 2
      ≠ ∑ u ∈ Finset.range n, ‖(if u = 0 then (1 : ℂ) else 0)‖ ^ 2 := by
  have h0 : 0 < n := lt_trans Nat.zero_lt_one hn
  rw [Kmat_operator_norm_sqrt h0 ha]
  have hx : ∑ u ∈ Finset.range n, ‖(if u = 0 then (1 : ℂ) else 0)‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single 0]
    · norm_num
    · intro b _ hb
      simp [hb]
    · intro hc
      exact absurd (Finset.mem_range.2 h0) hc
  rw [hx, mul_one]
  have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact ne_of_gt this

end FourierMatrix
end Run1B
