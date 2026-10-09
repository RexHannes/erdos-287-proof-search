import Mathlib

/-!
# Erdős #287 — V100R2 source chain: Poisson remainders and the `F_{AB}` routing algebra

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

§2.6 / §3 of the request (message-level source; the V100R2 text itself was not supplied).

* `poissonP Ψ I T q a = ∑'_{n ≡ a (q)} Ψ(n/T) - (T/q) I` — the Poisson remainder
  `𝒫_T(q,a)` of a weight `Ψ` with `I = ∫Ψ` (a real parameter: the identities below are exact
  for every value of `I`, and for every `Ψ`, with Lean's `tsum` convention).
* `poissonP_scale` — **Möbius scaling**: `𝒫_M(kq, ka) = 𝒫_{M/k}(q, a)` for `k ≥ 1`.
* `rho_factor` — if `ρ ≡ 0 (mod k)` then `ρ = k ρ̃` and `ρ ≡ k s (mod k q₀) ↔ s ≡ ρ̃ (mod q₀)`
  (the unique factorisation `ρ_k ≡ k ρ̃_k (mod k q₀)`).
* `rho_crt` — for `(k, q₀) = 1` there is `ρ_k` with `ρ_k ≡ 0 (k)`, `ρ_k ≡ a (q₀)`, and with an
  explicit inverse `k k̄ ≡ 1 (q₀)` its cofactor satisfies `ρ̃_k ≡ a k̄ (mod q₀)`.
* `poissonP_rho` — `𝒫_M(k q₀, ρ_k) = 𝒫_{M/k}(q₀, ρ̃_k)`.
* `lattice_discrepancy` — **bounded-variation lattice discrepancy** (integer lattice):
  `|∑_{n<N} g(n) - ∫_0^N g| ≤ Var_{[0,N]}(g)` for interval-integrable `g` of finite variation.
-/

open scoped BigOperators
open Finset MeasureTheory

namespace Erdos287.SourceChain

/-! ### The Poisson remainder and its scaling identity -/

/-- `𝒫_T(q,a) = ∑'_{n ≡ a (q)} Ψ(n/T) - (T/q) · I`. -/
noncomputable def poissonP (Ψ : ℝ → ℝ) (I T : ℝ) (q a : ℕ) : ℝ :=
  (∑' n : ℕ, if n ≡ a [MOD q] then Ψ ((n : ℝ) / T) else 0) - T / q * I

/-- **Möbius scaling.**  `𝒫_M(kq, ka) = 𝒫_{M/k}(q, a)` for `k ≥ 1`. -/
theorem poissonP_scale (Ψ : ℝ → ℝ) (I M : ℝ) {k : ℕ} (hk : 0 < k) (q a : ℕ) :
    poissonP Ψ I M (k * q) (k * a) = poissonP Ψ I (M / k) q a := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold poissonP
  congr 1
  · have hsupp : (Function.support fun n : ℕ =>
        if n ≡ k * a [MOD k * q] then Ψ ((n : ℝ) / M) else 0) ⊆ Set.range (fun m => k * m) := by
      intro n hn
      by_contra hnot
      apply hn
      have : ¬ n ≡ k * a [MOD k * q] := by
        intro h
        have hd : k ∣ n := by
          have h1 : n ≡ k * a [MOD k] := Nat.ModEq.of_dvd (dvd_mul_right k q) h
          exact (Nat.modEq_zero_iff_dvd.1 (h1.trans (Nat.modEq_zero_iff_dvd.2
            (dvd_mul_right k a))))
        obtain ⟨m, rfl⟩ := hd
        exact hnot ⟨m, rfl⟩
      simp [this]
    rw [← Function.Injective.tsum_eq ((fun x y (h : k * x = k * y) => Nat.eq_of_mul_eq_mul_left hk h)) hsupp]
    refine tsum_congr (fun m => ?_)
    simp only [Nat.ModEq.mul_left_cancel_iff' hk.ne']
    split_ifs
    · congr 1; push_cast; field_simp
    · rfl
  · push_cast; field_simp

/-! ### The `ρ_k` factorisation -/

/-- **Unique factorisation `ρ_k ≡ k ρ̃_k (mod k q₀)`.** -/
theorem rho_factor {k q0 ρ : ℕ} (hk : 0 < k) (hρ : ρ ≡ 0 [MOD k]) :
    ∃ ρt : ℕ, ρ = k * ρt ∧ ∀ s : ℕ, (ρ ≡ k * s [MOD k * q0] ↔ ρt ≡ s [MOD q0]) := by
  obtain ⟨ρt, rfl⟩ := Nat.modEq_zero_iff_dvd.1 hρ
  exact ⟨ρt, rfl, fun s => Nat.ModEq.mul_left_cancel_iff' hk.ne'⟩

/-- **CRT residue `ρ_k`** with `ρ_k ≡ 0 (k)`, `ρ_k ≡ a (q₀)`, for `(k, q₀) = 1`; with an explicit
inverse `k k̄ ≡ 1 (mod q₀)` the cofactor is `ρ̃_k ≡ a k̄ (mod q₀)`. -/
theorem rho_crt {k q0 : ℕ} (hk : 0 < k) (hkq : Nat.Coprime k q0) (a : ℕ) {kinv : ℕ}
    (hinv : k * kinv ≡ 1 [MOD q0]) :
    ∃ ρ ρt : ℕ, ρ ≡ 0 [MOD k] ∧ ρ ≡ a [MOD q0] ∧ ρ = k * ρt ∧ ρt ≡ a * kinv [MOD q0] := by
  obtain ⟨ρ, h0, ha⟩ := Nat.chineseRemainder hkq 0 a
  obtain ⟨ρt, rfl, -⟩ := rho_factor (q0 := q0) hk h0
  refine ⟨k * ρt, ρt, h0, ha, rfl, ?_⟩
  calc ρt = 1 * ρt := (one_mul _).symm
    _ ≡ (k * kinv) * ρt [MOD q0] := hinv.symm.mul_right ρt
    _ = kinv * (k * ρt) := by ring
    _ ≡ kinv * a [MOD q0] := ha.mul_left kinv
    _ = a * kinv := by ring

/-- **`𝒫_M(k q₀, ρ_k) = 𝒫_{M/k}(q₀, ρ̃_k)`.** -/
theorem poissonP_rho (Ψ : ℝ → ℝ) (I M : ℝ) {k q0 ρ : ℕ} (hk : 0 < k) (hρ : ρ ≡ 0 [MOD k]) :
    ∃ ρt : ℕ, ρ = k * ρt ∧ poissonP Ψ I M (k * q0) ρ = poissonP Ψ I (M / k) q0 ρt := by
  obtain ⟨ρt, rfl, -⟩ := rho_factor (q0 := q0) hk hρ
  exact ⟨ρt, rfl, poissonP_scale Ψ I M hk q0 ρt⟩

/-! ### Bounded-variation lattice discrepancy -/

theorem abs_sub_le_var (g : ℝ → ℝ) {a b x y : ℝ} (hfin : eVariationOn g (Set.Icc a b) ≠ ⊤)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |g x - g y| ≤ (eVariationOn g (Set.Icc a b)).toReal := by
  have h := eVariationOn.edist_le g hx hy
  rw [edist_dist, Real.dist_eq] at h
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 h

theorem var_sum_range (g : ℝ → ℝ) (N : ℕ) :
    ∑ n ∈ range N, eVariationOn g (Set.Icc (n : ℝ) (n + 1)) =
      eVariationOn g (Set.Icc 0 (N : ℝ)) := by
  induction N with
  | zero => simp [Set.Icc_self]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have := eVariationOn.Icc_add_Icc g (s := Set.univ) (a := 0) (b := (N : ℝ)) (c := N + 1)
      (by positivity) (by linarith) (Set.mem_univ _)
    simp only [Set.univ_inter] at this
    push_cast
    exact this

theorem unit_discrepancy (g : ℝ → ℝ) (a : ℝ) (hint : IntervalIntegrable g volume a (a + 1))
    (hfin : eVariationOn g (Set.Icc a (a + 1)) ≠ ⊤) :
    |g a - ∫ t in a..(a + 1), g t| ≤ (eVariationOn g (Set.Icc a (a + 1))).toReal := by
  have h1 : g a - ∫ t in a..(a + 1), g t = ∫ t in a..(a + 1), (g a - g t) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hint]
    simp
  rw [h1, ← Real.norm_eq_abs]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + 1)
    (f := fun t => g a - g t) (C := (eVariationOn g (Set.Icc a (a + 1))).toReal) (by
      intro t ht
      rw [Set.uIoc_of_le (by linarith)] at ht
      rw [Real.norm_eq_abs]
      exact abs_sub_le_var g hfin ⟨le_rfl, by linarith⟩ ⟨ht.1.le, ht.2⟩)
  simpa using this

/-- **Bounded-variation lattice discrepancy.**
`|∑_{n<N} g(n) - ∫_0^N g| ≤ Var_{[0,N]}(g)`. -/
theorem lattice_discrepancy (g : ℝ → ℝ) (N : ℕ)
    (hint : IntervalIntegrable g volume 0 N)
    (hbv : eVariationOn g (Set.Icc 0 (N : ℝ)) ≠ ⊤) :
    |∑ n ∈ range N, g n - ∫ t in (0 : ℝ)..N, g t| ≤
      (eVariationOn g (Set.Icc 0 (N : ℝ))).toReal := by
  have hfin : ∀ n ∈ range N, eVariationOn g (Set.Icc (n : ℝ) (n + 1)) ≠ ⊤ := by
    intro n hn
    refine ne_top_of_le_ne_top hbv (eVariationOn.mono g ?_)
    have := Finset.mem_range.1 hn
    intro t ht; refine ⟨le_trans (by positivity) ht.1, le_trans ht.2 ?_⟩
    exact_mod_cast this
  have hint' : ∀ n < N, IntervalIntegrable g volume (n : ℝ) (n + 1) := by
    intro n hn
    refine hint.mono_set ?_
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by positivity)]
    intro t ht; refine ⟨le_trans (by positivity) ht.1, le_trans ht.2 ?_⟩
    exact_mod_cast hn
  have hsplit : ∫ t in (0 : ℝ)..N, g t = ∑ n ∈ range N, ∫ t in (n : ℝ)..(n + 1), g t := by
    have := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := volume)
      (a := fun n : ℕ => (n : ℝ)) (n := N) (fun k hk => by
        simpa using hint' k hk)
    simpa using this.symm
  rw [hsplit, ← Finset.sum_sub_distrib, ← var_sum_range, ENNReal.toReal_sum hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun n hn => ?_))
  exact unit_discrepancy g n (hint' n (Finset.mem_range.1 hn)) (hfin n hn)

end Erdos287.SourceChain
