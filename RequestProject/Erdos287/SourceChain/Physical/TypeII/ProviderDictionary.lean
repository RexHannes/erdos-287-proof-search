import RequestProject.Erdos287.SourceChain.Physical.Factorization.ActualParams

/-!
# Erdős #287 — source-to-provider dictionary (ranges and coefficients)

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

**Source-fit decision.**  Pascadi's Proposition 5.2 is used *only* to produce, for each modulus,
a factorization `d = d₁ d₂ d₃` obeying the size system (5.3); the downstream trilinear estimate
consumes one-bounded coefficient sequences `γ_q, ν_s, λ_r` supported on `q ≤ Q`, `s ≤ S`,
`r ≤ R` with the three range conditions of `sources/physical_spec.md` §18 (boxed):

`N² R² S ≤ x^{1-8ε}`, `N^{71/50} R S^{93/50} ≤ x^{1-16ε}`,
`N^{39/25} Q^{11/25} R² S⁵ ≤ x^{2-32ε}`, with `ε = κ/2000`.

The physical source already supplies the factorization directly (allocation at the actual box
upper endpoints, fixed over each box, low factor in `d₁`), so literal membership of each complete
modulus `b ∏ q_i` in `𝒟⁺(x^{3/5-50κ})` is **not** an input of this interface and is not
retained as a blocker.

Proved here:

* `boxed_one`, `boxed_two`, `boxed_three` — the three boxed inequalities from (5.3)-type bounds
  (generic real lemmas; `boxed_two` uses `N ≤ x^{1/3+κ/2}`).
* `boxed_mono` — the boxed conditions pass to any dyadic sub-box `Q' ≤ Q`, `R' ≤ R`, `S' ≤ S`.
* `physCoefAtom_eq_dict` — **coefficient dictionary**: the constructed Type-II coefficient of an
  atom is `σ · a₁(l) · (a₂ * a₃)(r)` with `σ = Γ (-1)^J w_{J,P}`, `a₁ = κ_J * γ_{0,χ}`,
  `a₂ = γ_{1,χ}`, `a₃ = γ_{2,χ}`, gated by `P ∈ 𝐃_J^+` and `(f, l r) = 1`.
* `physAtom_provider_contract` — for every admissible sector of an actual critical cell
  (`CritRegime`, `CritCell`), with `Q = N X^{-κ}`, `S = E₁`, `R = E₂`: one-boundedness, supports,
  pairwise coprimality, `|σ| ≤ |Γ| w`, and the three boxed range conditions.
-/

open Finset Real

set_option autoImplicit false

namespace Erdos287.Physical.TypeII

open Erdos287.Physical.Sieve Erdos287.Physical.Sieve.ScalarParams Erdos287.Physical.Factor

lemma pow_rpow_eq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (y : ℝ) : (x ^ n) ^ y = x ^ ((n : ℝ) * y) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

/-- **First boxed condition** `N² R² S ≤ x^{1-8ε}` (`ε = κ/2000`). -/
theorem boxed_one {x κ N R S : ℝ} (hx : 1 < x) (hκ : 0 ≤ κ)
    (h2 : N ^ 2 * S * R ^ 2 ≤ x ^ (1 - κ / 2)) :
    N ^ 2 * R ^ 2 * S ≤ x ^ (1 - 8 * (κ / 2000)) := by
  calc N ^ 2 * R ^ 2 * S = N ^ 2 * S * R ^ 2 := by ring
    _ ≤ x ^ (1 - κ / 2) := h2
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)

/-- **Second boxed condition** `N^{71/50} R S^{93/50} ≤ x^{1-16ε}` (`ε = κ/2000`). -/
theorem boxed_two {x κ N R S : ℝ} (hx : 1 < x) (hκ : 0 ≤ κ) (hN : 0 ≤ N) (hR : 0 ≤ R)
    (hS : 0 ≤ S) (hNhi : N ≤ x ^ (1 / 3 + κ / 2))
    (h2 : N ^ 2 * S * R ^ 2 ≤ x ^ (1 - κ / 2)) (h3 : N ^ 2 * S ^ 5 * R ^ 2 ≤ x ^ (2 - κ / 2)) :
    N ^ ((71 : ℝ) / 50) * R * S ^ ((93 : ℝ) / 50) ≤ x ^ (1 - 16 * (κ / 2000)) := by
  have hx0 : 0 < x := by linarith
  set A := N ^ 2 * S * R ^ 2
  set B := N ^ 2 * S ^ 5 * R ^ 2
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  have key : N ^ ((71 : ℝ) / 50) * R * S ^ ((93 : ℝ) / 50) =
      A ^ ((8 : ℝ) / 50) * B ^ ((17 : ℝ) / 50) * N ^ ((21 : ℝ) / 50) := by
    simp only [A, B]
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hS,
      Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      pow_rpow_eq hN, pow_rpow_eq hR, pow_rpow_eq hS, pow_rpow_eq hN, pow_rpow_eq hR]
    have eN : N ^ ((71 : ℝ) / 50) = N ^ ((2 : ℕ) * ((8 : ℝ) / 50)) *
        N ^ ((2 : ℕ) * ((17 : ℝ) / 50)) * N ^ ((21 : ℝ) / 50) := by
      rw [← Real.rpow_add' hN (by norm_num), ← Real.rpow_add' hN (by norm_num)]
      norm_num
    have eR : R = R ^ ((2 : ℕ) * ((8 : ℝ) / 50)) * R ^ ((2 : ℕ) * ((17 : ℝ) / 50)) := by
      rw [← Real.rpow_add' hR (by norm_num)]
      norm_num
    have eS : S ^ ((93 : ℝ) / 50) = S ^ ((8 : ℝ) / 50) * S ^ ((5 : ℕ) * ((17 : ℝ) / 50)) := by
      rw [← Real.rpow_add' hS (by norm_num)]
      norm_num
    rw [eN, eS]
    conv_lhs => rw [eR]
    ring
  rw [key]
  have b1 : A ^ ((8 : ℝ) / 50) ≤ x ^ ((1 - κ / 2) * (8 / 50)) := by
    rw [Real.rpow_mul hx0.le]; exact Real.rpow_le_rpow hA h2 (by norm_num)
  have b2 : B ^ ((17 : ℝ) / 50) ≤ x ^ ((2 - κ / 2) * (17 / 50)) := by
    rw [Real.rpow_mul hx0.le]; exact Real.rpow_le_rpow hB h3 (by norm_num)
  have b3 : N ^ ((21 : ℝ) / 50) ≤ x ^ ((1 / 3 + κ / 2) * (21 / 50)) := by
    rw [Real.rpow_mul hx0.le]; exact Real.rpow_le_rpow hN hNhi (by norm_num)
  calc A ^ ((8 : ℝ) / 50) * B ^ ((17 : ℝ) / 50) * N ^ ((21 : ℝ) / 50)
      ≤ x ^ ((1 - κ / 2) * (8 / 50)) * x ^ ((2 - κ / 2) * (17 / 50)) *
          x ^ ((1 / 3 + κ / 2) * (21 / 50)) := by
        gcongr
    _ = x ^ (49 / 50 - κ / 25) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; ring_nf
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)

/-- **Third boxed condition** `N^{39/25} Q^{11/25} R² S⁵ ≤ x^{2-32ε}` (`ε = κ/2000`). -/
theorem boxed_three {x κ N Q R S : ℝ} (hx : 1 < x) (hκ : 0 ≤ κ) (hN : 0 ≤ N) (hQ : 0 ≤ Q)
    (hQhi : Q ≤ N * x ^ (-κ)) (h3 : N ^ 2 * S ^ 5 * R ^ 2 ≤ x ^ (2 - κ / 2)) :
    N ^ ((39 : ℝ) / 25) * Q ^ ((11 : ℝ) / 25) * R ^ 2 * S ^ 5 ≤ x ^ (2 - 32 * (κ / 2000)) := by
  have hx0 : 0 < x := by linarith
  have hQ' : Q ^ ((11 : ℝ) / 25) ≤ N ^ ((11 : ℝ) / 25) * x ^ (-κ * (11 / 25)) := by
    rw [Real.rpow_mul hx0.le, ← Real.mul_rpow hN (Real.rpow_nonneg hx0.le _)]
    exact Real.rpow_le_rpow hQ hQhi (by norm_num)
  have eN : N ^ ((39 : ℝ) / 25) * N ^ ((11 : ℝ) / 25) = N ^ 2 := by
    rw [← Real.rpow_add' hN (by norm_num)]; norm_num
  by_cases hS5 : 0 ≤ S ^ 5
  · calc N ^ ((39 : ℝ) / 25) * Q ^ ((11 : ℝ) / 25) * R ^ 2 * S ^ 5
        ≤ N ^ ((39 : ℝ) / 25) * (N ^ ((11 : ℝ) / 25) * x ^ (-κ * (11 / 25))) * R ^ 2 * S ^ 5 := by
          gcongr
      _ = (N ^ 2 * S ^ 5 * R ^ 2) * x ^ (-κ * (11 / 25)) := by
          rw [← eN]; ring
      _ ≤ x ^ (2 - κ / 2) * x ^ (-κ * (11 / 25)) := by
          gcongr
      _ = x ^ (2 - κ / 2 - κ * (11 / 25)) := by rw [← Real.rpow_add hx0]; ring_nf
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  · have hneg : N ^ ((39 : ℝ) / 25) * Q ^ ((11 : ℝ) / 25) * R ^ 2 * S ^ 5 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_lt (not_le.1 hS5))
    exact hneg.trans (Real.rpow_nonneg hx0.le _)

/-- The boxed conditions are monotone: they pass to every sub-box `Q' ≤ Q`, `R' ≤ R`,
`S' ≤ S` (in particular to every dyadic block below the box endpoints). -/
theorem boxed_mono {x κ N Q R S Q' R' S' : ℝ} (hN : 0 ≤ N) (hQ' : 0 ≤ Q') (hR' : 0 ≤ R')
    (hS' : 0 ≤ S') (hQQ : Q' ≤ Q) (hRR : R' ≤ R) (hSS : S' ≤ S)
    (h1 : N ^ 2 * R ^ 2 * S ≤ x ^ (1 - 8 * (κ / 2000)))
    (h2 : N ^ ((71 : ℝ) / 50) * R * S ^ ((93 : ℝ) / 50) ≤ x ^ (1 - 16 * (κ / 2000)))
    (h3 : N ^ ((39 : ℝ) / 25) * Q ^ ((11 : ℝ) / 25) * R ^ 2 * S ^ 5 ≤
      x ^ (2 - 32 * (κ / 2000))) :
    N ^ 2 * R' ^ 2 * S' ≤ x ^ (1 - 8 * (κ / 2000)) ∧
      N ^ ((71 : ℝ) / 50) * R' * S' ^ ((93 : ℝ) / 50) ≤ x ^ (1 - 16 * (κ / 2000)) ∧
      N ^ ((39 : ℝ) / 25) * Q' ^ ((11 : ℝ) / 25) * R' ^ 2 * S' ^ 5 ≤
        x ^ (2 - 32 * (κ / 2000)) := by
  have hR : 0 ≤ R := hR'.trans hRR
  have hQ : 0 ≤ Q := hQ'.trans hQQ
  refine ⟨le_trans ?_ h1, le_trans ?_ h2, le_trans ?_ h3⟩ <;> gcongr

variable {S : ScalarParams}

/-- The low factor is coprime to each high colour factor (`k = 1, 2`). -/
theorem lowFactor_coprime_col (hS : S.Good) {J : ℕ} {P : Fin J → Fin S.H} {c : ℕ → Fin 3}
    {χ : Fin S.Kc → Fin 3} {k : Fin 3} (hk0 : k ≠ 0) {l s : ℕ}
    (hl : S.lowFactor J P c χ l ≠ 0) (hs : S.colFactor J P c χ k s ≠ 0) : Nat.Coprime l s := by
  obtain ⟨x, hx, hk, hc⟩ := lowFactor_term_ne hl
  obtain ⟨hxm, -⟩ := Nat.mem_divisorsAntidiagonal.1 hx
  obtain ⟨hsqb, hlow⟩ := kappa_support hk
  obtain ⟨-, h0, -⟩ := colFactor_support hS hc
  obtain ⟨-, h1, -⟩ := colFactor_support hS hs
  have hx1 : x.1 ≠ 0 := hsqb.ne_zero
  refine Nat.coprime_of_dvd (fun p hp hpl hps => ?_)
  rw [← hxm] at hpl
  rcases (Nat.Prime.dvd_mul hp).1 hpl with h | h
  · exact not_low_of_high hS (h1 p hp hps).1 (hlow p (Nat.mem_primeFactors.2 ⟨hp, h, hx1⟩))
  · exact hk0 ((h1 p hp hps).2.symm.trans (h0 p hp h).2)

/-- **Coefficient dictionary** of the constructed Type-II coefficient. -/
theorem physCoefAtom_eq_dict (δ N Γ : ℝ) (f J : ℕ) (P : Fin J → Fin S.H)
    (χ : Fin S.Kc → Fin 3) (l r : ℕ) [Decidable (S.BoxAdm J P ∧ Nat.Coprime f (l * r))] :
    physCoefAtom S δ N Γ f J P χ l r =
      if S.BoxAdm J P ∧ Nat.Coprime f (l * r) then
        (Γ * ((-1 : ℝ) ^ J * S.atomWeight J P (S.atomColour δ N J P))) *
          S.lowFactor J P (S.atomColour δ N J P) χ l *
          ∑ x ∈ r.divisorsAntidiagonal, S.colFactor J P (S.atomColour δ N J P) χ 1 x.1 *
            S.colFactor J P (S.atomColour δ N J P) χ 2 x.2
      else 0 := by
  unfold physCoefAtom
  split_ifs <;> simp [ArithmeticFunction.mul_apply, mul_assoc]

/-- **Provider contract of every admissible sector of an actual critical cell.**
With `Q = N X^{-κ}`, `S = E₁`, `R = E₂` (box-endpoint products of colours 1 and 2),
the three one-bounded factor sequences have the stated supports, pairwise coprime supports,
the sign/weight scalar is bounded by `|Γ| w`, and the three boxed range conditions hold
with `ε = κ/2000`. -/
theorem physAtom_provider_contract {κ N : ℝ} (h : CritRegime S κ) (hN : CritCell S κ N)
    (Γ : ℝ) {J : ℕ} {P : Fin J → Fin S.H} (hP : S.BoxAdm J P) (χ : Fin S.Kc → Fin 3) :
    let c := S.atomColour κ N J P
    let Q := N * S.X ^ (-κ)
    let Sb := cprod (S.boxVec J P) c 1 J
    let R := cprod (S.boxVec J P) c 2 J
    -- one-boundedness
    (∀ n, |S.lowFactor J P c χ n| ≤ 1) ∧ (∀ n, |S.colFactor J P c χ 1 n| ≤ 1) ∧
      (∀ n, |S.colFactor J P c χ 2 n| ≤ 1) ∧
    -- supports
      (∀ n, S.lowFactor J P c χ n ≠ 0 → (n : ℝ) ≤ Q) ∧
      (∀ n, S.colFactor J P c χ 1 n ≠ 0 → (n : ℝ) ≤ Sb) ∧
      (∀ n, S.colFactor J P c χ 2 n ≠ 0 → (n : ℝ) ≤ R) ∧
    -- coprime supports
      (∀ a s, S.lowFactor J P c χ a ≠ 0 → S.colFactor J P c χ 1 s ≠ 0 → Nat.Coprime a s) ∧
      (∀ a t, S.lowFactor J P c χ a ≠ 0 → S.colFactor J P c χ 2 t ≠ 0 → Nat.Coprime a t) ∧
      (∀ s t, S.colFactor J P c χ 1 s ≠ 0 → S.colFactor J P c χ 2 t ≠ 0 → Nat.Coprime s t) ∧
    -- scalar
      |Γ * ((-1 : ℝ) ^ J * S.atomWeight J P c)| ≤ |Γ| * S.atomWeight J P c ∧
    -- boxed range conditions
      N ^ 2 * R ^ 2 * Sb ≤ S.X ^ (1 - 8 * (κ / 2000)) ∧
      N ^ ((71 : ℝ) / 50) * R * Sb ^ ((93 : ℝ) / 50) ≤ S.X ^ (1 - 16 * (κ / 2000)) ∧
      N ^ ((39 : ℝ) / 25) * Q ^ ((11 : ℝ) / 25) * R ^ 2 * Sb ^ 5 ≤
        S.X ^ (2 - 32 * (κ / 2000)) := by
  intro c Q Sb R
  have hS := h.good
  have hA := atomParams_of_crit h hN
  have hX0 : 0 < S.X := by linarith [hS.X_gt]
  have hκ := h.κ_pos
  have hDl := Dlow_ge_one hS
  obtain ⟨s1, s2, s3⟩ := atomColour_spec hA hP
  have hN0 : 0 ≤ N := by
    have := (Real.rpow_pos_of_pos hX0 (2 * κ)).trans_le hA.N_lo
    exact ((div_pos_iff_of_pos_right (by linarith)).1 this).le
  have hSb : 0 ≤ Sb := prod_nonneg (fun i _ => by
    unfold boxVec; split_ifs
    · exact (boxTop_eq hS _ ▸ (boxEnd_pos hS _).le)
    · exact zero_le_one)
  have hR : 0 ≤ R := prod_nonneg (fun i _ => by
    unfold boxVec; split_ifs
    · exact (boxTop_eq hS _ ▸ (boxEnd_pos hS _).le)
    · exact zero_le_one)
  have hlow := Dlow_sq_le h
  -- the two clean `(5.3)` inequalities at `κ/2`
  have c2 : N ^ 2 * Sb * R ^ 2 ≤ S.X ^ (1 - κ / 2) := by
    calc N ^ 2 * Sb * R ^ 2 = S.Dlow ^ 2 * ((N / S.Dlow) ^ 2 * Sb * R ^ 2) := by field_simp
      _ ≤ S.X ^ (κ / 2) * S.X ^ (1 - κ) := by
          gcongr
      _ = S.X ^ (1 - κ / 2) := by rw [← Real.rpow_add hX0]; ring_nf
  have c3 : N ^ 2 * Sb ^ 5 * R ^ 2 ≤ S.X ^ (2 - κ / 2) := by
    calc N ^ 2 * Sb ^ 5 * R ^ 2 = S.Dlow ^ 2 * ((N / S.Dlow) ^ 2 * Sb ^ 5 * R ^ 2) := by
          field_simp
      _ ≤ S.X ^ (κ / 2) * S.X ^ (2 - κ) := by
          gcongr
      _ = S.X ^ (2 - κ / 2) := by rw [← Real.rpow_add hX0]; ring_nf
  refine ⟨abs_lowFactor_le hS P c χ, abs_colFactor_le hS P c χ 1, abs_colFactor_le hS P c χ 2,
    fun n hn => ?_, fun n hn => (colFactor_support hS hn).2.2,
    fun n hn => (colFactor_support hS hn).2.2, fun a s ha hs => ?_, fun a t ha ht => ?_,
    fun s t hs ht => colFactor_coprime hS (by decide) hs ht, ?_,
    boxed_one hS.X_gt hκ.le c2,
    boxed_two hS.X_gt hκ.le hN0 hR hSb hN.N_hi c2 c3,
    boxed_three hS.X_gt hκ.le hN0 (by positivity) le_rfl c3⟩
  · refine (lowFactor_support hS hn).trans ?_
    calc S.Dlow * cprod (S.boxVec J P) c 0 J ≤ S.Dlow * (N / S.Dlow * S.X ^ (-κ)) :=
          mul_le_mul_of_nonneg_left s1 (by linarith)
      _ = Q := by simp only [Q]; field_simp
  · exact lowFactor_coprime_col hS (by decide) ha hs
  · exact lowFactor_coprime_col hS (by decide) ha ht
  · rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (atomWeight_nonneg P c)]

end Erdos287.Physical.TypeII
