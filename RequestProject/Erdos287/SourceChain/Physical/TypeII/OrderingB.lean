import RequestProject.Erdos287.SourceChain.Physical.Profile
import RequestProject.Erdos287.SourceChain.Physical.TypeII.Cells

/-!
# Erdős #287 — Type-II source: the literal Ordering-B square `V_ξ`

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Literal objects of `sources/physical_spec.md` §§23–24, with the actual masks:

* `Iz A B s v = 1_{A v ≡ B (mod s)}` (`B ∈ ℤ`: the reduced pair `B_{jℓ}` may be negative),
  `Uz s v = 1_{(v,s)=1}/φ(s)`, `hz = Iz - Uz`;
* `typeII_split_Z` — `I_{lr} - U_{lr} = I_l (I_r - U_r) + (I_l - U_l) U_r` for coprime `l, r`;
* `OBData` — one separated Type-II cell: modulus `f`, residue `c`, `(A, B)`, dyadic scales
  `L, R, N, M`, coefficients `coef l r = c_{ξ,l,r}`, `α`, `β`;
* `OBData.inner l m = ∑_{r∼R} c_{ξ,l,r} ∑_{n∼N} α_n 1_{mn≡c (f)} I_l(mn) h_r(mn)`;
* `OBData.V = ∑_{l∼L} ∑_m Ψ(m/M) |inner l m|²` with the explicit plateau profile `Ψ`
  (`physPsi`); `V_eq_range` — the `m`-range is lossless (`Ψ(m/M) = 0` for `m ≥ 5M/2`);
* `OBData.T = ∑_{l∼L} ∑_{m∼M} β_m inner l m` and `T_sq_le` — **first Cauchy**
  `|T|² ≤ (∑_{l∼L} ∑_{m∼M} |β_m|²) V`;
* `V_expand` — **Ordering-B expansion** of the square (pairs `(r₁,n₁)`, `(r₂,n₂)`, the `m`-sum
  innermost, all masks retained);
* `base_congruence` — every nonzero term of the expansion has `(n₁n₂, fl) = 1` and
  `n₁ ≡ n₂ (mod fl)`;
* `source_eq_T` — the independently defined Type-II source
  `∑_{l,r} c_{ξ,l,r} ∑_v (α * β)(v) 1_{v≡c (f)} I_l(v) h_r(v)` equals `T`.
-/

open scoped BigOperators
open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII

open Classical in
/-- `I_s(v) = 1_{A v ≡ B (mod s)}`. -/
noncomputable def Iz (A : ℕ) (B : ℤ) (s v : ℕ) : ℝ :=
  if (A : ℤ) * v ≡ B [ZMOD s] then 1 else 0

open Classical in
/-- `U_s(v) = 1_{(v,s)=1} / φ(s)`. -/
noncomputable def Uz (s v : ℕ) : ℝ := if Nat.Coprime v s then 1 / (Nat.totient s : ℝ) else 0

/-- `h_s = I_s - U_s`. -/
noncomputable def hz (A : ℕ) (B : ℤ) (s v : ℕ) : ℝ := Iz A B s v - Uz s v

theorem Iz_mul {l r : ℕ} (hlr : Nat.Coprime l r) (A : ℕ) (B : ℤ) (v : ℕ) :
    Iz A B (l * r) v = Iz A B l v * Iz A B r v := by
  unfold Iz
  have key := Int.modEq_and_modEq_iff_modEq_mul (a := (A : ℤ) * v) (b := B) (m := l) (n := r)
    (by simpa using hlr)
  push_cast
  by_cases h1 : (A : ℤ) * v ≡ B [ZMOD l] <;> by_cases h2 : (A : ℤ) * v ≡ B [ZMOD r]
  · rw [if_pos h1, if_pos h2, if_pos (key.1 ⟨h1, h2⟩)]; ring
  · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 (key.2 h).2)]; ring
  · rw [if_neg h1, if_neg (fun h => h1 (key.2 h).1)]; ring
  · rw [if_neg h1, if_neg (fun h => h1 (key.2 h).1)]; ring

theorem Uz_mul {l r : ℕ} (hlr : Nat.Coprime l r) (v : ℕ) : Uz (l * r) v = Uz l v * Uz r v := by
  unfold Uz
  rw [Nat.totient_mul hlr, Nat.cast_mul]
  by_cases h1 : Nat.Coprime v l <;> by_cases h2 : Nat.Coprime v r
  · rw [if_pos (Nat.Coprime.mul_right h1 h2), if_pos h1, if_pos h2]; field_simp
  · rw [if_neg (fun h => h2 (Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) h)), if_neg h2]
    ring
  · rw [if_neg (fun h => h1 (Nat.Coprime.coprime_dvd_right (Dvd.intro _ rfl) h)), if_neg h1]
    ring
  · rw [if_neg (fun h => h1 (Nat.Coprime.coprime_dvd_right (Dvd.intro _ rfl) h)), if_neg h1]
    ring

/-- **Exact Type-II split** (§23) with the integer residue `B`. -/
theorem typeII_split_Z {l r : ℕ} (hlr : Nat.Coprime l r) (A : ℕ) (B : ℤ) (v : ℕ) :
    Iz A B (l * r) v - Uz (l * r) v = Iz A B l v * hz A B r v + hz A B l v * Uz r v := by
  unfold hz; rw [Iz_mul hlr, Uz_mul hlr]; ring

/-- One separated Type-II cell (§24): `x = MN`, `l ∼ L`, `r ∼ R`, `n ∼ N`, `m ∼ M`. -/
structure OBData where
  f : ℕ
  c : ℕ
  A : ℕ
  B : ℤ
  L : ℕ
  R : ℕ
  N : ℕ
  M : ℕ
  coef : ℕ → ℕ → ℝ
  alpha : ℕ → ℝ
  beta : ℕ → ℝ

namespace OBData

variable (D : OBData)

open Classical in
/-- The residue mask `1_{v ≡ c (mod f)}`. -/
noncomputable def res (v : ℕ) : ℝ := if v ≡ D.c [MOD D.f] then 1 else 0

/-- `inner l m = ∑_{r∼R} c_{ξ,l,r} ∑_{n∼N} α_n 1_{mn≡c (f)} I_l(mn) h_r(mn)`. -/
noncomputable def inner (l m : ℕ) : ℝ :=
  ∑ r ∈ Ico D.R (2 * D.R), D.coef l r * ∑ n ∈ Ico D.N (2 * D.N),
    D.alpha n * D.res (m * n) * Iz D.A D.B l (m * n) * hz D.A D.B r (m * n)

/-- **The actual Ordering-B square**
`V_ξ = ∑_{l∼L} ∑_m Ψ(m/M) |∑_{r∼R} c_{ξ,l,r} ∑_{n∼N} α_n 1_{mn≡c (f)} I_l(mn) h_r(mn)|²`. -/
noncomputable def V : ℝ :=
  ∑ l ∈ Ico D.L (2 * D.L), ∑ m ∈ range (3 * D.M + 1),
    physPsi ((m : ℝ) / D.M) * D.inner l m ^ 2

/-- The Type-II cell sum `T_ξ = ∑_{l∼L} ∑_{m∼M} β_m inner l m`. -/
noncomputable def T : ℝ :=
  ∑ l ∈ Ico D.L (2 * D.L), ∑ m ∈ Ico D.M (2 * D.M), D.beta m * D.inner l m

variable {D}

/-- The `m`-range of `V` is lossless: `Ψ(m/M) = 0` for `m > 3M`. -/
theorem V_eq_range (hM : 0 < D.M) {K : ℕ} (hK : 3 * D.M ≤ K) :
    D.V = ∑ l ∈ Ico D.L (2 * D.L), ∑ m ∈ range (K + 1),
      physPsi ((m : ℝ) / D.M) * D.inner l m ^ 2 := by
  unfold V
  refine Finset.sum_congr rfl (fun l _ => ?_)
  apply Finset.sum_subset
  · intro m hm; simp only [mem_range] at hm ⊢; omega
  · intro m hm hm'
    simp only [mem_range, not_lt] at hm hm'
    have hMr : (0 : ℝ) < D.M := by exact_mod_cast hM
    have : (5 : ℝ) / 2 ≤ (m : ℝ) / D.M := by
      rw [le_div_iff₀ hMr]
      have : (3 * D.M + 1 : ℝ) ≤ m := by exact_mod_cast hm'
      linarith
    rw [physPsi_eq_zero (Or.inr this), zero_mul]

/-- **First Cauchy**: `|T_ξ|² ≤ (∑_{l∼L} ∑_{m∼M} |β_m|²) V_ξ`. -/
theorem T_sq_le (hM : 0 < D.M) :
    D.T ^ 2 ≤ (∑ _ ∈ Ico D.L (2 * D.L), ∑ m ∈ Ico D.M (2 * D.M), D.beta m ^ 2) * D.V := by
  unfold T
  rw [← Finset.sum_product', ← Finset.sum_product']
  refine (Finset.sum_mul_sq_le_sq_mul_sq _ (fun x : ℕ × ℕ => D.beta x.2)
    (fun x : ℕ × ℕ => D.inner x.1 x.2)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [Finset.sum_product]
  unfold V
  refine Finset.sum_le_sum (fun l _ => ?_)
  have hMr : (0 : ℝ) < D.M := by exact_mod_cast hM
  calc ∑ m ∈ Ico D.M (2 * D.M), D.inner l m ^ 2
      ≤ ∑ m ∈ Ico D.M (2 * D.M), physPsi ((m : ℝ) / D.M) * D.inner l m ^ 2 := by
        refine Finset.sum_le_sum (fun m hm => ?_)
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hm
        have hp : 1 ≤ physPsi ((m : ℝ) / D.M) := by
          apply physPsi_plateau
          · rw [le_div_iff₀ hMr, one_mul]; exact_mod_cast (by omega : D.M ≤ m)
          · rw [div_le_iff₀ hMr]
            have : (m : ℝ) < 2 * D.M := by exact_mod_cast h2
            linarith
        nlinarith [sq_nonneg (D.inner l m)]
    _ ≤ ∑ m ∈ range (3 * D.M + 1), physPsi ((m : ℝ) / D.M) * D.inner l m ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm; simp only [mem_Ico, mem_range] at hm ⊢; omega
        · intro m _ _; exact mul_nonneg (physPsi_nonneg _) (sq_nonneg _)

/-- **Ordering-B expansion**: opening the square, with the `m`-sum innermost and all masks
retained. -/
theorem V_expand :
    D.V = ∑ l ∈ Ico D.L (2 * D.L), ∑ r₁ ∈ Ico D.R (2 * D.R), ∑ r₂ ∈ Ico D.R (2 * D.R),
      ∑ n₁ ∈ Ico D.N (2 * D.N), ∑ n₂ ∈ Ico D.N (2 * D.N),
        D.coef l r₁ * D.coef l r₂ * D.alpha n₁ * D.alpha n₂ *
          ∑ m ∈ range (3 * D.M + 1), physPsi ((m : ℝ) / D.M) *
            (D.res (m * n₁) * D.res (m * n₂) * Iz D.A D.B l (m * n₁) * Iz D.A D.B l (m * n₂) *
              hz D.A D.B r₁ (m * n₁) * hz D.A D.B r₂ (m * n₂)) := by
  unfold V
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have key : ∀ m : ℕ, physPsi ((m : ℝ) / D.M) * D.inner l m ^ 2 =
      ∑ r₁ ∈ Ico D.R (2 * D.R), ∑ r₂ ∈ Ico D.R (2 * D.R),
        ∑ n₁ ∈ Ico D.N (2 * D.N), ∑ n₂ ∈ Ico D.N (2 * D.N),
          D.coef l r₁ * D.coef l r₂ * D.alpha n₁ * D.alpha n₂ *
            (physPsi ((m : ℝ) / D.M) *
              (D.res (m * n₁) * D.res (m * n₂) * Iz D.A D.B l (m * n₁) *
                Iz D.A D.B l (m * n₂) * hz D.A D.B r₁ (m * n₁) * hz D.A D.B r₂ (m * n₂))) := by
    intro m
    unfold inner
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r₁ _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r₂ _ => ?_)
    rw [show ∀ (a b c S1 S2 : ℝ), a * (b * S1 * (c * S2)) = (a * b * c) * (S1 * S2) by
      intros; ring, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n₁ _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n₂ _ => ?_)
    ring
  rw [Finset.sum_congr rfl (fun m _ => key m)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r₁ _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r₂ _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n₁ _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n₂ _ => ?_)
  rw [Finset.mul_sum]

end OBData

/-- **Ordering B preserves the physical base**: if `m n_i ≡ c (mod f)` and
`A m n_i ≡ B (mod l)` for `i = 1, 2`, with `(c, f) = 1`, `(B, l) = 1` and `(f, l) = 1`, then
`(n₁ n₂, f l) = 1` and `n₁ ≡ n₂ (mod f l)`. -/
theorem base_congruence {f l A m n₁ n₂ : ℕ} {c B : ℤ} (hcf : IsCoprime c (f : ℤ))
    (hBl : IsCoprime B (l : ℤ)) (hfl : Nat.Coprime f l)
    (h1 : (m : ℤ) * n₁ ≡ c [ZMOD f]) (h2 : (m : ℤ) * n₂ ≡ c [ZMOD f])
    (h3 : (A : ℤ) * m * n₁ ≡ B [ZMOD l]) (h4 : (A : ℤ) * m * n₂ ≡ B [ZMOD l]) :
    IsCoprime ((n₁ : ℤ) * n₂) ((f : ℤ) * l) ∧ (n₁ : ℤ) ≡ n₂ [ZMOD (f * l : ℕ)] := by
  -- coprimality transfers along congruences
  have cop_of_modEq : ∀ {x y q : ℤ}, x ≡ y [ZMOD q] → IsCoprime y q → IsCoprime x q := by
    intro x y q hxy hy
    have : x = y + q * ((x - y) / q) := by
      rw [Int.mul_ediv_cancel' (Int.ModEq.dvd hxy.symm)]; ring
    rw [this]
    exact hy.add_mul_left_left _
  have hm1f : IsCoprime ((m : ℤ) * n₁) f := cop_of_modEq h1 hcf
  have hm2f : IsCoprime ((m : ℤ) * n₂) f := cop_of_modEq h2 hcf
  have hA1l : IsCoprime ((A : ℤ) * m * n₁) l := cop_of_modEq h3 hBl
  have hA2l : IsCoprime ((A : ℤ) * m * n₂) l := cop_of_modEq h4 hBl
  have hmf : IsCoprime (m : ℤ) f := hm1f.of_mul_left_left
  have hAml : IsCoprime ((A : ℤ) * m) l := hA1l.of_mul_left_left
  refine ⟨?_, ?_⟩
  · apply IsCoprime.mul_left
    · exact IsCoprime.mul_right hm1f.of_mul_left_right hA1l.of_mul_left_right
    · exact IsCoprime.mul_right hm2f.of_mul_left_right hA2l.of_mul_left_right
  · have hf : (n₁ : ℤ) ≡ n₂ [ZMOD f] := by
      have hd : (f : ℤ) ∣ (m : ℤ) * (n₂ - n₁) := by
        have := Int.ModEq.dvd (h1.trans h2.symm); rw [mul_sub]; exact this
      exact (Int.modEq_iff_dvd.2 (hmf.symm.dvd_of_dvd_mul_left hd))
    have hl : (n₁ : ℤ) ≡ n₂ [ZMOD l] := by
      have hd : (l : ℤ) ∣ ((A : ℤ) * m) * (n₂ - n₁) := by
        have := Int.ModEq.dvd (h3.trans h4.symm); rw [mul_sub]; exact this
      exact (Int.modEq_iff_dvd.2 (hAml.symm.dvd_of_dvd_mul_left hd))
    push_cast
    exact (Int.modEq_and_modEq_iff_modEq_mul (by simpa using hfl)).1 ⟨hf, hl⟩

/-- Convolution against a dyadically supported pair: for `α` supported on `[N, 2N)` and
`β` on `[M, 2M)`, `∑_{v < K} (α * β)(v) G(v) = ∑_{n∼N} ∑_{m∼M} α_n β_m G(mn)` once `K ≥ 4NM`. -/
theorem sum_conv_dyadic (α β : ArithmeticFunction ℝ) {N M K : ℕ}
    (hα : ∀ n, α n ≠ 0 → N ≤ n ∧ n < 2 * N) (hβ : ∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M)
    (hK : 4 * N * M ≤ K) (G : ℕ → ℝ) :
    ∑ v ∈ range K, (α * β) v * G v =
      ∑ n ∈ Ico N (2 * N), ∑ m ∈ Ico M (2 * M), α n * β m * G (m * n) := by
  simp_rw [ArithmeticFunction.mul_apply, Finset.sum_mul]
  rw [Finset.sum_sigma', ← Finset.sum_product']
  refine Finset.sum_bij_ne_zero (fun y _ _ => y.2) ?_ ?_ ?_ ?_
  · intro y hy hne
    have h1 : α y.2.1 ≠ 0 := fun h => hne (by rw [h]; ring)
    have h2 : β y.2.2 ≠ 0 := fun h => hne (by rw [h]; ring)
    rw [Finset.mem_product, Finset.mem_Ico, Finset.mem_Ico]
    exact ⟨hα _ h1, hβ _ h2⟩
  · intro y1 hy1 _ y2 hy2 _ h
    obtain ⟨-, hx1⟩ := Finset.mem_sigma.1 hy1
    obtain ⟨-, hx2⟩ := Finset.mem_sigma.1 hy2
    have e1 := (Nat.mem_divisorsAntidiagonal.1 hx1).1
    have e2 := (Nat.mem_divisorsAntidiagonal.1 hx2).1
    simp only at h
    have hd : y1.1 = y2.1 := by rw [← e1, ← e2, h]
    exact Sigma.ext hd (heq_of_eq h)
  · intro x hx hne
    obtain ⟨hn, hm⟩ := Finset.mem_product.1 hx
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ico.1 hn
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.1 hm
    have hN : 0 < N := by
      by_contra h0; push_neg at h0; interval_cases N; omega
    have hM : 0 < M := by
      by_contra h0; push_neg at h0; interval_cases M; omega
    refine ⟨⟨x.1 * x.2, x⟩, ?_, ?_, rfl⟩
    · rw [Finset.mem_sigma, Finset.mem_range, Nat.mem_divisorsAntidiagonal]
      refine ⟨?_, rfl, ?_⟩
      · have : x.1 * x.2 < (2 * N) * (2 * M) := Nat.mul_lt_mul'' hn2 hm2
        nlinarith
      · exact Nat.mul_ne_zero (by omega) (by omega)
    · simpa [mul_comm x.2 x.1] using hne
  · intro y hy _
    obtain ⟨-, hx⟩ := Finset.mem_sigma.1 hy
    have e := (Nat.mem_divisorsAntidiagonal.1 hx).1
    simp only
    rw [← e, mul_comm y.2.1 y.2.2]

namespace OBData

variable {D : OBData}

/-- **The independently defined Type-II source equals the Ordering-B cell sum**:
`∑_{l∼L} ∑_{r∼R} c_{ξ,l,r} ∑_{v<K} (α * β)(v) 1_{v≡c (f)} I_l(v) h_r(v) = T_ξ`. -/
theorem source_eq_T (α β : ArithmeticFunction ℝ) (hαD : ∀ n, D.alpha n = α n)
    (hβD : ∀ m, D.beta m = β m)
    (hα : ∀ n, α n ≠ 0 → D.N ≤ n ∧ n < 2 * D.N) (hβ : ∀ m, β m ≠ 0 → D.M ≤ m ∧ m < 2 * D.M)
    {K : ℕ} (hK : 4 * D.N * D.M ≤ K) :
    ∑ l ∈ Ico D.L (2 * D.L), ∑ r ∈ Ico D.R (2 * D.R), D.coef l r *
      ∑ v ∈ range K, (α * β) v * (D.res v * Iz D.A D.B l v * hz D.A D.B r v) = D.T := by
  unfold T inner
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp_rw [sum_conv_dyadic α β hα hβ hK]
  calc ∑ r ∈ Ico D.R (2 * D.R), D.coef l r * ∑ n ∈ Ico D.N (2 * D.N), ∑ m ∈ Ico D.M (2 * D.M),
        α n * β m * (D.res (m * n) * Iz D.A D.B l (m * n) * hz D.A D.B r (m * n))
      = ∑ r ∈ Ico D.R (2 * D.R), ∑ m ∈ Ico D.M (2 * D.M), ∑ n ∈ Ico D.N (2 * D.N),
          D.coef l r * (α n * β m * (D.res (m * n) * Iz D.A D.B l (m * n) *
            hz D.A D.B r (m * n))) := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ m ∈ Ico D.M (2 * D.M), ∑ r ∈ Ico D.R (2 * D.R), ∑ n ∈ Ico D.N (2 * D.N),
          D.coef l r * (α n * β m * (D.res (m * n) * Iz D.A D.B l (m * n) *
            hz D.A D.B r (m * n))) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [hαD, hβD]
        ring

end OBData

end Erdos287.Physical.TypeII
