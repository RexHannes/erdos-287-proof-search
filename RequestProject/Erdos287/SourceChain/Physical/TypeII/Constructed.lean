import RequestProject.Erdos287.SourceChain.Physical.Factorization.Decomposition
import RequestProject.Erdos287.SourceChain.Physical.TypeII.OrderingB

/-!
# Erdős #287 — the constructed Type-II coefficient (no free split parameter)

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

This replaces the externally supplied `SplitRule σ` of `TypeII/Instance.lean`.  The Type-II
coefficient of an atom `λ = (J, P, χ)` (Pascadi colouring `c = atomColour δ N J P`) is

`c_{ξ,λ}(l, r) = Γ_ξ (-1)^J w_{J,P} · a₁(l) · (a₂ * a₃)(r) · 1[P ∈ 𝐃_J^+] 1[(f_ξ, l r) = 1]`

with `a₁ = κ_J * γ_{0,χ}`, `a₂ = γ_{1,χ}`, `a₃ = γ_{2,χ}`.  Proved:

* `physCoefAtom_reassemble` — summing the split coefficient over all atoms and all `(l, r)`
  returns **exactly** `Γ_ξ ∑_d 1[(f_ξ,d)=1] ℓ_X(d) g(d)` (each scalar term once; no packet
  multiplicity or designated-coordinate sum is introduced);
* `physCoefAtom_coprime` — every nonzero coefficient has `(l, r) = 1` and `(f_ξ, l r) = 1`;
* `physCoefAtom_abs_le` — `|c_{ξ,λ}(l,r)| ≤ |Γ_ξ| w_{J,P}` (one-bounded factors; the split of
  `r` into colours 1 and 2 is unique, `abs_conv12_le`);
* `physCoefAtom_ranges` — Pascadi ranges of the factors: `l ≤ N X^{-δ}`, `r = a₂ a₃` with
  `a₂ ≤ E₁`, `a₃ ≤ E₂`, `N² E₁ E₂² ≤ D_low² X^{1-δ}`, `N² E₁⁵ E₂² ≤ D_low² X^{2-δ}`;
* `typeII_source_decomp` — the independently defined scalar Type-II source
  `Γ ∑_d 1[(f,d)=1] ℓ_X(d) (I_d - U_d)(v)` equals
  `∑_λ ∑_{l,r} c_{ξ,λ}(l,r) (I_l h_r + h_l U_r)(v)` (exact Type-II split, atom by atom);
* `physOB` / `physOB_source_eq_T` — each atom's `I_l h_r` part is the actual Ordering-B cell
  built from **the same atom coefficient** (selected before the Cauchy step), and its
  independently defined source equals `T_ξ`.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII

open Erdos287.Physical.Sieve Erdos287.Physical.Sieve.ScalarParams Erdos287.Physical.Factor

/-- Box sums of a Dirichlet convolution. -/
lemma sum_box_conv (A B : ArithmeticFunction ℝ) (h : ℕ → ℝ) (K : ℕ) :
    ∑ l ∈ Ico 1 K, ∑ r ∈ Ico 1 K, (if l * r < K then A l * B r * h (l * r) else 0) =
      ∑ d ∈ Ico 1 K, (A * B) d * h d := by
  classical
  have hanti : ∀ d ∈ Ico 1 K, d.divisorsAntidiagonal =
      (Ico 1 K ×ˢ Ico 1 K).filter (fun x => x.1 * x.2 = d) := by
    intro d hd
    rw [mem_Ico] at hd
    ext x
    simp only [Nat.mem_divisorsAntidiagonal, mem_filter, mem_product, mem_Ico]
    constructor
    · rintro ⟨hx, -⟩
      have h1 : x.1 ≠ 0 := by rintro h0; rw [h0, zero_mul] at hx; omega
      have h2 : x.2 ≠ 0 := by rintro h0; rw [h0, mul_zero] at hx; omega
      have := Nat.le_mul_of_pos_right x.1 (Nat.pos_of_ne_zero h2)
      have := Nat.le_mul_of_pos_left x.2 (Nat.pos_of_ne_zero h1)
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, hx⟩ <;> omega
    · rintro ⟨-, hx⟩; exact ⟨hx, by omega⟩
  have hR : ∑ d ∈ Ico 1 K, (A * B) d * h d = ∑ d ∈ Ico 1 K, ∑ x ∈ Ico 1 K ×ˢ Ico 1 K,
      if x.1 * x.2 = d then A x.1 * B x.2 * h (x.1 * x.2) else 0 := by
    refine sum_congr rfl (fun d hd => ?_)
    rw [ArithmeticFunction.mul_apply, hanti d hd, sum_filter, sum_mul]
    refine sum_congr rfl (fun x _ => ?_)
    split_ifs with hx
    · rw [hx]
    · simp
  rw [hR]
  conv_rhs => rw [sum_comm, sum_product]
  refine sum_congr rfl (fun l hl => sum_congr rfl (fun r hr => ?_))
  rw [sum_ite_eq]
  rw [mem_Ico] at hl hr
  have hpos : 1 ≤ l * r := Nat.mul_pos (by omega) (by omega)
  simp only [mem_Ico]
  split_ifs <;> first | rfl | (exfalso; omega)

variable (S : ScalarParams)

open Classical in
/-- **The constructed Type-II coefficient of an atom** `λ = (J, P, χ)` (Pascadi colouring). -/
noncomputable def physCoefAtom (δ N Γ : ℝ) (f J : ℕ) (P : Fin J → Fin S.H)
    (χ : Fin S.Kc → Fin 3) (l r : ℕ) : ℝ :=
  if S.BoxAdm J P ∧ Nat.Coprime f (l * r) then
    Γ * ((-1 : ℝ) ^ J * S.atomWeight J P (S.atomColour δ N J P)) *
      (S.lowFactor J P (S.atomColour δ N J P) χ l *
        (S.colFactor J P (S.atomColour δ N J P) χ 1 *
          S.colFactor J P (S.atomColour δ N J P) χ 2) r)
  else 0

variable {S}

open Classical in
/-- **Lossless reassembly of `ℓ_X` from the constructed Type-II coefficients.** -/
theorem physCoefAtom_reassemble (hS : S.Good) (δ N Γ : ℝ) (f K : ℕ) (g : ℕ → ℝ) :
    ∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H, ∑ χ : Fin S.Kc → Fin 3,
      ∑ l ∈ Ico 1 K, ∑ r ∈ Ico 1 K,
        (if l * r < K then physCoefAtom S δ N Γ f J P χ l r * g (l * r) else 0) =
      Γ * ∑ d ∈ Ico 1 K, if Nat.Coprime f d then S.ellX d * g d else 0 := by
  -- the right-hand side, atom by atom
  have hR : Γ * ∑ d ∈ Ico 1 K, (if Nat.Coprime f d then S.ellX d * g d else 0) =
      ∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H, ∑ χ : Fin S.Kc → Fin 3,
        ∑ d ∈ Ico 1 K, (S.lowFactor J P (S.atomColour δ N J P) χ *
          (S.colFactor J P (S.atomColour δ N J P) χ 1 * S.colFactor J P (S.atomColour δ N J P) χ 2)) d *
          (if S.BoxAdm J P ∧ Nat.Coprime f d then
            Γ * ((-1 : ℝ) ^ J * S.atomWeight J P (S.atomColour δ N J P)) * g d else 0) := by
    rw [mul_sum]
    have hd : ∀ d ∈ Ico 1 K, Γ * (if Nat.Coprime f d then S.ellX d * g d else 0) =
        ∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H, ∑ χ : Fin S.Kc → Fin 3,
          (S.lowFactor J P (S.atomColour δ N J P) χ *
            (S.colFactor J P (S.atomColour δ N J P) χ 1 * S.colFactor J P (S.atomColour δ N J P) χ 2)) d *
            (if S.BoxAdm J P ∧ Nat.Coprime f d then
              Γ * ((-1 : ℝ) ^ J * S.atomWeight J P (S.atomColour δ N J P)) * g d else 0) := by
      intro d _
      rw [ellX_tensor hS (S.atomColour δ N)]
      by_cases hc : Nat.Coprime f d
      · rw [if_pos hc, sum_mul, mul_sum]
        refine sum_congr rfl (fun J _ => ?_)
        rw [sum_mul, mul_sum]
        refine sum_congr rfl (fun P _ => ?_)
        by_cases hP : S.BoxAdm J P
        · rw [if_pos hP, if_pos ⟨hP, hc⟩, mul_sum, sum_mul, mul_sum]
          refine sum_congr rfl (fun χ _ => ?_)
          rw [← mul_assoc (S.lowFactor J P (S.atomColour δ N J P) χ)]
          ring
        · rw [if_neg hP]; simp [hP]
      · rw [if_neg hc, mul_zero]; simp [hc]
    rw [sum_congr rfl hd, sum_comm]
    refine sum_congr rfl (fun J _ => ?_)
    rw [sum_comm]
    refine sum_congr rfl (fun P _ => ?_)
    rw [sum_comm]
  rw [hR]
  refine sum_congr rfl (fun J _ => sum_congr rfl (fun P _ => sum_congr rfl (fun χ _ => ?_)))
  rw [← sum_box_conv]
  refine sum_congr rfl (fun l _ => sum_congr rfl (fun r _ => ?_))
  by_cases h1 : l * r < K
  · simp only [if_pos h1, physCoefAtom]
    by_cases h2 : S.BoxAdm J P ∧ Nat.Coprime f (l * r)
    · rw [if_pos h2, if_pos h2]; ring
    · rw [if_neg h2, if_neg h2]; ring
  · simp only [if_neg h1]

/-- The split of `r` into colours 1 and 2 is unique, so `|γ₁ * γ₂| ≤ 1`. -/
theorem abs_conv12_le (hS : S.Good) {J : ℕ} (P : Fin J → Fin S.H) (c : ℕ → Fin 3)
    (χ : Fin S.Kc → Fin 3) (r : ℕ) :
    |(S.colFactor J P c χ 1 * S.colFactor J P c χ 2) r| ≤ 1 := by
  rw [ArithmeticFunction.mul_apply]
  refine abs_sum_le_one_of_unique _ _ ?_ ?_
  · intro x hx y hy hfx hfy
    obtain ⟨hxm, hr0⟩ := Nat.mem_divisorsAntidiagonal.1 hx
    obtain ⟨hym, -⟩ := Nat.mem_divisorsAntidiagonal.1 hy
    obtain ⟨hx1, sx1, -⟩ := colFactor_support hS (left_ne_zero_of_mul hfx)
    obtain ⟨hx2, sx2, -⟩ := colFactor_support hS (right_ne_zero_of_mul hfx)
    obtain ⟨hy1, sy1, -⟩ := colFactor_support hS (left_ne_zero_of_mul hfy)
    obtain ⟨hy2, sy2, -⟩ := colFactor_support hS (right_ne_zero_of_mul hfy)
    -- the colour-1 part is determined by its factorization
    have key : ∀ (a b : ℕ), a ≠ 0 → b ≠ 0 → a * b = r →
        (∀ p, p.Prime → p ∣ a → S.chiAt χ p = 1) → (∀ p, p.Prime → p ∣ b → S.chiAt χ p = 2) →
        ∀ p, a.factorization p = if S.chiAt χ p = 1 then r.factorization p else 0 := by
      intro a b ha hb hab h1 h2 p
      rw [← hab, Nat.factorization_mul ha hb, Finsupp.add_apply]
      by_cases hp : p.Prime
      · split_ifs with hc
        · have : ¬ p ∣ b := fun hd => by have := h2 p hp hd; rw [hc] at this; exact absurd this (by decide)
          rw [Nat.factorization_eq_zero_of_not_dvd this, add_zero]
        · have : ¬ p ∣ a := fun hd => hc (h1 p hp hd)
          rw [Nat.factorization_eq_zero_of_not_dvd this]
      · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
    have e1 : x.1 = y.1 := by
      apply Nat.eq_of_factorization_eq hx1 hy1
      intro p
      rw [key x.1 x.2 hx1 hx2 hxm (fun p hp hd => (sx1 p hp hd).2) (fun p hp hd => (sx2 p hp hd).2),
        key y.1 y.2 hy1 hy2 hym (fun p hp hd => (sy1 p hp hd).2) (fun p hp hd => (sy2 p hp hd).2)]
    have e2 : x.2 = y.2 := by
      have : x.1 * x.2 = x.1 * y.2 := by rw [hxm, e1, hym]
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hx1) this
    exact Prod.ext e1 e2
  · intro x _
    rw [abs_mul]
    exact mul_le_one₀ (abs_colFactor_le hS P c χ 1 _) (abs_nonneg _) (abs_colFactor_le hS P c χ 2 _)

/-- **Coefficient bound**: `|c_{ξ,λ}(l,r)| ≤ |Γ_ξ| w_{J,P}`. -/
theorem physCoefAtom_abs_le (hS : S.Good) (δ N Γ : ℝ) (f J : ℕ) (P : Fin J → Fin S.H)
    (χ : Fin S.Kc → Fin 3) (l r : ℕ) :
    |physCoefAtom S δ N Γ f J P χ l r| ≤ |Γ| * S.atomWeight J P (S.atomColour δ N J P) := by
  unfold physCoefAtom
  split_ifs
  · rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (atomWeight_nonneg P _)]
    have h1 := abs_lowFactor_le hS P (S.atomColour δ N J P) χ l
    have h2 := abs_conv12_le hS P (S.atomColour δ N J P) χ r
    have hw := atomWeight_nonneg P (S.atomColour δ N J P)
    have : |S.lowFactor J P (S.atomColour δ N J P) χ l| *
        |(S.colFactor J P (S.atomColour δ N J P) χ 1 *
          S.colFactor J P (S.atomColour δ N J P) χ 2) r| ≤ 1 :=
      mul_le_one₀ h1 (abs_nonneg _) h2
    calc |Γ| * S.atomWeight J P (S.atomColour δ N J P) *
          (|S.lowFactor J P (S.atomColour δ N J P) χ l| *
            |(S.colFactor J P (S.atomColour δ N J P) χ 1 *
              S.colFactor J P (S.atomColour δ N J P) χ 2) r|)
        ≤ |Γ| * S.atomWeight J P (S.atomColour δ N J P) * 1 :=
          mul_le_mul_of_nonneg_left this (mul_nonneg (abs_nonneg _) hw)
      _ = _ := mul_one _
  · simp only [abs_zero]; exact mul_nonneg (abs_nonneg _) (atomWeight_nonneg P _)

/-- Every nonzero constructed coefficient has `(l, r) = 1` and `(f, l r) = 1`. -/
theorem physCoefAtom_coprime (hS : S.Good) {δ N Γ : ℝ} {f J : ℕ} {P : Fin J → Fin S.H}
    {χ : Fin S.Kc → Fin 3} {l r : ℕ} (h : physCoefAtom S δ N Γ f J P χ l r ≠ 0) :
    Nat.Coprime l r ∧ Nat.Coprime f (l * r) ∧ S.BoxAdm J P := by
  unfold physCoefAtom at h
  split_ifs at h with hc
  · refine ⟨lowFactor_coprime_high hS (P := P) (c := S.atomColour δ N J P) (χ := χ) ?_ ?_,
      hc.2, hc.1⟩
    · intro h0; apply h; rw [h0]; ring
    · intro h0; apply h; rw [h0]; ring
  · exact absurd rfl h

/-- **Pascadi ranges of the constructed coefficient's factors.** -/
theorem physCoefAtom_ranges (hS : S.Good) {δ N Γ : ℝ} (hA : AtomParams S δ N) {f J : ℕ}
    {P : Fin J → Fin S.H} {χ : Fin S.Kc → Fin 3} {l r : ℕ}
    (h : physCoefAtom S δ N Γ f J P χ l r ≠ 0) :
    let c := S.atomColour δ N J P
    let E₁ := cprod (S.boxVec J P) c 1 J
    let E₂ := cprod (S.boxVec J P) c 2 J
    (l : ℝ) ≤ N * S.X ^ (-δ) ∧
      (∃ a₂ a₃ : ℕ, a₂ * a₃ = r ∧ (a₂ : ℝ) ≤ E₁ ∧ (a₃ : ℝ) ≤ E₂) ∧
      N ^ 2 * E₁ * E₂ ^ 2 ≤ S.Dlow ^ 2 * S.X ^ (1 - δ) ∧
      N ^ 2 * E₁ ^ 5 * E₂ ^ 2 ≤ S.Dlow ^ 2 * S.X ^ (2 - δ) := by
  intro c E₁ E₂
  have hP := (physCoefAtom_coprime hS h).2.2
  unfold physCoefAtom at h
  rw [if_pos ⟨hP, (physCoefAtom_coprime hS (by unfold physCoefAtom; exact h)).2.1⟩] at h
  have hl : S.lowFactor J P c χ l ≠ 0 := fun h0 => h (by simp [c, h0])
  have hr : (S.colFactor J P c χ 1 * S.colFactor J P c χ 2) r ≠ 0 :=
    fun h0 => h (by simp [c, h0])
  obtain ⟨s1, s2, s3⟩ := atomColour_spec hA hP
  have hDl := Dlow_ge_one hS
  have hN : 0 ≤ N := by
    have := (Real.rpow_pos_of_pos (by linarith [hS.X_gt] : (0 : ℝ) < S.X) (2 * δ)).trans_le hA.N_lo
    exact ((div_pos_iff_of_pos_right (by linarith)).1 this).le
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (lowFactor_support hS hl).trans ?_
    calc S.Dlow * cprod (S.boxVec J P) c 0 J ≤ S.Dlow * (N / S.Dlow * S.X ^ (-δ)) :=
          mul_le_mul_of_nonneg_left s1 (by linarith)
      _ = N * S.X ^ (-δ) := by field_simp
  · rw [ArithmeticFunction.mul_apply] at hr
    obtain ⟨y, hy, hne⟩ := exists_ne_zero_of_sum_ne_zero hr
    obtain ⟨-, -, h1⟩ := colFactor_support hS (left_ne_zero_of_mul hne)
    obtain ⟨-, -, h2⟩ := colFactor_support hS (right_ne_zero_of_mul hne)
    exact ⟨y.1, y.2, (Nat.mem_divisorsAntidiagonal.1 hy).1, h1, h2⟩
  · calc N ^ 2 * E₁ * E₂ ^ 2 = S.Dlow ^ 2 * ((N / S.Dlow) ^ 2 * E₁ * E₂ ^ 2) := by
          field_simp
      _ ≤ S.Dlow ^ 2 * S.X ^ (1 - δ) := mul_le_mul_of_nonneg_left s2 (by positivity)
  · calc N ^ 2 * E₁ ^ 5 * E₂ ^ 2 = S.Dlow ^ 2 * ((N / S.Dlow) ^ 2 * E₁ ^ 5 * E₂ ^ 2) := by
          field_simp
      _ ≤ S.Dlow ^ 2 * S.X ^ (2 - δ) := mul_le_mul_of_nonneg_left s3 (by positivity)

open Classical in
/-- **Exact Type-II decomposition of the scalar source, atom by atom**: for every `v`,
`Γ ∑_d 1[(f,d)=1] ℓ_X(d) (I_d - U_d)(v) = ∑_λ ∑_{l,r} c_{ξ,λ}(l,r) (I_l h_r + h_l U_r)(v)`. -/
theorem typeII_source_decomp (hS : S.Good) (δ N Γ : ℝ) (f K A : ℕ) (B : ℤ) (v : ℕ) :
    Γ * ∑ d ∈ Ico 1 K, (if Nat.Coprime f d then S.ellX d * (Iz A B d v - Uz d v) else 0) =
      ∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H, ∑ χ : Fin S.Kc → Fin 3,
        ∑ l ∈ Ico 1 K, ∑ r ∈ Ico 1 K,
          (if l * r < K then physCoefAtom S δ N Γ f J P χ l r *
            (Iz A B l v * hz A B r v + hz A B l v * Uz r v) else 0) := by
  rw [← physCoefAtom_reassemble hS δ N Γ f K (fun d => Iz A B d v - Uz d v)]
  refine sum_congr rfl (fun J _ => sum_congr rfl (fun P _ => sum_congr rfl (fun χ _ =>
    sum_congr rfl (fun l _ => sum_congr rfl (fun r _ => ?_)))))
  split_ifs
  · by_cases h0 : physCoefAtom S δ N Γ f J P χ l r = 0
    · rw [h0, zero_mul, zero_mul]
    · rw [typeII_split_Z (physCoefAtom_coprime hS h0).1]
  · rfl

/-- **The actual Ordering-B cell of an atom**: the coefficient is the constructed atom
coefficient (the same atom is selected before the Cauchy step). -/
noncomputable def physOB (δ N Γ : ℝ) (f c A : ℕ) (B : ℤ) (L R Nn M : ℕ) (J : ℕ)
    (P : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3) (alpha beta : ℕ → ℝ) : OBData where
  f := f
  c := c
  A := A
  B := B
  L := L
  R := R
  N := Nn
  M := M
  coef := physCoefAtom S δ N Γ f J P χ
  alpha := alpha
  beta := beta

/-- For each atom, the independently defined Type-II source equals the Ordering-B cell sum
`T_ξ` of the cell built from the constructed coefficient. -/
theorem physOB_source_eq_T (δ N Γ : ℝ) (f c A : ℕ) (B : ℤ) (L R Nn M J : ℕ)
    (P : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3) (α β : ArithmeticFunction ℝ)
    (hα : ∀ n, α n ≠ 0 → Nn ≤ n ∧ n < 2 * Nn) (hβ : ∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M)
    {K : ℕ} (hK : 4 * Nn * M ≤ K) :
    ∑ l ∈ Ico L (2 * L), ∑ r ∈ Ico R (2 * R), physCoefAtom S δ N Γ f J P χ l r *
      ∑ v ∈ range K, (α * β) v *
        ((physOB (S := S) δ N Γ f c A B L R Nn M J P χ α β).res v * Iz A B l v * hz A B r v) =
      (physOB (S := S) δ N Γ f c A B L R Nn M J P χ α β).T :=
  OBData.source_eq_T (D := physOB (S := S) δ N Γ f c A B L R Nn M J P χ α β) α β
    (fun _ => rfl) (fun _ => rfl) hα hβ hK

end Erdos287.Physical.TypeII
