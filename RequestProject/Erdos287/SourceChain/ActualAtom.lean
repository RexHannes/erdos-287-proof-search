import RequestProject.Erdos287.SourceChain.AffinePhase
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Erdős #287 — the canonical clean critical atom, the no-dilation phase and character separation

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**
Status: `AstraActualAtomW4Candidate`, `V101ResidueAtomW4Candidate`, `IndependentAuditPending`
(documentation only).

* `CleanAtom` — one canonical structure for a cleaned critical atom (shared by both the Astra and
  the V101 route; no route-specific surrogate), carrying the exact CRT system
  `n₁ρ ≡ c (f)`, `An₁ρ ≡ B (q r₁ s₁)`, `An₂ρ ≡ B (r₂ s₂)`, the two explicit inverse witnesses,
  coprimalities, near-diagonal exclusion and the range data.
* `CleanAtom.noDilation_phase` — the exact identity
  `hρ/(fquv) ≡ Bh/(An₁fquv) + Bh(n₁-n₂)·\overline{Afn₂qu}/(n₁v) + h(Ac-B)·\overline{qun₁v}/(Af)`
  (mod 1), `u = r₁s₁`, `v = r₂s₂`, with **no** assumption `(A,f) = 1`.
* `colour_deletion_counterfixture` — deleting the `Af`-local colour changes the phase.
* `unit_class_expansion`, `unit_class_expansion_factor` — the unit-class indicator modulo
  `D = Af` as an average of Dirichlet characters (finite-group orthogonality from Mathlib; no
  cyclicity assumed), split multiplicatively as `χ(q r₁ C_*) χ(s₁)`.
* `character_coefficient_bound`, `character_count_le` — every twist is one-bounded and the total
  coefficient mass is at most `φ(D) ≤ D`.
* `fixedPhase_den_le` — the fixed phase `ω_t = (Ac-B)\bar t/(Af)` has denominator `≤ Af`, i.e.
  `T_H(ω_t) ≤ Af`.
-/

namespace Erdos287.SourceChain

/-- **The canonical clean critical atom.** -/
structure CleanAtom where
  A : ℤ
  B : ℤ
  f : ℤ
  c : ℤ
  q : ℤ
  r1 : ℤ
  r2 : ℤ
  s1 : ℤ
  s2 : ℤ
  n1 : ℤ
  n2 : ℤ
  ρ : ℤ
  h : ℤ
  /-- inverse of `A f n₂ q u` modulo `n₁ v` -/
  invS : ℤ
  /-- inverse of `q u n₁ v` modulo `A f` -/
  invT : ℤ
  A_ne : A ≠ 0
  f_ne : f ≠ 0
  q_ne : q ≠ 0
  r1_ne : r1 ≠ 0
  r2_ne : r2 ≠ 0
  s1_ne : s1 ≠ 0
  s2_ne : s2 ≠ 0
  n1_ne : n1 ≠ 0
  crt_f : n1 * ρ ≡ c [ZMOD f]
  crt_1 : A * n1 * ρ ≡ B [ZMOD q * (r1 * s1)]
  crt_2 : A * n2 * ρ ≡ B [ZMOD r2 * s2]
  inv_S : (A * f * n2 * q * (r1 * s1)) * invS ≡ 1 [ZMOD n1 * (r2 * s2)]
  inv_T : (q * (r1 * s1) * n1 * (r2 * s2)) * invT ≡ 1 [ZMOD A * f]
  /-- own / cross coprimalities -/
  cop_r : IsCoprime (r1 * s1) (r2 * s2)
  /-- near-diagonal exclusion -/
  nearDiag_excl : n1 ≠ n2
  /-- ranges (dyadic parameters) -/
  N : ℝ
  Q : ℝ
  R : ℝ
  S : ℝ
  H : ℝ
  n1_range : (n1.natAbs : ℝ) ≤ 2 * N
  n2_range : (n2.natAbs : ℝ) ≤ 2 * N
  q_range : (q.natAbs : ℝ) ≤ 2 * Q
  h_range : (h.natAbs : ℝ) ≤ H

namespace CleanAtom

variable (a : CleanAtom)

/-- `u = r₁ s₁`. -/
def u : ℤ := a.r1 * a.s1
/-- `v = r₂ s₂`. -/
def v : ℤ := a.r2 * a.s2

/-- **No-dilation general-affine phase identity** for the canonical atom. -/
theorem noDilation_phase :
    IntDiff (((a.h * a.ρ : ℤ) : ℚ) / (a.f * a.q * a.u * a.v))
      (((a.B * a.h : ℤ) : ℚ) / (a.A * a.n1 * a.f * a.q * a.u * a.v) +
        ((a.B * a.h * (a.n1 - a.n2) * a.invS : ℤ) : ℚ) / (a.n1 * a.v) +
        ((a.h * (a.A * a.c - a.B) * a.invT : ℤ) : ℚ) / (a.A * a.f)) :=
  ph1_phase a.f_ne a.q_ne (mul_ne_zero a.r1_ne a.s1_ne) (mul_ne_zero a.r2_ne a.s2_ne) a.A_ne
    a.n1_ne a.crt_f a.crt_1 a.crt_2 a.inv_S a.inv_T

end CleanAtom

/-- **Regression (fixed-local counterfixture).**  With `f = 3`, `q = u = v = A = n₁ = n₂ = 1`,
`ρ = c = h = 1`, `B = 0` (all CRT/inverse hypotheses hold with `\bar{·} = 1`), the full phase is
`1/3`, while the phase with the `Af`-local colour deleted is `0`: they differ by a non-integer. -/
theorem colour_deletion_counterfixture :
    ¬ IntDiff (((1 * 1 : ℤ) : ℚ) / (3 * 1 * 1 * 1))
      (((0 * 1 : ℤ) : ℚ) / (1 * 1 * 3 * 1 * 1 * 1) + ((0 * 1 * (1 - 1) * 1 : ℤ) : ℚ) / (1 * 1)) := by
  rintro ⟨k, hk⟩
  norm_num at hk
  have h3 : (3 : ℚ) * k = 1 := by rw [← hk]; norm_num
  have : (3 : ℤ) * k = 1 := by exact_mod_cast h3
  omega

/-- The same data satisfy every hypothesis of the phase identity (so the counterfixture is a
genuine instance, not a vacuous one). -/
theorem colour_deletion_counterfixture_hyps :
    (1 : ℤ) * 1 ≡ 1 [ZMOD 3] ∧ (1 : ℤ) * 1 * 1 ≡ 0 [ZMOD 1 * 1] ∧ (1 : ℤ) * 1 * 1 ≡ 0 [ZMOD 1] ∧
      ((1 : ℤ) * 3 * 1 * 1 * 1) * 1 ≡ 1 [ZMOD 1 * 1] ∧ ((1 : ℤ) * 1 * 1 * 1) * 1 ≡ 1 [ZMOD 1 * 3] := by
  refine ⟨by decide, ?_, ?_, ?_, by decide⟩ <;> simp [Int.ModEq]

/-! ### Character separation modulo `D = Af` (after Ordering B) -/

open DirichletCharacter in
/-- **Unit-class expansion.**  For a unit `t` modulo `D`,
`1_{x = t} = φ(D)⁻¹ ∑_χ \bar χ(t) χ(x)` — finite-group orthogonality, no cyclicity assumed. -/
theorem unit_class_expansion {D : ℕ} [NeZero D] {t : ZMod D} (ht : IsUnit t) (x : ZMod D) :
    (if t = x then (1 : ℂ) else 0) =
      (D.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ D, χ t⁻¹ * χ x := by
  rw [sum_char_inv_mul_char_eq ℂ ht x]
  have hφ : (D.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne D))).ne'
  split_ifs <;> simp [hφ]

open DirichletCharacter in
/-- The expansion with the argument `q r₁ C_* s₁` split multiplicatively. -/
theorem unit_class_expansion_factor {D : ℕ} [NeZero D] {t : ZMod D} (ht : IsUnit t)
    (qr1C s1 : ZMod D) :
    (if t = qr1C * s1 then (1 : ℂ) else 0) =
      (D.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ D, χ t⁻¹ * χ qr1C * χ s1 := by
  rw [unit_class_expansion ht]
  congr 1
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  rw [map_mul, mul_assoc]

/-- Every character twist is one-bounded. -/
theorem character_coefficient_bound {D : ℕ} (χ : DirichletCharacter ℂ D) (t a b : ZMod D) :
    ‖χ t * χ a * χ b‖ ≤ 1 := by
  rw [norm_mul, norm_mul]
  have h1 := DirichletCharacter.norm_le_one χ t
  have h2 := DirichletCharacter.norm_le_one χ a
  have h3 := DirichletCharacter.norm_le_one χ b
  have : ‖χ t‖ * ‖χ a‖ ≤ 1 := mul_le_one₀ h1 (norm_nonneg _) h2
  exact mul_le_one₀ this (norm_nonneg _) h3

/-- The number of characters (total coefficient mass) is `φ(D) ≤ D`. -/
theorem character_count_le (D : ℕ) [NeZero D] :
    Nat.card (DirichletCharacter ℂ D) = D.totient ∧ D.totient ≤ D :=
  ⟨DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ D, Nat.totient_le D⟩

/-- Total absolute coefficient mass of the expansion: `φ(D)⁻¹ ∑_χ ‖…‖ ≤ 1`, and the unnormalised
mass `∑_χ ‖…‖ ≤ φ(D) ≤ D`. -/
theorem character_mass_le {D : ℕ} [NeZero D] (t a b : ZMod D) :
    ∑ χ : DirichletCharacter ℂ D, ‖χ t * χ a * χ b‖ ≤ D := by
  calc ∑ χ : DirichletCharacter ℂ D, ‖χ t * χ a * χ b‖
      ≤ ∑ _χ : DirichletCharacter ℂ D, (1 : ℝ) :=
        Finset.sum_le_sum (fun χ _ => character_coefficient_bound χ t a b)
    _ = (Nat.card (DirichletCharacter ℂ D) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]; simp
    _ ≤ D := by
        rw [(character_count_le D).1]; exact_mod_cast Nat.totient_le D

/-- **`T_H(ω_t) ≤ Af`**: the fixed phase `ω_t = (Ac - B)\bar t/(Af)` has denominator dividing
`Af`, hence at most `Af`. -/
theorem fixedPhase_den_le (A f : ℕ) (hA : 0 < A) (hf : 0 < f) (num : ℤ) :
    ((num : ℚ) / ((A * f : ℕ) : ℚ)).den ≤ A * f := by
  have hpos : 0 < A * f := Nat.mul_pos hA hf
  have h := Rat.den_dvd num ((A * f : ℕ) : ℤ)
  rw [Rat.divInt_eq_div] at h
  push_cast at h ⊢
  have h' : ((num : ℚ) / ((A : ℚ) * f)).den ∣ A * f := by exact_mod_cast h
  exact Nat.le_of_dvd hpos h'

end Erdos287.SourceChain
