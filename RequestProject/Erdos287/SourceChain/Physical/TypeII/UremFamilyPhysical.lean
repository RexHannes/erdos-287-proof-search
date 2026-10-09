import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilyCompose
import RequestProject.Erdos287.SourceChain.Physical.TypeII.RepairedProviders

/-!
# Erdős #287 — the literal `physUrem` as a sum of family Urem blocks

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

* `physUrem_eq_uremBlocks` — exact identity: for one packet,
  `physUrem = ∑_{J,P,χ} ∑_{1 ≤ r < K} φ(r)⁻¹ ∑_{i < n} Y(L = 2^i, r)`,
  where `Y = uremBlock` uses the **actual** atom coefficient `physCoefCut` as `z_l` and the masked
  sequence `α^{(r)}`.  `Γ` occurs exactly once (inside `physCoefCut`).  Hypotheses: `S.Good`,
  `0 < f`, `(c, f) = 1` and `AffinePrimesDivideBase A B f` (every prime of `A·|B|` divides `f`;
  proved for the actual packets by `physData_affinePrimesDivideBase`).
* `abs_physUrem_le_blocks` — the triangle inequality for that identity.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII.UremFamily

open Erdos287.Physical.TypeII Erdos287.Physical.Sieve Erdos287.Physical.Sieve.ScalarParams
  Erdos287.Physical.Factor

variable {S : ScalarParams}

lemma coprime_AB_of_base {A f l : ℕ} {B : ℤ} (hAPB : AffinePrimesDivideBase A B f)
    (hfl : Nat.Coprime f l) : Nat.Coprime (A * B.natAbs) l := by
  apply Nat.coprime_of_dvd
  intro p hp hpAB hpl
  have hpf := hAPB p hp hpAB
  have := Nat.dvd_gcd hpf hpl
  rw [Nat.Coprime.gcd_eq_one hfl] at this
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

/-- **The literal `physUrem` of one packet as a sum of family Urem blocks.** -/
theorem physUrem_eq_uremBlocks (hS : S.Good) (δ N Γ : ℝ) {f c A : ℕ} {B : ℤ} {K n : ℕ}
    (hKn : K ≤ 2 ^ n) {Nn M K' : ℕ} (α β : ArithmeticFunction ℝ)
    (hα : ∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn) (hβ : ∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M)
    (hK' : 4 * Nn * M ≤ K') (hf : 0 < f) (hcf : Nat.Coprime c f)
    (hAPB : AffinePrimesDivideBase A B f) :
    physUrem S δ N Γ f c A B K K' α β =
      ∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H, ∑ χ : Fin S.Kc → Fin 3,
        ∑ r ∈ Ico 1 K, (1 / (Nat.totient r : ℝ)) * ∑ i ∈ range n,
          uremBlock (Ico Nn (2 * Nn)) (maskR α r) f c A B (2 ^ i) M r
            (fun l => physCoefCut S δ N Γ f K J P χ l r) β := by
  unfold physUrem
  refine sum_congr rfl (fun J _ => sum_congr rfl (fun P _ => sum_congr rfl (fun χ _ => ?_)))
  rw [sum_comm]
  refine sum_congr rfl (fun r hr => ?_)
  have hr1 : 1 ≤ r := (mem_Ico.1 hr).1
  set X : ℕ → ℝ := fun l => physCoefCut S δ N Γ f K J P χ l r *
    ∑ m ∈ Ico M (2 * M), β m * copInd m (f * l * r) *
      relDisc (Ico Nn (2 * Nn)) (maskR α r) f (cRes f c m) l (aRes l A B m) with hX
  have step1 : ∀ l ∈ Ico 1 K, physCoefCut S δ N Γ f K J P χ l r *
      ∑ v ∈ range K', (α * β) v * (resMask f c v * (hz A B l v * Uz r v)) =
      (1 / (Nat.totient r : ℝ)) * X l := by
    intro l hl
    by_cases h0 : physCoefCut S δ N Γ f K J P χ l r = 0
    · simp [hX, h0]
    · have hne : physCoefAtom S δ N Γ f J P χ l r ≠ 0 := by
        intro h; apply h0; unfold physCoefCut; split_ifs <;> simp [h]
      obtain ⟨-, hflr, -⟩ := physCoefAtom_coprime hS hne
      have hfl : Nat.Coprime f l := Nat.Coprime.coprime_mul_right_right hflr
      rw [inner_urem_eq_relDisc α β hα hβ hK' hf (lt_of_lt_of_le zero_lt_one (mem_Ico.1 hl).1)
        hcf (coprime_AB_of_base hAPB hfl)]
      simp only [hX]
      ring
  rw [sum_congr rfl step1, ← mul_sum]
  congr 1
  have hzero : ∀ l, K ≤ l → X l = 0 := by
    intro l hl
    simp only [hX, physCoefCut]
    rw [if_neg (by nlinarith), zero_mul]
  have hext : ∑ l ∈ Ico 1 K, X l = ∑ l ∈ Ico 1 (2 ^ n), X l := by
    apply sum_subset (Ico_subset_Ico_right hKn)
    intro l hl hl'
    simp only [mem_Ico, not_and, not_lt] at hl hl'
    exact hzero l (hl' hl.1)
  rw [hext, sum_Ico_one_two_pow]
  rfl

/-- Moving a packet sum of absolute values inside a finite sum. -/
lemma sum_abs_sum_le {ι κ : Type*} (Ξ : Finset ι) (s : Finset κ) (g : ι → κ → ℝ) :
    ∑ ξ ∈ Ξ, |∑ a ∈ s, g ξ a| ≤ ∑ a ∈ s, ∑ ξ ∈ Ξ, |g ξ a| := by
  rw [sum_comm]
  exact sum_le_sum (fun ξ _ => abs_sum_le_sum_abs _ _)

/-- A band sum with vanishing tail is dominated by the truncated majorant. -/
lemma band_sum_le {n n0 : ℕ} (X Y : ℕ → ℝ) (hXY : ∀ i, i < n0 → X i ≤ Y i)
    (hX0 : ∀ i, n0 ≤ i → X i = 0) (hY : ∀ i, 0 ≤ Y i) :
    ∑ i ∈ range n, X i ≤ ∑ i ∈ range n0, Y i := by
  rcases le_total n n0 with h | h
  · calc ∑ i ∈ range n, X i ≤ ∑ i ∈ range n, Y i :=
          sum_le_sum (fun i hi => hXY i (lt_of_lt_of_le (mem_range.1 hi) h))
      _ ≤ ∑ i ∈ range n0, Y i :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.2 h) (fun i _ _ => hY i)
  · rw [← sum_range_add_sum_Ico X h]
    rw [sum_eq_zero (fun i hi => hX0 i (mem_Ico.1 hi).1), add_zero]
    exact sum_le_sum (fun i hi => hXY i (mem_range.1 hi))

/-- **The physical family Urem estimate, reduced to BDH energies of the common sequence.**
For a packet family `Ξ` sharing one sequence `α` (one HB/dyadic group) — packet-dependent
`β_ξ`, `Γ_ξ`, `f_ξ`, `c_ξ`, `A_ξ`, `B_ξ` — the sum over packets of `|physUrem_ξ|` (with `Γ_ξ`
counted once, inside `physUrem`) is bounded by the atom weights times the packet density
`∑_ξ |Γ_ξ| (M/f_ξ + L)` times the complete-modulus BDH energies of the masked sequences
`α^{(r)}`.  Only the dyadic bands `L = 2^i < 2^{n₀}` that can carry a nonzero coefficient
appear.  Fully unconditional. -/
theorem physical_family_urem_le {ι : Type*} (Ξ : Finset ι) (hS : S.Good) (δ N : ℝ)
    (Γ : ι → ℝ) (f c A : ι → ℕ) (B : ι → ℤ) {K n n0 Nn M K' F Kexp : ℕ} (hKn : K ≤ 2 ^ n)
    (α : ArithmeticFunction ℝ) (β : ι → ArithmeticFunction ℝ)
    (hα : ∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn)
    (hβ : ∀ ξ ∈ Ξ, ∀ m, β ξ m ≠ 0 → M ≤ m ∧ m < 2 * M) (hK' : 4 * Nn * M ≤ K')
    (hf : ∀ ξ ∈ Ξ, 0 < f ξ ∧ f ξ ≤ F) (hcf : ∀ ξ ∈ Ξ, Nat.Coprime (c ξ) (f ξ))
    (hAPB : ∀ ξ ∈ Ξ, AffinePrimesDivideBase (A ξ) (B ξ) (f ξ)) {Bβ Ca : ℝ} (hCa : 0 ≤ Ca)
    (hβ2 : ∀ ξ ∈ Ξ, ∑ m ∈ Ico M (2 * M), β ξ m ^ 2 ≤ Bβ)
    (hmult : ∀ f0, ∑ ξ ∈ Ξ with f ξ = f0, |Γ ξ| ≤ Ca * tau f0 ^ Kexp)
    (hl0 : ∀ ξ ∈ Ξ, ∀ J (P : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3) l r,
      physCoefCut S δ N (Γ ξ) (f ξ) K J P χ l r ≠ 0 → l < 2 ^ n0) :
    ∑ ξ ∈ Ξ, |physUrem S δ N (Γ ξ) (f ξ) (c ξ) (A ξ) (B ξ) K K' α (β ξ)| ≤
      ∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H, ∑ _χ : Fin S.Kc → Fin 3,
        ∑ r ∈ Ico 1 K, (1 / (Nat.totient r : ℝ)) * ∑ i ∈ range n0,
          S.atomWeight J P (S.atomColour δ N J P) * Real.sqrt Bβ *
            Real.sqrt (∑ ξ ∈ Ξ, |Γ ξ| * ((M : ℝ) / f ξ + (2 ^ i : ℕ))) *
            Real.sqrt (Ca * bdhEnergy (Ico Nn (2 * Nn)) (maskR α r) (2 * F * 2 ^ i) Kexp) := by
  have hid : ∀ ξ ∈ Ξ, physUrem S δ N (Γ ξ) (f ξ) (c ξ) (A ξ) (B ξ) K K' α (β ξ) =
      ∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H, ∑ χ : Fin S.Kc → Fin 3,
        ∑ r ∈ Ico 1 K, (1 / (Nat.totient r : ℝ)) * ∑ i ∈ range n,
          uremBlock (Ico Nn (2 * Nn)) (maskR α r) (f ξ) (c ξ) (A ξ) (B ξ) (2 ^ i) M r
            (fun l => physCoefCut S δ N (Γ ξ) (f ξ) K J P χ l r) (β ξ) := fun ξ hξ =>
    physUrem_eq_uremBlocks hS δ N (Γ ξ) hKn α (β ξ) hα (hβ ξ hξ) hK' (hf ξ hξ).1 (hcf ξ hξ)
      (hAPB ξ hξ)
  rw [sum_congr rfl (fun ξ hξ => by rw [hid ξ hξ])]
  refine (sum_abs_sum_le _ _ _).trans ?_
  gcongr with J _
  refine (sum_abs_sum_le _ _ _).trans ?_
  gcongr with P _
  refine (sum_abs_sum_le _ _ _).trans ?_
  gcongr with χ _
  refine (sum_abs_sum_le _ _ _).trans ?_
  gcongr with r hr
  have hφ : 0 ≤ 1 / (Nat.totient r : ℝ) := by positivity
  simp_rw [abs_mul, abs_of_nonneg hφ]
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hφ
  refine (sum_abs_sum_le _ _ _).trans ?_
  have hW := atomWeight_nonneg P (S.atomColour δ N J P)
  refine band_sum_le _ _ (fun i _ => ?_) (fun i hi => ?_) (fun i => by positivity)
  · refine family_urem_le_bdhEnergy Ξ (Ico Nn (2 * Nn)) (maskR α r) (Nat.two_pow_pos i) f c A B Γ
      (fun ξ l => physCoefCut S δ N (Γ ξ) (f ξ) K J P χ l r) (fun ξ m => β ξ m) hW hCa hf hcf
      ?_ ?_ hβ2 hmult
    · intro ξ hξ l hne
      have hne' : physCoefAtom S δ N (Γ ξ) (f ξ) J P χ l r ≠ 0 := by
        intro h; apply hne; simp only [physCoefCut]; split_ifs <;> simp [h]
      obtain ⟨-, hflr, -⟩ := physCoefAtom_coprime hS hne'
      have hfl : Nat.Coprime (f ξ) l := Nat.Coprime.coprime_mul_right_right hflr
      exact ⟨hfl, coprime_AB_of_base (hAPB ξ hξ) hfl⟩
    · intro ξ _ l
      simp only [physCoefCut]
      split_ifs
      · exact physCoefAtom_abs_le hS δ N (Γ ξ) (f ξ) J P χ l r
      · simp only [abs_zero]; exact mul_nonneg (abs_nonneg _) hW
  · refine sum_eq_zero (fun ξ hξ => ?_)
    rw [abs_eq_zero]
    unfold uremBlock
    refine sum_eq_zero (fun l hl => ?_)
    have : physCoefCut S δ N (Γ ξ) (f ξ) K J P χ l r = 0 := by
      by_contra hne
      have h1 := hl0 ξ hξ J P χ l r hne
      have h2 : 2 ^ n0 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
      have h3 := (mem_Ico.1 hl).1
      omega
    simp [this]

end Erdos287.Physical.TypeII.UremFamily
