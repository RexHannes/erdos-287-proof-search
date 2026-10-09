import RequestProject.Erdos287.Direct.PathPolynomial

/-!
# Route D — the finite all-target reciprocal lemma (finite Fourier adapter)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This module proves, *in the kernel*, the finite Fourier adapter used by the simultaneous
prime-component completion step, and isolates the analytic input as an interface
proposition — never as an axiom.

* `subsetSumCount q C a t` counts the binary selections `S ⊆ C` with `∑_{n ∈ S} a n = t`
  in `ZMod q`.
* `char_sum_identity` is the exact finite Fourier identity
  `q · N(t) = ∑_ψ ψ(−t) ∏_{n ∈ C} (1 + ψ(a n))`, the sum running over all additive
  characters of `ZMod q`.
* `subsetSumCount_pos_of_bound` is the sufficient condition: if every nontrivial character
  product is `≤ B` in absolute value and `(q − 1)·B < 2^{|C|}`, then **every** target is
  attained.
* `ReciprocalExpSumInterface` is the (external, unformalised) exponential-sum input for the
  reciprocal system `a n = n⁻¹`; `allTargets_of_expSumInterface` is the deterministic
  consumer.  The interface is a hypothesis of the theorem, not an axiom of the file.
-/

open scoped BigOperators

namespace Erdos287
namespace Direct

/-! ## D.22  Binary subset sums in `ZMod q` -/

variable {q : ℕ}

/-- The number of binary selections from `C` whose `a`-sum equals the target `t`. -/
def subsetSumCount (q : ℕ) (C : Finset ℕ) (a : ℕ → ZMod q) (t : ZMod q) : ℕ :=
  (C.powerset.filter (fun S => ∑ n ∈ S, a n = t)).card

/-- **`subsetSumCount_pos_iff`.**  `KERNEL-PROVED`.  Positivity of the count is exactly
attainability of the target. -/
theorem subsetSumCount_pos_iff (q : ℕ) (C : Finset ℕ) (a : ℕ → ZMod q) (t : ZMod q) :
    0 < subsetSumCount q C a t ↔ ∃ S ⊆ C, ∑ n ∈ S, a n = t := by
  rw [subsetSumCount, Finset.card_pos]
  constructor
  · rintro ⟨S, hS⟩
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    exact ⟨S, hS.1, hS.2⟩
  · rintro ⟨S, hSC, hS⟩
    exact ⟨S, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hSC, hS⟩⟩

theorem addChar_sum_eq_prod {A : Type*} [AddCommGroup A] (ψ : AddChar A ℂ) (s : Finset ℕ)
    (f : ℕ → A) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ψ.map_add_eq_mul, ih]

/-- **`prod_one_add_eq_sum_subsets`.**  `KERNEL-PROVED`.  Expansion of the character product
over binary selections. -/
theorem prod_one_add_eq_sum_subsets (C : Finset ℕ) (x : ℕ → ℂ) :
    ∏ n ∈ C, (1 + x n) = ∑ S ∈ C.powerset, ∏ n ∈ S, x n := by
  classical
  have := Finset.prod_add x (fun _ => (1 : ℂ)) C
  simp only [mul_one, Finset.prod_const_one] at this
  simpa [add_comm] using this

/-- **`char_sum_identity`.**  `KERNEL-PROVED`.  The exact finite Fourier identity for the
number of binary subset sums hitting a prescribed target of `ZMod q`. -/
theorem char_sum_identity [NeZero q] (C : Finset ℕ) (a : ℕ → ZMod q) (t : ZMod q) :
    (q : ℂ) * (subsetSumCount q C a t : ℂ) =
      ∑ ψ : AddChar (ZMod q) ℂ, ψ (-t) * ∏ n ∈ C, (1 + ψ (a n)) := by
  classical
  have hcard : (Fintype.card (ZMod q) : ℂ) = (q : ℂ) := by rw [ZMod.card q]
  calc (q : ℂ) * (subsetSumCount q C a t : ℂ)
      = ∑ S ∈ C.powerset, (if (∑ n ∈ S, a n) - t = 0 then (Fintype.card (ZMod q) : ℂ) else 0) := by
        rw [subsetSumCount, Finset.card_filter]
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        by_cases h : (∑ n ∈ S, a n) = t
        · simp [h]
        · have h' : (∑ n ∈ S, a n) - t ≠ 0 := sub_ne_zero_of_ne h
          simp [h, h']
    _ = ∑ S ∈ C.powerset, ∑ ψ : AddChar (ZMod q) ℂ, ψ ((∑ n ∈ S, a n) - t) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [AddChar.sum_apply_eq_ite]
    _ = ∑ ψ : AddChar (ZMod q) ℂ, ∑ S ∈ C.powerset, ψ (-t) * ∏ n ∈ S, ψ (a n) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun chi _ => Finset.sum_congr rfl fun S _ => ?_
        rw [show (∑ n ∈ S, a n) - t = (-t) + ∑ n ∈ S, a n by ring, chi.map_add_eq_mul,
          addChar_sum_eq_prod]
    _ = ∑ ψ : AddChar (ZMod q) ℂ, ψ (-t) * ∏ n ∈ C, (1 + ψ (a n)) := by
        refine Finset.sum_congr rfl fun ψ _ => ?_
        rw [← Finset.mul_sum, prod_one_add_eq_sum_subsets]

/-! ## D.23  The sufficient condition: every target is attained -/

/-- **`subsetSumCount_pos_of_bound`.**  `KERNEL-PROVED`.  If every nontrivial character
product is bounded by `B` and `(q − 1)·B < 2^{|C|}`, then every target of `ZMod q` is a binary
subset sum of `a` over `C`. -/
theorem subsetSumCount_pos_of_bound [NeZero q] (C : Finset ℕ) (a : ℕ → ZMod q) (B : ℝ)
    (hB : ∀ ψ : AddChar (ZMod q) ℂ, ψ ≠ 0 → ‖∏ n ∈ C, (1 + ψ (a n))‖ ≤ B)
    (hlt : ((q : ℝ) - 1) * B < 2 ^ C.card) (t : ZMod q) :
    0 < subsetSumCount q C a t := by
  classical
  set F : AddChar (ZMod q) ℂ → ℂ := fun ψ => ψ (-t) * ∏ n ∈ C, (1 + ψ (a n)) with hF
  have hsplit : ∑ ψ : AddChar (ZMod q) ℂ, F ψ
      = F 0 + ∑ ψ ∈ (Finset.univ.erase (0 : AddChar (ZMod q) ℂ)), F ψ :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ (0 : AddChar (ZMod q) ℂ))).symm
  have hF0 : F 0 = (2 : ℂ) ^ C.card := by
    simp [hF, AddChar.zero_apply]
    norm_num
  -- the nontrivial characters contribute at most `(q-1)·B`
  have hcardChar : (Finset.univ.erase (0 : AddChar (ZMod q) ℂ)).card = q - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, AddChar.card_eq,
      ZMod.card]
  have hbound : ‖∑ ψ ∈ (Finset.univ.erase (0 : AddChar (ZMod q) ℂ)), F ψ‖ ≤ ((q : ℝ) - 1) * B := by
    have hq1 : (1 : ℕ) ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
    calc ‖∑ ψ ∈ (Finset.univ.erase (0 : AddChar (ZMod q) ℂ)), F ψ‖
        ≤ ∑ ψ ∈ (Finset.univ.erase (0 : AddChar (ZMod q) ℂ)), ‖F ψ‖ := norm_sum_le _ _
      _ ≤ ∑ _ψ ∈ (Finset.univ.erase (0 : AddChar (ZMod q) ℂ)), B := by
          refine Finset.sum_le_sum fun ψ hψ => ?_
          have hψ0 : ψ ≠ 0 := Finset.ne_of_mem_erase hψ
          rw [hF]
          simp only [norm_mul, AddChar.norm_apply, one_mul]
          exact hB ψ hψ0
      _ = ((q : ℕ) - 1 : ℕ) * B := by rw [Finset.sum_const, hcardChar, nsmul_eq_mul]
      _ = ((q : ℝ) - 1) * B := by
          congr 1
          have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
            have := Nat.cast_sub (R := ℝ) hq1
            simpa using this
          rw [hcast]
  -- hence the total is positive
  have hid := char_sum_identity C a t
  rw [← hF] at hid
  rw [hsplit, hF0] at hid
  have hre : (2 : ℝ) ^ C.card - ((q : ℝ) - 1) * B ≤ ‖(q : ℂ) * (subsetSumCount q C a t : ℂ)‖ := by
    have h2 : ‖(2 : ℂ) ^ C.card‖ = (2 : ℝ) ^ C.card := by
      rw [norm_pow]; norm_num
    have h1 : ‖(2 : ℂ) ^ C.card‖ ≤ ‖(q : ℂ) * (subsetSumCount q C a t : ℂ)‖ +
        ‖∑ ψ ∈ (Finset.univ.erase (0 : AddChar (ZMod q) ℂ)), F ψ‖ := by
      have hsub : (2 : ℂ) ^ C.card
          = ((q : ℂ) * (subsetSumCount q C a t : ℂ))
            - ∑ ψ ∈ (Finset.univ.erase (0 : AddChar (ZMod q) ℂ)), F ψ := by
        rw [hid]; ring
      rw [hsub]
      exact norm_sub_le _ _
    rw [h2] at h1
    linarith [hbound]
  have hpos : (0 : ℝ) < ‖(q : ℂ) * (subsetSumCount q C a t : ℂ)‖ := by linarith
  rcases Nat.eq_zero_or_pos (subsetSumCount q C a t) with h0 | h0
  · rw [h0] at hpos; simp at hpos
  · exact h0

/-! ## D.24  The analytic interface and its deterministic consumer -/

/-- **Interface (external, unformalised): reciprocal exponential-sum bound.**  The
Bourgain–Garaev-type input asserting that every nontrivial additive character product over the
reciprocal system `n ↦ n⁻¹ (mod q)` on the reservoir `C` is at most `B` in modulus.  This is an
*explicit hypothesis*: no axiom asserts it anywhere in this project. -/
def ReciprocalExpSumInterface (q : ℕ) (C : Finset ℕ) (B : ℝ) : Prop :=
  ∀ ψ : AddChar (ZMod q) ℂ, ψ ≠ 0 → ‖∏ n ∈ C, (1 + ψ ((n : ZMod q)⁻¹))‖ ≤ B

/-- Every residue is an inverse binary subset sum of the reservoir `C`. -/
def AttainsAllTargets (q : ℕ) (C : Finset ℕ) : Prop :=
  ∀ t : ZMod q, ∃ S ⊆ C, ∑ n ∈ S, (n : ZMod q)⁻¹ = t

/-- **`allTargets_of_expSumInterface`.**  `KERNEL-PROVED` bridge, `CONDITIONAL` on the
exponential-sum interface: under the interface bound and the size condition
`(q − 1)·B < 2^{|C|}`, the reservoir attains every target. -/
theorem allTargets_of_expSumInterface [NeZero q] {C : Finset ℕ} {B : ℝ}
    (hBG : ReciprocalExpSumInterface q C B) (hlt : ((q : ℝ) - 1) * B < 2 ^ C.card) :
    AttainsAllTargets q C := by
  intro t
  have := subsetSumCount_pos_of_bound C (fun n => (n : ZMod q)⁻¹) B hBG hlt t
  exact (subsetSumCount_pos_iff q C (fun n => (n : ZMod q)⁻¹) t).1 this

end Direct
end Erdos287
