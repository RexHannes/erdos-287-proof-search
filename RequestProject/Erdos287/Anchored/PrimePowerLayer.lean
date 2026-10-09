import RequestProject.Erdos287.Anchored.Fingerprint

/-!
# The full prime-power layer condition

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Fix a prime `p`, a threshold power `q = p ^ a` and a window `[a₀, M]`.  The *actual* cofactor
set of the layer is

`C = { c : a₀ ≤ q * c ≤ M }`,

`L = lcm C`, and `t = v_p(L)`.  This file proves the exact equivalence between

* the **full top prime-power condition** `p ^ (t + 1) ∣ ∑_{c ∈ E} L / c`, and
* the anchored reciprocal condition `v_p(∑_{c ∈ E} 1/c) ≥ 1`,

for every nonempty `E ⊆ C`, with **no** coprimality assumption: the case `p ∣ c` is retained
and is exhibited by an explicit witness (`layer_retains_p_dvd_cofactor`).  The reduction to
the leading-digit / unit-cofactor special case is *not* performed — that firewall is the
point of this module.

The empty subset is a genuine exception and is recorded as such
(`layer_condition_empty_firewall`), which is why the equivalence carries a nonemptiness
hypothesis.
-/

open scoped BigOperators

namespace Erdos287
namespace Anchored

/-! ## A.7  A computation helper for `p`-adic valuations of explicit numbers -/

/-- `padicValNat p n = k` from the two explicit divisibility facts. -/
theorem padicValNat_eq_of_dvd_of_not_dvd {p : ℕ} [Fact p.Prime] {n k : ℕ} (hn : n ≠ 0)
    (h1 : p ^ k ∣ n) (h2 : ¬ p ^ (k + 1) ∣ n) : padicValNat p n = k := by
  have a1 := (padicValNat_dvd_iff_le hn).1 h1
  have a2 : ¬ (k + 1 ≤ padicValNat p n) := fun h => h2 ((padicValNat_dvd_iff_le hn).2 h)
  omega

/-! ## A.8  The layer cofactor set -/

/-- The cofactor set of the `q`-layer inside the window `[a₀, M]`:
`layerCofactors q a₀ M = { c : a₀ ≤ q * c ≤ M }`. -/
def layerCofactors (q a₀ M : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).filter (fun c => a₀ ≤ q * c ∧ q * c ≤ M)

@[simp] theorem mem_layerCofactors {q a₀ M c : ℕ} :
    c ∈ layerCofactors q a₀ M ↔ (1 ≤ c ∧ c ≤ M) ∧ (a₀ ≤ q * c ∧ q * c ≤ M) := by
  simp [layerCofactors, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-- Every layer cofactor is positive. -/
theorem layerCofactors_pos {q a₀ M : ℕ} : ∀ c ∈ layerCofactors q a₀ M, 0 < c := by
  intro c hc
  have := (mem_layerCofactors.1 hc).1.1
  omega

/-! ## A.9  The exact prime-power / reciprocal equivalence -/

/-- **`layer_primePower_iff`.**  `KERNEL-PROVED`.  For a finite set `C` of positive cofactors,
`L = lcmOf C`, `t = v_p(L)` and a nonempty `E ⊆ C`:

`p ^ (t + 1) ∣ ∑_{c ∈ E} L / c  ↔  v_p(∑_{c ∈ E} 1/c) ≥ 1`.

No hypothesis relates `p` to the elements of `C`; in particular cofactors divisible by `p`
are retained. -/
theorem layer_primePower_iff (p : ℕ) [Fact p.Prime] {C E : Finset ℕ} (hEC : E ⊆ C)
    (hC : ∀ c ∈ C, 0 < c) (hne : E.Nonempty) :
    p ^ (padicValNat p (lcmOf C) + 1) ∣ cofactorNum C E ↔
      1 ≤ padicValRat p (recipSum E) := by
  have hL : 0 < lcmOf C := lcmOf_pos hC
  have hS : cofactorNum C E ≠ 0 := cofactorNum_ne_zero hEC hC hne
  have hrec : recipSum E = ((cofactorNum C E : ℕ) : ℚ) / ((lcmOf C : ℕ) : ℚ) :=
    recipSum_eq_cofactorNum_div hEC hC
  have hSq : ((cofactorNum C E : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hS
  have hLq : ((lcmOf C : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have hval : padicValRat p (recipSum E)
      = (padicValNat p (cofactorNum C E) : ℤ) - (padicValNat p (lcmOf C) : ℤ) := by
    rw [hrec, padicValRat.div hSq hLq, padicValRat.of_nat, padicValRat.of_nat]
  rw [hval, padicValNat_dvd_iff_le hS]
  omega

/-- The same statement with the layer numerator written as an integer sum. -/
theorem layer_primePower_iff_int (p : ℕ) [Fact p.Prime] {C E : Finset ℕ} (hEC : E ⊆ C)
    (hC : ∀ c ∈ C, 0 < c) (hne : E.Nonempty) :
    ((p : ℤ) ^ (padicValNat p (lcmOf C) + 1) ∣ ∑ c ∈ E, ((lcmOf C / c : ℕ) : ℤ)) ↔
      1 ≤ padicValRat p (recipSum E) := by
  rw [← layer_primePower_iff p hEC hC hne]
  constructor
  · intro h
    have : ((p ^ (padicValNat p (lcmOf C) + 1) : ℕ) : ℤ) ∣ ((cofactorNum C E : ℕ) : ℤ) := by
      push_cast
      simpa [cofactorNum, Nat.cast_sum] using h
    exact_mod_cast this
  · intro h
    have : ((p ^ (padicValNat p (lcmOf C) + 1) : ℕ) : ℤ) ∣ ((cofactorNum C E : ℕ) : ℤ) := by
      exact_mod_cast h
    push_cast at this
    simpa [cofactorNum, Nat.cast_sum] using this

/-- **`anchoredFeasible_iff_layer_primePower`.**  `KERNEL-PROVED`.  The anchored local
feasibility predicate is exactly the full prime-power layer condition over the allowed
subsets, the zero state appearing explicitly as `E = ∅`. -/
theorem anchoredFeasible_iff_layer_primePower (p : ℕ) [Fact p.Prime] {C P N : Finset ℕ}
    (hC : ∀ c ∈ C, 0 < c) :
    AnchoredFeasible p C P N ↔
      ∃ E ∈ allowed C P N,
        E = ∅ ∨ p ^ (padicValNat p (lcmOf C) + 1) ∣ cofactorNum C E := by
  unfold AnchoredFeasible
  constructor
  · rintro ⟨E, hE, h⟩
    refine ⟨E, hE, ?_⟩
    rcases Finset.eq_empty_or_nonempty E with hE0 | hne
    · exact Or.inl hE0
    · have hEC : E ⊆ C := (mem_allowed.1 hE).2.1
      have hpos : 0 < recipSum E := recipSum_pos hne (fun c hc => hC c (hEC hc))
      rcases h with h | h
      · exact absurd h hpos.ne'
      · exact Or.inr ((layer_primePower_iff p hEC hC hne).2 h)
  · rintro ⟨E, hE, h⟩
    refine ⟨E, hE, ?_⟩
    rcases h with h | h
    · exact Or.inl (by simp [h])
    · rcases Finset.eq_empty_or_nonempty E with hE0 | hne
      · exact Or.inl (by simp [hE0])
      · have hEC : E ⊆ C := (mem_allowed.1 hE).2.1
        exact Or.inr ((layer_primePower_iff p hEC hC hne).1 h)

/-! ## A.10  Firewalls -/

/-- **`layer_condition_empty_firewall`.**  `KERNEL-PROVED`.  The nonemptiness hypothesis of
`layer_primePower_iff` is necessary: for `E = ∅` the divisibility holds trivially while the
valuation condition fails (`v_p(0) = 0` by convention). -/
theorem layer_condition_empty_firewall (p : ℕ) [Fact p.Prime] (C : Finset ℕ) :
    p ^ (padicValNat p (lcmOf C) + 1) ∣ cofactorNum C ∅ ∧
      ¬ (1 ≤ padicValRat p (recipSum (∅ : Finset ℕ))) := by
  refine ⟨by simp, ?_⟩
  simp [recipSum]

/-- **`layer_retains_p_dvd_cofactor`.**  `KERNEL-PROVED`.  An explicit witness in which the
selected cofactors are themselves divisible by `p`: with `C = {2,3,6}`, `E = {2,6}` and
`p = 2` the full prime-power condition holds, hence so does the valuation condition.  The
layer condition therefore genuinely covers the case `p ∣ c`, and is *not* reduced to the
unit-cofactor special case. -/
theorem layer_retains_p_dvd_cofactor :
    lcmOf {2, 3, 6} = 6 ∧ cofactorNum {2, 3, 6} {2, 6} = 4 ∧
      (2 ∣ (2 : ℕ) ∧ 2 ∣ (6 : ℕ)) ∧
      1 ≤ padicValRat 2 (recipSum {2, 6}) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlcm : lcmOf {2, 3, 6} = 6 := by decide
  have hnum : cofactorNum {2, 3, 6} {2, 6} = 4 := by decide
  have ht : padicValNat 2 (lcmOf {2, 3, 6}) = 1 := by
    rw [hlcm]
    exact padicValNat_eq_of_dvd_of_not_dvd (by norm_num) (by norm_num) (by norm_num)
  have hEC : ({2, 6} : Finset ℕ) ⊆ ({2, 3, 6} : Finset ℕ) := by decide
  have hC : ∀ c ∈ ({2, 3, 6} : Finset ℕ), 0 < c := by decide
  have hne : ({2, 6} : Finset ℕ).Nonempty := ⟨2, by decide⟩
  refine ⟨hlcm, hnum, ⟨⟨1, rfl⟩, ⟨3, rfl⟩⟩, ?_⟩
  refine (layer_primePower_iff 2 hEC hC hne).1 ?_
  rw [ht, hnum]
  norm_num

end Anchored
end Erdos287
