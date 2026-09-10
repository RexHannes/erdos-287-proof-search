import RequestProject.Window

/-!
# Erdős Problem #287

Erdős Problem #287 asks:

> Let `k ≥ 2`.  Is it true that, for any distinct integers `1 < n₁ < ⋯ < n_k` with
> `1 = 1/n₁ + ⋯ + 1/n_k`, we must have `max (n_{i+1} - n_i) ≥ 3`?

A *counterexample* is therefore a finite set `A` of integers `> 1`, with at least two elements,
whose reciprocals sum to `1` and in which every gap between consecutive elements is at most `2`.
This is `Erdos287.Erdos287Counterexample`.

The problem is open in general.  This file sets up the "window pair" machinery which, combined
with a certified chain of prime pairs, rules out all counterexamples whose largest element is
at most `10 ^ 60`.
-/

namespace Erdos287

open Finset

/--
`A` is a counterexample to Erdős Problem #287:

* every element of `A` exceeds `1`;
* `A` has at least two elements;
* the reciprocals of the elements of `A` sum to `1`;
* every gap between consecutive elements of `A` is at most `2`, i.e. whenever `a ∈ A` is not the
  largest element, one of `a + 1`, `a + 2` again lies in `A`.
-/
def Erdos287Counterexample (A : Finset ℕ) : Prop :=
  (∀ n ∈ A, 1 < n) ∧ 2 ≤ A.card ∧ (∑ n ∈ A, (1 : ℚ) / n) = 1 ∧
    ∀ a ∈ A, (∃ b ∈ A, a < b) → (a + 1 ∈ A ∨ a + 2 ∈ A)

theorem Erdos287Counterexample.nonempty {A : Finset ℕ} (h : Erdos287Counterexample A) :
    A.Nonempty := by
  rw [← Finset.card_pos]
  have := h.2.1
  omega

/-- Sanity check that the definition is not vacuous: `{2, 3, 6}` satisfies every clause of
`Erdos287Counterexample` except the gap-at-most-two clause (`1 = 1/2 + 1/3 + 1/6`, and the gap
from `3` to `6` is `3`).  Erdős remarks that this example shows `3` would be best possible. -/
theorem two_three_six_all_but_gap :
    (∀ n ∈ ({2, 3, 6} : Finset ℕ), 1 < n) ∧ 2 ≤ ({2, 3, 6} : Finset ℕ).card ∧
      (∑ n ∈ ({2, 3, 6} : Finset ℕ), (1 : ℚ) / n) = 1 := by
  refine ⟨by decide, by decide, ?_⟩
  norm_num

/-- ... but `{2, 3, 6}` is not a counterexample, because of its gap of `3`. -/
theorem not_counterexample_two_three_six :
    ¬ Erdos287Counterexample ({2, 3, 6} : Finset ℕ) := by
  rintro ⟨-, -, -, hgap⟩
  rcases hgap 3 (by decide) ⟨6, by decide, by norm_num⟩ with h | h <;> revert h <;> decide

/--
A certificate that the prime power `p ^ a` is a *forbidden divisor* at maximum `M`:

* `p` is prime and `a ≥ 1`;
* every integer `≤ M` divisible by `p ^ a` is one of `1 · p^a, …, w · p^a` (window width `w`);
* `L` is a common multiple of `1, …, w` prime to `p`;
* for every nonempty `J ⊆ {1, …, w}` the integer `∑_{j ∈ J} L / j` is prime to `p`.

Under these conditions no set of positive integers `≤ M` whose reciprocals sum to `1` can
contain a multiple of `p ^ a` (see `Erdos287.no_dvd_of_window`).
-/
def ForbiddenPP (M p a w L : ℕ) : Prop :=
  p.Prime ∧ 0 < a ∧ M < (w + 1) * p ^ a ∧ 0 < L ∧
    (∀ j ∈ Finset.Icc 1 w, j ∣ L) ∧ ¬ p ∣ L ∧
    (∀ J ∈ (Finset.Icc 1 w).powerset, J.Nonempty → ¬ p ∣ ∑ j ∈ J, L / j)

/--
`WindowPairSupply M` says that there is a position `x` with `x + 1 ≤ M ≤ 2 * x` such that both
`x` and `x + 1` are *forbidden denominator positions* at maximum `M`: `x` is divisible by a
forbidden prime power `pu ^ au`, and `x + 1` is divisible by a forbidden prime power `pv ^ av`.
-/
def WindowPairSupply (M : ℕ) : Prop :=
  ∃ x pu au wu Lu pv av wv Lv,
    x + 1 ≤ M ∧ M ≤ 2 * x ∧
      ForbiddenPP M pu au wu Lu ∧ pu ^ au ∣ x ∧
      ForbiddenPP M pv av wv Lv ∧ pv ^ av ∣ (x + 1)

/-- A forbidden prime power really is forbidden: no element of a reciprocal representation of
`1` with all parts `≤ M` is divisible by it. -/
theorem ForbiddenPP.not_dvd {M p a w L : ℕ} (hF : ForbiddenPP M p a w L)
    {A : Finset ℕ} (hA0 : ∀ n ∈ A, 0 < n) (hAM : ∀ n ∈ A, n ≤ M)
    (hsum : ∑ n ∈ A, (1 : ℚ) / n = 1) : ∀ n ∈ A, ¬ p ^ a ∣ n := by
  obtain ⟨hp, ha, hM, hL0, hLdvd, hpL, hcond⟩ := hF
  exact no_dvd_of_window hA0 hsum hp ha
    (fun n hn => lt_of_le_of_lt (hAM n hn) hM) hL0 hLdvd hpL
    (fun J hJ => hcond J (Finset.mem_powerset.2 hJ))

/-- **Bridge.**  A window pair supply at the maximum of `A` refutes the counterexample `A`. -/
theorem not_counterexample_of_windowPairSupply {A : Finset ℕ} (h : Erdos287Counterexample A)
    (hW : WindowPairSupply (A.max' h.nonempty)) : False := by
  classical
  obtain ⟨hgt1, hcard, hsum, hgap⟩ := id h
  set M := A.max' h.nonempty with hMdef
  have hMmem : M ∈ A := Finset.max'_mem _ _
  have hAM : ∀ n ∈ A, n ≤ M := fun n hn => Finset.le_max' _ n hn
  have hA0 : ∀ n ∈ A, 0 < n := fun n hn => lt_trans one_pos (hgt1 n hn)
  obtain ⟨x, pu, au, wu, Lu, pv, av, wv, Lv, hx1, hx2, hFu, hdu, hFv, hdv⟩ := hW
  -- `x` and `x + 1` are not in `A`
  have hxA : x ∉ A := fun hmem => hFu.not_dvd hA0 hAM hsum x hmem hdu
  have hx1A : x + 1 ∉ A := fun hmem => hFv.not_dvd hA0 hAM hsum (x + 1) hmem hdv
  have hxpos : 0 < x := by omega
  -- there is an element of `A` which is at most `x`
  have hex : ∃ n ∈ A, n ≤ x := by
    by_contra hc
    push_neg at hc
    have hsub : A ⊆ Finset.Icc (x + 1) M := fun n hn =>
      Finset.mem_Icc.2 ⟨hc n hn, hAM n hn⟩
    have hcard' : A.card ≤ x := by
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      omega
    have hxQ : (0 : ℚ) < (x : ℚ) + 1 := by positivity
    have hterm : ∀ n ∈ A, (1 : ℚ) / n ≤ 1 / ((x : ℚ) + 1) := by
      intro n hn
      have h1 : ((x : ℚ) + 1) ≤ (n : ℚ) := by exact_mod_cast hc n hn
      exact one_div_le_one_div_of_le hxQ h1
    have hle : (∑ n ∈ A, (1 : ℚ) / n) ≤ (A.card : ℚ) * (1 / ((x : ℚ) + 1)) := by
      calc ∑ n ∈ A, (1 : ℚ) / n ≤ ∑ _n ∈ A, 1 / ((x : ℚ) + 1) := Finset.sum_le_sum hterm
        _ = (A.card : ℚ) * (1 / ((x : ℚ) + 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [hsum] at hle
    have hcQ : (A.card : ℚ) ≤ (x : ℚ) := by exact_mod_cast hcard'
    have h1 : (1 : ℚ) * ((x : ℚ) + 1) ≤ ((A.card : ℚ) * (1 / ((x : ℚ) + 1))) * ((x : ℚ) + 1) :=
      mul_le_mul_of_nonneg_right hle (le_of_lt hxQ)
    rw [one_mul, mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hxQ), mul_one] at h1
    linarith
  -- take the largest such element
  obtain ⟨n₁, hn₁A, hn₁x⟩ := hex
  obtain ⟨y, hyA, hyx, hymax⟩ : ∃ y ∈ A, y ≤ x ∧ ∀ n ∈ A, n ≤ x → n ≤ y := by
    obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image (A.filter (fun n => n ≤ x)) id
      ⟨n₁, by simp [hn₁A, hn₁x]⟩
    simp only [Finset.mem_filter] at hy
    exact ⟨y, hy.1, hy.2, fun n hn hnx => hmax n (by simp [hn, hnx])⟩
  have hyltx : y < x := lt_of_le_of_ne hyx (by rintro rfl; exact hxA hyA)
  have hyltM : y < M := by omega
  rcases hgap y hyA ⟨M, hMmem, hyltM⟩ with h1 | h2
  · have := hymax (y + 1) h1 (by omega)
    omega
  · have hne1 : y + 2 ≠ x := by rintro hh; rw [hh] at h2; exact hxA h2
    have hne2 : y + 2 ≠ x + 1 := by rintro hh; rw [hh] at h2; exact hx1A h2
    have := hymax (y + 2) h2 (by omega)
    omega

end Erdos287
