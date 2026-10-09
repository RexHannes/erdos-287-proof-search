import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V8 §2B: canonical saturation

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The canonical saturation of a Boolean word `x` on a finite interval `I` with respect to a
modulus `L` (in the programme `L = L_T = lcm(1,…,T)`) is

  `x*_n = 1` if `n ∣ L`,   `x*_n = x_n` otherwise.

Everything in this file is an **elementary, fully kernel-proved** transformation theorem:

* `saturate_mono`                — only `0 → 1` flips;
* `saturate_endpoint`            — selected endpoints (indeed all selected points) are preserved;
* `saturate_noAdjZero`           — the no-`00` property is preserved;
* `saturate_denomEntry`          — denominator-entry into `L` is preserved;
* `saturate_forbidden_subset`    — the literal forbidden (zero) set can only shrink;
* `saturate_forbidden_eq`        — the forbidden set after saturation is exactly the old
  forbidden set minus the divisors of `L`.

The **asymptotic counting** statement `|{n ∈ I : n ∤ L_T}| = o(M)` is *not* proved here; it is
recorded as the uninhabited external interface `NonDivisorCountSublinear`.
-/

open scoped BigOperators

namespace Erdos287
namespace ResearchBankV8
namespace Saturation

/-- The canonical saturation of `x` at modulus `L`. -/
def saturate (L : ℕ) (x : ℕ → Bool) : ℕ → Bool :=
  fun n => if n ∣ L then true else x n

/-- No two consecutive members of the finite set `I` are both zeros of `x`. -/
def NoAdjZero (I : Finset ℕ) (x : ℕ → Bool) : Prop :=
  ∀ n, n ∈ I → n + 1 ∈ I → x n = true ∨ x (n + 1) = true

/-- The selected set of `x` on `I`. -/
def selected (I : Finset ℕ) (x : ℕ → Bool) : Finset ℕ := I.filter fun n => x n = true

/-- The literal forbidden (zero) set of `x` on `I`. -/
def forbidden (I : Finset ℕ) (x : ℕ → Bool) : Finset ℕ := I.filter fun n => x n = false

/-- **Denominator-entry into `L`**: `L · ∑_{n selected} 1/n` is an integer, i.e. the reduced
denominator of the selected reciprocal sum divides `L`. -/
def DenomEntry (I : Finset ℕ) (x : ℕ → Bool) (L : ℕ) : Prop :=
  ∃ k : ℤ, (L : ℚ) * ∑ n ∈ selected I x, (1 : ℚ) / n = k

/-- **Only `0 → 1`.** -/
theorem saturate_mono (L : ℕ) (x : ℕ → Bool) (n : ℕ) (h : x n = true) :
    saturate L x n = true := by
  unfold saturate; split_ifs <;> simp [h]

/-- The only changed coordinates are former zeros that divide `L`, and they become ones. -/
theorem saturate_changed (L : ℕ) (x : ℕ → Bool) (n : ℕ) (h : saturate L x n ≠ x n) :
    x n = false ∧ n ∣ L ∧ saturate L x n = true := by
  unfold saturate at *
  split_ifs at * with hd
  · cases hx : x n <;> simp_all
  · exact absurd rfl h

/-- **Selected endpoints are preserved** (in fact every selected point is). -/
theorem saturate_endpoint (L : ℕ) (x : ℕ → Bool) {A M : ℕ} (hA : x A = true)
    (hM : x M = true) : saturate L x A = true ∧ saturate L x M = true :=
  ⟨saturate_mono L x A hA, saturate_mono L x M hM⟩

/-- **No-`00` is preserved.** -/
theorem saturate_noAdjZero (L : ℕ) (I : Finset ℕ) (x : ℕ → Bool) (h : NoAdjZero I x) :
    NoAdjZero I (saturate L x) := by
  intro n hn hn1
  rcases h n hn hn1 with h1 | h1
  · exact Or.inl (saturate_mono L x n h1)
  · exact Or.inr (saturate_mono L x (n + 1) h1)

/-- The selected set only grows. -/
theorem selected_subset_saturate (L : ℕ) (I : Finset ℕ) (x : ℕ → Bool) :
    selected I x ⊆ selected I (saturate L x) := by
  intro n hn
  simp only [selected, Finset.mem_filter] at *
  exact ⟨hn.1, saturate_mono L x n hn.2⟩

/-- **The literal forbidden set can only shrink.** -/
theorem saturate_forbidden_subset (L : ℕ) (I : Finset ℕ) (x : ℕ → Bool) :
    forbidden I (saturate L x) ⊆ forbidden I x := by
  intro n hn
  simp only [forbidden, Finset.mem_filter, saturate] at *
  refine ⟨hn.1, ?_⟩
  split_ifs at hn with hd
  · simp at hn
  · exact hn.2

/-- The forbidden set after saturation is exactly the old one minus the divisors of `L`. -/
theorem saturate_forbidden_eq (L : ℕ) (I : Finset ℕ) (x : ℕ → Bool) :
    forbidden I (saturate L x) = (forbidden I x).filter fun n => ¬ n ∣ L := by
  ext n
  simp only [forbidden, Finset.mem_filter, saturate]
  split_ifs with hd <;> simp [hd]

/-- The newly selected points all divide `L`. -/
theorem saturate_new_dvd (L : ℕ) (I : Finset ℕ) (x : ℕ → Bool) :
    ∀ n ∈ selected I (saturate L x) \ selected I x, n ∣ L := by
  intro n hn
  simp only [selected, Finset.mem_sdiff, Finset.mem_filter, saturate] at hn
  by_contra hd
  simp [hd] at hn
  obtain ⟨⟨h1, h2⟩, h3⟩ := hn
  simp [h3 h1] at h2

/-- A sum of reciprocals of divisors of `L`, multiplied by `L`, is an integer. -/
theorem integral_of_dvd_sum (L : ℕ) (S : Finset ℕ) (hS : ∀ n ∈ S, n ∣ L) :
    ∃ k : ℤ, (L : ℚ) * ∑ n ∈ S, (1 : ℚ) / n = k := by
  refine ⟨∑ n ∈ S, ((L / n : ℕ) : ℤ), ?_⟩
  rw [Finset.mul_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have : L = 0 := Nat.eq_zero_of_zero_dvd (hS 0 hn)
    subst this; simp
  · rw [Int.cast_natCast, Nat.cast_div (hS n hn) (by positivity)]
    ring

/-- **Denominator-entry is preserved by saturation.** -/
theorem saturate_denomEntry (L : ℕ) (I : Finset ℕ) (x : ℕ → Bool) (h : DenomEntry I x L) :
    DenomEntry I (saturate L x) L := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨k', hk'⟩ := integral_of_dvd_sum L _ (saturate_new_dvd L I x)
  refine ⟨k + k', ?_⟩
  have hsplit := Finset.sum_sdiff (f := fun n : ℕ => (1 : ℚ) / n)
    (selected_subset_saturate L I x)
  rw [← hsplit, mul_add, hk, hk']
  push_cast; ring

/-- The saturation is idempotent. -/
theorem saturate_idem (L : ℕ) (x : ℕ → Bool) : saturate L (saturate L x) = saturate L x := by
  funext n; unfold saturate; split_ifs <;> rfl

/-- After saturation, every divisor of `L` is selected. -/
theorem saturate_selects_divisors (L : ℕ) (x : ℕ → Bool) (n : ℕ) (h : n ∣ L) :
    saturate L x n = true := by
  simp [saturate, h]

/-! ## External asymptotic counting interface (uninhabited) -/

/-- **External interface — NOT proved here.**  The asymptotic statement that the non-divisors of
`L_T` in the interval `[A(M), M]` form a set of size `o(M)`.  Here `A T : ℕ → ℕ` are the interval
start and the cutoff as functions of `M`.  This is a prime-counting statement (it follows from
PNT-type inputs); it is recorded only as a proposition and is never inhabited in this bank. -/
def NonDivisorCountSublinear (A T : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ M ≥ M₀,
    ((((Finset.Icc (A M) M).filter fun n => ¬ n ∣ (Finset.Icc 1 (T M)).lcm id).card : ℕ) : ℝ)
      ≤ ε * M

/-- **Firewall.**  The forbidden set of the saturated word is contained in the non-divisor set;
the elementary saturation theorems never use the counting interface. -/
theorem forbidden_saturate_subset_nonDivisors (L : ℕ) (I : Finset ℕ) (x : ℕ → Bool) :
    forbidden I (saturate L x) ⊆ I.filter fun n => ¬ n ∣ L := by
  intro n hn
  rw [saturate_forbidden_eq] at hn
  simp only [forbidden, Finset.mem_filter] at *
  exact ⟨hn.1.1, hn.2⟩

/-- **Conditional corollary** (the counting interface is an explicit hypothesis): the saturated
forbidden set is `≤ ε M` eventually. -/
theorem saturate_forbidden_small_of_interface (A T : ℕ → ℕ)
    (hcount : NonDivisorCountSublinear A T) (x : ℕ → ℕ → Bool) :
    ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ M ≥ M₀,
      (((forbidden (Finset.Icc (A M) M)
          (saturate ((Finset.Icc 1 (T M)).lcm id) (x M))).card : ℕ) : ℝ) ≤ ε * M := by
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := hcount ε hε
  refine ⟨M₀, fun M hM => le_trans ?_ (hM₀ M hM)⟩
  exact_mod_cast Finset.card_le_card (forbidden_saturate_subset_nonDivisors _ _ _)

end Saturation
end ResearchBankV8
end Erdos287
