import Mathlib

/-!
# Quadratic-Kummer backend, layer 1: the finite Cauchy / correlation compiler

This file contains **no number theory at all**.  It isolates the purely finite
Cauchy–Schwarz step of a bilinear-form estimate: whatever the kernel `K` is, if its
`n`-correlations `∑_m K(m,n₁)K(m,n₂)` are bounded by `Mb` on a sparse symmetric
"exceptional" relation (at most `s` partners per index) and by `R` otherwise, then the
bilinear form obeys

`(∑_{m,n} α_m β_n K(m,n))² ≤ ‖α‖₂² ‖β‖₂² (s·Mb + R·|N|)`.

This is the exact shape the quadratic-Kummer argument needs; the arithmetic content
(root-stabilizer algebra, Weil/completion bounds) lives elsewhere and is *not* assumed
here.

## Main results

* `Erdos287.Kummer.abs_mul_abs_le_half_add` — the elementary AM–GM step;
* `Erdos287.Kummer.exceptional_double_sum_le` — the sparse symmetric counting step;
* `Erdos287.Kummer.kummer_bilinear_of_correlation_bounds` — the compiler.
-/

open scoped BigOperators

namespace Erdos287
namespace Kummer

variable {ιM ιN : Type*}

/-- `|x| * |y| ≤ (x² + y²)/2`. -/
theorem abs_mul_abs_le_half_add (x y : ℝ) : |x| * |y| ≤ (x ^ 2 + y ^ 2) / 2 := by
  nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y, abs_nonneg x, abs_nonneg y]

/-- **Sparse symmetric counting.**  If `exc n ⊆ In` has at most `s` elements for each
`n ∈ In` and the relation `n₂ ∈ exc n₁` is symmetric, then

`∑_{n₁ ∈ In} ∑_{n₂ ∈ exc n₁} |β n₁| |β n₂| ≤ s · ∑_{n ∈ In} β n²`. -/
theorem exceptional_double_sum_le [DecidableEq ιN] (In : Finset ιN) (exc : ιN → Finset ιN)
    (beta : ιN → ℝ) (s : ℝ)
    (hsub : ∀ n, exc n ⊆ In)
    (hcard : ∀ n ∈ In, ((exc n).card : ℝ) ≤ s)
    (hsymm : ∀ n₁ ∈ In, ∀ n₂ ∈ In, (n₂ ∈ exc n₁ ↔ n₁ ∈ exc n₂)) :
    ∑ n₁ ∈ In, ∑ n₂ ∈ exc n₁, |beta n₁| * |beta n₂| ≤ s * ∑ n ∈ In, beta n ^ 2 := by
  classical
  -- Step 1: AM–GM termwise.
  have step1 : ∑ n₁ ∈ In, ∑ n₂ ∈ exc n₁, |beta n₁| * |beta n₂|
      ≤ ∑ n₁ ∈ In, ∑ n₂ ∈ exc n₁, ((beta n₁) ^ 2 + (beta n₂) ^ 2) / 2 := by
    refine Finset.sum_le_sum ?_
    intro n₁ _
    refine Finset.sum_le_sum ?_
    intro n₂ _
    exact abs_mul_abs_le_half_add _ _
  -- Step 2: split into the "row" part and the "column" part.
  have hsplit : ∑ n₁ ∈ In, ∑ n₂ ∈ exc n₁, ((beta n₁) ^ 2 + (beta n₂) ^ 2) / 2
      = (∑ n₁ ∈ In, ((exc n₁).card : ℝ) * (beta n₁) ^ 2) / 2
        + (∑ n₁ ∈ In, ∑ n₂ ∈ exc n₁, (beta n₂) ^ 2) / 2 := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro n₁ _
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  -- Step 3: the row part.
  have hrow : ∑ n₁ ∈ In, ((exc n₁).card : ℝ) * (beta n₁) ^ 2 ≤ s * ∑ n ∈ In, beta n ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro n hn
    exact mul_le_mul_of_nonneg_right (hcard n hn) (sq_nonneg _)
  -- Step 4: the column part, via symmetry of the exceptional relation.
  have hcol : ∑ n₁ ∈ In, ∑ n₂ ∈ exc n₁, (beta n₂) ^ 2 ≤ s * ∑ n ∈ In, beta n ^ 2 := by
    have hrewrite : ∀ n₁ : ιN, ∑ n₂ ∈ exc n₁, (beta n₂) ^ 2
        = ∑ n₂ ∈ In, (if n₂ ∈ exc n₁ then (beta n₂) ^ 2 else 0) := by
      intro n₁
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hsub n₁)]
    calc ∑ n₁ ∈ In, ∑ n₂ ∈ exc n₁, (beta n₂) ^ 2
        = ∑ n₁ ∈ In, ∑ n₂ ∈ In, (if n₂ ∈ exc n₁ then (beta n₂) ^ 2 else 0) :=
          Finset.sum_congr rfl (fun n₁ _ => hrewrite n₁)
      _ = ∑ n₂ ∈ In, ∑ n₁ ∈ In, (if n₂ ∈ exc n₁ then (beta n₂) ^ 2 else 0) := Finset.sum_comm
      _ = ∑ n₂ ∈ In, ((In.filter (fun n₁ => n₂ ∈ exc n₁)).card : ℝ) * (beta n₂) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro n₂ _
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ s * ∑ n ∈ In, beta n ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum ?_
          intro n₂ hn₂
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have hsubset : In.filter (fun n₁ => n₂ ∈ exc n₁) ⊆ exc n₂ := by
            intro y hy
            simp only [Finset.mem_filter] at hy
            exact (hsymm y hy.1 n₂ hn₂).1 hy.2
          have := Finset.card_le_card hsubset
          calc ((In.filter (fun n₁ => n₂ ∈ exc n₁)).card : ℝ) ≤ ((exc n₂).card : ℝ) := by
                exact_mod_cast this
            _ ≤ s := hcard n₂ hn₂
  linarith [step1, hsplit.le, hsplit.ge, hrow, hcol]

/-- **Finite Cauchy / correlation compiler.**

Hypotheses (all finite, no arithmetic):

* `exc n ⊆ In` is an "exceptional" relation, symmetric on `In`, with at most `s`
  partners per index;
* the correlation `∑_{m ∈ Im} K m n₁ * K m n₂` is bounded in absolute value by `Mb` for
  exceptional pairs and by `R` for all other pairs from `In`.

Conclusion:

`(∑_{m,n} α_m β_n K(m,n))² ≤ (∑ α²)(∑ β²) (s·Mb + R·|In|)`. -/
theorem kummer_bilinear_of_correlation_bounds [DecidableEq ιN]
    (Im : Finset ιM) (In : Finset ιN)
    (alpha : ιM → ℝ) (beta : ιN → ℝ) (K : ιM → ιN → ℝ)
    (exc : ιN → Finset ιN) (s Mb R : ℝ)
    (hsub : ∀ n, exc n ⊆ In)
    (hcard : ∀ n ∈ In, ((exc n).card : ℝ) ≤ s)
    (hsymm : ∀ n₁ ∈ In, ∀ n₂ ∈ In, (n₂ ∈ exc n₁ ↔ n₁ ∈ exc n₂))
    (hMb0 : 0 ≤ Mb) (hR0 : 0 ≤ R)
    (hExc : ∀ n₁ ∈ In, ∀ n₂ ∈ exc n₁, |∑ m ∈ Im, K m n₁ * K m n₂| ≤ Mb)
    (hNonExc : ∀ n₁ ∈ In, ∀ n₂ ∈ In, n₂ ∉ exc n₁ → |∑ m ∈ Im, K m n₁ * K m n₂| ≤ R) :
    (∑ m ∈ Im, ∑ n ∈ In, alpha m * beta n * K m n) ^ 2
      ≤ (∑ m ∈ Im, alpha m ^ 2) * (∑ n ∈ In, beta n ^ 2)
        * (s * Mb + R * In.card) := by
  classical
  -- Rewrite the bilinear form as `∑_m α_m · g m`.
  set g : ιM → ℝ := fun m => ∑ n ∈ In, beta n * K m n with hg
  have hform : ∑ m ∈ Im, ∑ n ∈ In, alpha m * beta n * K m n = ∑ m ∈ Im, alpha m * g m := by
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [hg, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  -- Cauchy–Schwarz in `m`.
  have hCS : (∑ m ∈ Im, alpha m * g m) ^ 2
      ≤ (∑ m ∈ Im, alpha m ^ 2) * (∑ m ∈ Im, g m ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Im alpha g
  -- Expand `∑_m g m ^ 2` into correlations.
  have hexpand : ∑ m ∈ Im, g m ^ 2
      = ∑ n₁ ∈ In, ∑ n₂ ∈ In, (beta n₁ * beta n₂) * (∑ m ∈ Im, K m n₁ * K m n₂) := by
    have hstep : ∀ m, g m ^ 2
        = ∑ n₁ ∈ In, ∑ n₂ ∈ In, (beta n₁ * beta n₂) * (K m n₁ * K m n₂) := by
      intro m
      rw [hg, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl (fun n₁ _ => Finset.sum_congr rfl (fun n₂ _ => by ring))
    calc ∑ m ∈ Im, g m ^ 2
        = ∑ m ∈ Im, ∑ n₁ ∈ In, ∑ n₂ ∈ In, (beta n₁ * beta n₂) * (K m n₁ * K m n₂) :=
          Finset.sum_congr rfl (fun m _ => hstep m)
      _ = ∑ n₁ ∈ In, ∑ m ∈ Im, ∑ n₂ ∈ In, (beta n₁ * beta n₂) * (K m n₁ * K m n₂) :=
          Finset.sum_comm
      _ = ∑ n₁ ∈ In, ∑ n₂ ∈ In, ∑ m ∈ Im, (beta n₁ * beta n₂) * (K m n₁ * K m n₂) :=
          Finset.sum_congr rfl (fun n₁ _ => Finset.sum_comm)
      _ = ∑ n₁ ∈ In, ∑ n₂ ∈ In, (beta n₁ * beta n₂) * (∑ m ∈ Im, K m n₁ * K m n₂) := by
          refine Finset.sum_congr rfl (fun n₁ _ => Finset.sum_congr rfl (fun n₂ _ => ?_))
          rw [Finset.mul_sum]
  -- Bound the correlation sum.
  have hbound : ∑ m ∈ Im, g m ^ 2
      ≤ (∑ n ∈ In, beta n ^ 2) * (s * Mb + R * In.card) := by
    rw [hexpand]
    -- termwise absolute bound
    have habs : ∀ n₁ ∈ In, ∀ n₂ ∈ In,
        (beta n₁ * beta n₂) * (∑ m ∈ Im, K m n₁ * K m n₂)
          ≤ |beta n₁| * |beta n₂| *
            (if n₂ ∈ exc n₁ then Mb else R) := by
      intro n₁ h₁ n₂ h₂
      have hcorr : |(beta n₁ * beta n₂) * (∑ m ∈ Im, K m n₁ * K m n₂)|
          ≤ |beta n₁| * |beta n₂| * (if n₂ ∈ exc n₁ then Mb else R) := by
        rw [abs_mul, abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        by_cases hmem : n₂ ∈ exc n₁
        · simp only [hmem, if_true]
          exact hExc n₁ h₁ n₂ hmem
        · simp only [hmem, if_false]
          exact hNonExc n₁ h₁ n₂ h₂ hmem
      exact le_trans (le_abs_self _) hcorr
    have hle1 : ∑ n₁ ∈ In, ∑ n₂ ∈ In, (beta n₁ * beta n₂) * (∑ m ∈ Im, K m n₁ * K m n₂)
        ≤ ∑ n₁ ∈ In, ∑ n₂ ∈ In, |beta n₁| * |beta n₂| *
            (if n₂ ∈ exc n₁ then Mb else R) := by
      refine Finset.sum_le_sum ?_
      intro n₁ h₁
      exact Finset.sum_le_sum (fun n₂ h₂ => habs n₁ h₁ n₂ h₂)
    -- split the indicator: `Mb` on the exceptional part, `R` everywhere
    have hle2 : ∀ n₁ ∈ In, ∑ n₂ ∈ In, |beta n₁| * |beta n₂| *
          (if n₂ ∈ exc n₁ then Mb else R)
        ≤ (∑ n₂ ∈ exc n₁, |beta n₁| * |beta n₂|) * Mb
          + (∑ n₂ ∈ In, |beta n₁| * |beta n₂|) * R := by
      intro n₁ _
      have hrw : ∑ n₂ ∈ In, |beta n₁| * |beta n₂| *
            (if n₂ ∈ exc n₁ then Mb else R)
          ≤ ∑ n₂ ∈ In, ((if n₂ ∈ exc n₁ then |beta n₁| * |beta n₂| * Mb else 0)
              + |beta n₁| * |beta n₂| * R) := by
        refine Finset.sum_le_sum ?_
        intro n₂ _
        by_cases hmem : n₂ ∈ exc n₁
        · simp only [hmem, if_true]
          have := mul_nonneg (mul_nonneg (abs_nonneg (beta n₁)) (abs_nonneg (beta n₂))) hR0
          linarith
        · simp only [hmem, if_false]
          linarith
      refine le_trans hrw ?_
      rw [Finset.sum_add_distrib]
      have hfirst : ∑ n₂ ∈ In, (if n₂ ∈ exc n₁ then |beta n₁| * |beta n₂| * Mb else 0)
          = (∑ n₂ ∈ exc n₁, |beta n₁| * |beta n₂|) * Mb := by
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hsub n₁), Finset.sum_mul]
      rw [hfirst, Finset.sum_mul, Finset.sum_mul]
    have hle3 : ∑ n₁ ∈ In, ∑ n₂ ∈ In, |beta n₁| * |beta n₂| *
          (if n₂ ∈ exc n₁ then Mb else R)
        ≤ (∑ n₁ ∈ In, ∑ n₂ ∈ exc n₁, |beta n₁| * |beta n₂|) * Mb
          + (∑ n₁ ∈ In, ∑ n₂ ∈ In, |beta n₁| * |beta n₂|) * R := by
      have := Finset.sum_le_sum hle2
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul] at this
      exact this
    -- the exceptional part
    have hexc := exceptional_double_sum_le In exc beta s hsub hcard hsymm
    -- the generic part: `(∑|β|)² ≤ |In| ∑ β²`
    have hgen : (∑ n₁ ∈ In, ∑ n₂ ∈ In, |beta n₁| * |beta n₂|)
        ≤ (In.card : ℝ) * ∑ n ∈ In, beta n ^ 2 := by
      have hsq : (∑ n ∈ In, |beta n|) ^ 2 ≤ (In.card : ℝ) * ∑ n ∈ In, beta n ^ 2 := by
        have := Finset.sum_mul_sq_le_sq_mul_sq In (fun _ => (1 : ℝ)) (fun n => |beta n|)
        simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] at this
        simpa using this
      have hfact : ∑ n₁ ∈ In, ∑ n₂ ∈ In, |beta n₁| * |beta n₂|
          = (∑ n ∈ In, |beta n|) ^ 2 := by
        rw [sq, Finset.sum_mul_sum]
      rw [hfact]; exact hsq
    have hbeta0 : 0 ≤ ∑ n ∈ In, beta n ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    calc ∑ n₁ ∈ In, ∑ n₂ ∈ In, (beta n₁ * beta n₂) * (∑ m ∈ Im, K m n₁ * K m n₂)
        ≤ (∑ n₁ ∈ In, ∑ n₂ ∈ exc n₁, |beta n₁| * |beta n₂|) * Mb
          + (∑ n₁ ∈ In, ∑ n₂ ∈ In, |beta n₁| * |beta n₂|) * R := le_trans hle1 hle3
      _ ≤ (s * ∑ n ∈ In, beta n ^ 2) * Mb
          + ((In.card : ℝ) * ∑ n ∈ In, beta n ^ 2) * R := by
            have h1 := mul_le_mul_of_nonneg_right hexc hMb0
            have h2 := mul_le_mul_of_nonneg_right hgen hR0
            linarith
      _ = (∑ n ∈ In, beta n ^ 2) * (s * Mb + R * In.card) := by ring
  have halpha0 : 0 ≤ ∑ m ∈ Im, alpha m ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc (∑ m ∈ Im, ∑ n ∈ In, alpha m * beta n * K m n) ^ 2
      = (∑ m ∈ Im, alpha m * g m) ^ 2 := by rw [hform]
    _ ≤ (∑ m ∈ Im, alpha m ^ 2) * (∑ m ∈ Im, g m ^ 2) := hCS
    _ ≤ (∑ m ∈ Im, alpha m ^ 2)
          * ((∑ n ∈ In, beta n ^ 2) * (s * Mb + R * In.card)) :=
        mul_le_mul_of_nonneg_left hbound halpha0
    _ = (∑ m ∈ Im, alpha m ^ 2) * (∑ n ∈ In, beta n ^ 2)
          * (s * Mb + R * In.card) := by ring

end Kummer
end Erdos287
