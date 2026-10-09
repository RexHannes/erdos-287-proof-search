import RequestProject.Erdos287.ResearchBankV26.HeathBrownIdentity

/-!
# Erdős #287 — Research Bank V26 §4.3 (cont.): singleton bins

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A Heath-Brown term with fewer than six variables is padded with the singleton sequence `{1}`
(the Dirichlet unit `δ₁ = 1`), which changes nothing.  No rough bin is required to contain a
value `> x^ν`: the singleton bin contains only `1`.

**LEAN BANK.**
* `singleton_apply` — `δ₁(n) = 1_{n = 1}`;
* `pad_singleton` — `F ⋆ δ₁^{⋆m} = F` for every `m`;
* `hb_term_six_variables` — every `k = 3` HB term equals a product of EXACTLY six factors after
  padding with singleton sequences;
* `singleton_bin_values` — the singleton bin's only nonzero value is at `n = 1`, so no lower
  bound `> x^ν` on bin values is available or needed.
-/

namespace Erdos287
namespace ResearchBankV26
namespace SingletonBins

open ArithmeticFunction HeathBrownIdentity

/-- The singleton sequence `{1}`: the Dirichlet unit. -/
noncomputable abbrev singletonSeq : ArithmeticFunction ℝ := 1

theorem singleton_apply (n : ℕ) : singletonSeq n = if n = 1 then 1 else 0 := one_apply

/-- **Padding with singleton sequences changes nothing.** -/
theorem pad_singleton (F : ArithmeticFunction ℝ) (m : ℕ) : F * singletonSeq ^ m = F := by
  simp [singletonSeq]

/-- **Every `k = 3` HB term is a product of exactly six factors** after padding
(`j+1` Möbius factors, `j` constant factors, one `log`, and `2 − j` singleton factors, `j < 3`). -/
theorem hb_term_six_variables (y : ℝ) (j : ℕ) (hj : j < 3) :
    hbTerm y j = My y ^ (j + 1) * zetaR ^ j * log * singletonSeq ^ (2 * (2 - j)) ∧
      (j + 1) + j + 1 + 2 * (2 - j) = 6 := by
  refine ⟨(pad_singleton _ _).symm, by omega⟩

/-- The singleton bin has a single nonzero value, at `n = 1`. -/
theorem singleton_bin_values (n : ℕ) (h : singletonSeq n ≠ 0) : n = 1 := by
  rw [singleton_apply] at h; by_contra hn; exact h (if_neg hn)

end SingletonBins
end ResearchBankV26
end Erdos287
