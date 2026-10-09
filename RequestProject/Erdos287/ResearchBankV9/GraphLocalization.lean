import RequestProject.Erdos287.Blocker
import RequestProject.Erdos287.ProblemStatement
import RequestProject.Erdos287.ResearchBankV9.AffineContact

/-!
# Erdős #287 — Research Bank V9 §3F: graph localization ⟹ no #287 representation

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The deterministic implication

  useful graph edge + both endpoint affine forms prime + bounded-cofactor rigidity
  + physical contact `z, z+1 ∈ [cM, M]` + `c > 1/e`
  ⟹ no #287 counterexample with maximum `M`,

kernel-proved with its four ingredients kept separate:

1. **exact adjacent-contact arithmetic** — `AffineContact.contact_locations`;
2. **bounded-cofactor row rigidity** — the project's `ExcludedPP` (window exclusion
   `p > C(⌊M/p⌋)`, from `primePower_window_exclusion`);
3. **no-`00` / gap `≤ 2`** — `Gap2CE.excludedPP_blockerPair` (from `holes_isolated`);
4. **harmonic-tail estimate** — `Gap2CE.exp_lower` (`e(N − 1) < M`), used in
   `contact_above_N`: `z ≥ cM` with `c > 1/e` forces `z ≥ N`.

Any asymptotic prime supply producing such edges is external and is not used here.
-/

namespace Erdos287
namespace ResearchBankV9
namespace GraphLocalization

open AffineContact

/-- **Harmonic-tail localization.**  In a gap-`≤ 2` counterexample, any `z ≥ cM` with `c > 1/e`
lies above the minimum `N`. -/
theorem contact_above_N (ce : Gap2CE) {c : ℝ} (hc : 1 / Real.exp 1 < c) {z : ℕ}
    (hz : c * ce.M ≤ z) : ce.N ≤ z := by
  have hlow := ce.exp_lower
  have he := Real.exp_pos 1
  have hM : (0 : ℝ) ≤ ce.M := by positivity
  have h1 : ((ce.N : ℝ) - 1) < ce.M / Real.exp 1 := by
    rw [lt_div_iff₀ he]; linarith
  have h2 : (ce.M : ℝ) / Real.exp 1 ≤ c * ce.M := by
    rw [div_eq_mul_inv, mul_comm]
    have : (Real.exp 1)⁻¹ ≤ c := by rw [← one_div]; exact hc.le
    exact mul_le_mul_of_nonneg_right this hM
  have : (ce.N : ℝ) < z + 1 := by linarith
  exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)

/-- **Contact contradiction (abstract form).**  Two excluded prime powers dividing a physical
contact `z, z+1` with `cM ≤ z`, `z + 1 ≤ M`, `c > 1/e` refute every gap-`≤ 2` counterexample
with maximum `M`. -/
theorem contact_contradiction (ce : Gap2CE) {c : ℝ} (hc : 1 / Real.exp 1 < c) {z q₁ q₂ : ℕ}
    (hz : c * ce.M ≤ z) (hz1 : z + 1 ≤ ce.M) (hq₁ : ExcludedPP ce.M q₁)
    (hq₂ : ExcludedPP ce.M q₂) (hd₁ : q₁ ∣ z) (hd₂ : q₂ ∣ z + 1) : False :=
  ce.excludedPP_blockerPair (contact_above_N ce hc hz) hz1 hq₁ hq₂ hd₁ hd₂

/-- Bounded-cofactor rigidity of a prime `P` at scale `M`: `C(⌊M/P⌋) < P`. -/
def Rigid (M P : ℕ) : Prop := P.Prime ∧ C (M / P) < (P : ℤ)

theorem Rigid.excluded {M P : ℕ} (h : Rigid M P) : ExcludedPP M P :=
  ⟨P, 1, h.1, le_rfl, (pow_one P).symm, by simpa using h.2⟩

/-- The data of a useful graph edge localized at scale `M` with constant `c`. -/
structure UsefulEdgeData (M : ℕ) (c : ℝ) where
  /-- Smaller slope. -/
  ai : ℕ
  /-- Larger slope. -/
  aj : ℕ
  /-- The common parameter. -/
  t : ℕ
  /-- Ordered slopes. -/
  hij : ai < aj
  /-- gcd-clique edge condition `gcd(a_i, a_j) = a_j − a_i`. -/
  hg : Nat.gcd ai aj = aj - ai
  /-- `F_i(t)` is prime with bounded-cofactor rigidity. -/
  rigid_i : Rigid M (F ai t)
  /-- `F_j(t)` is prime with bounded-cofactor rigidity. -/
  rigid_j : Rigid M (F aj t)
  /-- Physical contact lower localization `cM ≤ z`. -/
  lower : c * M ≤ ((ai / (aj - ai)) * F aj t : ℕ)
  /-- Physical contact upper localization `z + 1 ≤ M`. -/
  upper : (ai / (aj - ai)) * F aj t + 1 ≤ M

/-- **Graph localization ⟹ contradiction** for gap-`≤ 2` counterexamples. -/
theorem no_gap2CE_of_usefulEdge (ce : Gap2CE) {c : ℝ} (hc : 1 / Real.exp 1 < c)
    (d : UsefulEdgeData ce.M c) : False := by
  obtain ⟨hz1, -, -⟩ := contact_locations d.hij d.hg d.t
  refine contact_contradiction ce hc d.lower d.upper d.rigid_j.excluded d.rigid_i.excluded
    (dvd_mul_left _ _) ?_
  rw [hz1]; exact dvd_mul_left _ _

/-- **No #287 representation with maximum `M`** (exact problem predicate). -/
theorem no_erdos287Counterexample_of_usefulEdge {A : Finset ℕ} (h : Erdos287Counterexample A)
    {c : ℝ} (hc : 1 / Real.exp 1 < c) (d : UsefulEdgeData (A.max' h.nonempty) c) : False :=
  no_gap2CE_of_usefulEdge h.toGap2CE hc d

/-- Conditional form: if every scale `M ≥ M₀` carries a useful localized edge, no counterexample
has maximum `≥ M₀`.  (The supply of edges is a hypothesis, never inhabited here.) -/
theorem no_counterexample_above_of_edge_supply {c : ℝ} (hc : 1 / Real.exp 1 < c) {M₀ : ℕ}
    (hsupply : ∀ M ≥ M₀, Nonempty (UsefulEdgeData M c)) {A : Finset ℕ}
    (h : Erdos287Counterexample A) (hM : M₀ ≤ A.max' h.nonempty) : False :=
  no_erdos287Counterexample_of_usefulEdge h hc (hsupply _ hM).some

end GraphLocalization
end ResearchBankV9
end Erdos287
