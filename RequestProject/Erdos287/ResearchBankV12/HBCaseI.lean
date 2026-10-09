import RequestProject.Erdos287.ResearchBankV12.HBSelectionConcrete

/-!
# Erdős #287 — Research Bank V12 §11: Case I — concrete Type-I support routing

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Case I: `μ ≥ 4/13`.  Put

* `sI = μ − 3θ − ζ`,  `rI = λ − μ + 3θ + ζ`  (so `sI + rI = λ`).

Actual Type-I boxes: `0 ≤ θ ≤ θ₀`, `0 ≤ s ≤ sI`, `0 ≤ r ≤ rI`.

Routing (`caseIRoute`):
* if `rI < 0` → rapid-decay branch (and then no box with `r ≥ 0` is legal: `rI_neg_no_box`);
* else if the actual `r < θ` → rapid-decay branch, with the declared margin
  `μ − θ − r − s ≥ ζ` (`rapidDecay_declared_margin`);
* otherwise → frozen Type-I domain, where the following domain facts are proved
  (`typeI_domain_facts`):
  1. reserve `μ − 3θ − s ≥ ζ`;
  2. level `r + s ≤ λ`;
  3. `θ ≤ r` (the modulus is not in the rapid-decay range);
  4. smooth side `sI ≥ 4/13 − 3θ₀ − ζ > 0`;
  5. modulus side `r ≤ rI ≤ λ − 4/13 + 3θ₀ + ζ < 1/4`.

**Scope.**  The reserve (item 1) and the rapid-decay margin `μ − θ − r − s ≥ ζ` were supplied
verbatim and are proved.  The five margins of the frozen Type-I theorem were **not printed** in the
supplied material, and the frozen Type-I bank (V10 `SmoothTypeIInput`) contains no explicit domain
predicate for them; they are therefore **not reconstructed from the supplied source**.  Items 2–5
are only the natural geometric facts that follow from the supplied definitions; they are **not**
claimed to be the frozen theorem's literal hypotheses.  No Type-I spectral mathematics is
reproved.
-/

namespace Erdos287
namespace ResearchBankV12
namespace HBCaseI

open ConcreteParameters

/-- `sI = μ − 3θ − ζ`. -/
def sI (μ θ : ℚ) : ℚ := μ - 3 * θ - zeta

/-- `rI = λ − μ + 3θ + ζ`. -/
def rI (μ θ : ℚ) : ℚ := lam - μ + 3 * θ + zeta

theorem sI_add_rI (μ θ : ℚ) : sI μ θ + rI μ θ = lam := by unfold sI rI; ring

/-- Case-I routes. -/
inductive TypeIRoute
  | rapidDecay
  | typeIDomain
  deriving DecidableEq, Repr

/-- The Case-I routing rule. -/
def caseIRoute (μ θ r : ℚ) : TypeIRoute :=
  if rI μ θ < 0 ∨ r < θ then .rapidDecay else .typeIDomain

/-- An actual Case-I box. -/
structure CaseIBox (μ θ r s : ℚ) : Prop where
  μ_ge : 4 / 13 ≤ μ
  θ_nonneg : 0 ≤ θ
  θ_le : θ ≤ theta0
  r_nonneg : 0 ≤ r
  r_le : r ≤ rI μ θ
  s_nonneg : 0 ≤ s
  s_le : s ≤ sI μ θ

/-- If `rI < 0` there is no legal box (so the rapid-decay route is the only one). -/
theorem rI_neg_no_box {μ θ r s : ℚ} (h : rI μ θ < 0) : ¬ CaseIBox μ θ r s := fun hb => by
  have := hb.r_nonneg; have := hb.r_le; linarith

/-- `rI < 0` exactly when `μ > λ + 3θ + ζ`. -/
theorem rI_neg_iff (μ θ : ℚ) : rI μ θ < 0 ↔ lam + 3 * θ + zeta < μ := by
  unfold rI; constructor <;> intro h <;> linarith

/-- The rapid-decay margin in the `r < θ` branch (trivial form). -/
theorem rapidDecay_margin {θ r : ℚ} (h : r < θ) : 0 < θ - r := by linarith

/-- **The declared rapid-decay margin** `μ − θ − r − s ≥ ζ` on every actual Case-I box with
`r < θ` (in fact `μ − θ − r − s > θ + ζ ≥ ζ`). -/
theorem rapidDecay_declared_margin {μ θ r s : ℚ} (hb : CaseIBox μ θ r s) (h : r < θ) :
    zeta ≤ μ - θ - r - s := by
  have h1 := hb.s_le; have h2 := hb.θ_nonneg
  unfold sI at h1; linarith

/-- **The Type-I domain facts** in the non-rapid-decay branch. -/
theorem typeI_domain_facts {μ θ r s : ℚ} (hb : CaseIBox μ θ r s) (hθr : θ ≤ r) :
    zeta ≤ μ - 3 * θ - s ∧ r + s ≤ lam ∧ θ ≤ r ∧
      4 / 13 - 3 * theta0 - zeta ≤ sI μ θ ∧ 0 < 4 / 13 - 3 * theta0 - zeta ∧
      r ≤ lam - 4 / 13 + 3 * theta0 + zeta ∧ lam - 4 / 13 + 3 * theta0 + zeta < 1 / 4 := by
  have h1 := hb.s_le; have h2 := hb.r_le; have h3 := hb.μ_ge; have h4 := hb.θ_le
  have h5 := hb.θ_nonneg
  have hz := zeta_eq; have ht := theta0_lt; have ht0 := theta0_pos; have hl := lam_eq
  unfold sI at *; unfold rI at *
  refine ⟨by linarith, by linarith, hθr, by linarith, by rw [hz]; linarith, by linarith, ?_⟩
  rw [hl, hz]; linarith

/-- **Reserve** `μ − 3θ − s ≥ ζ` holds on every actual Case-I box. -/
theorem reserve (μ θ r s : ℚ) (hb : CaseIBox μ θ r s) : zeta ≤ μ - 3 * θ - s := by
  have := hb.s_le; unfold sI at this; linarith

/-- **Case-I routing is complete**: every actual Case-I box lands either in the rapid-decay
branch (with `rI < 0` or margin `θ − r > 0`) or in the Type-I domain with all domain facts. -/
theorem caseI_routed {μ θ r s : ℚ} (hb : CaseIBox μ θ r s) :
    (caseIRoute μ θ r = .rapidDecay ∧ 0 < θ - r ∧ zeta ≤ μ - θ - r - s) ∨
    (caseIRoute μ θ r = .typeIDomain ∧ zeta ≤ μ - 3 * θ - s ∧ r + s ≤ lam ∧ θ ≤ r) := by
  unfold caseIRoute
  by_cases hr : r < θ
  · exact Or.inl ⟨by simp [hr], by linarith, rapidDecay_declared_margin hb hr⟩
  · have hrI : ¬ rI μ θ < 0 := fun h => rI_neg_no_box h hb
    right
    have hθr : θ ≤ r := not_lt.1 hr
    obtain ⟨a, b, c, -⟩ := typeI_domain_facts hb hθr
    exact ⟨by simp [hrI, hr], a, b, c⟩

/-- Fixture: `μ = 1` (a single smooth factor) routes to rapid decay since `rI < 0`. -/
theorem mu_one_rapidDecay (θ r : ℚ) (hθ' : θ ≤ theta0) :
    caseIRoute 1 θ r = .rapidDecay := by
  have : rI 1 θ < 0 := by
    unfold rI; rw [lam_eq, zeta_eq]; have := theta0_lt; linarith
  simp [caseIRoute, this]

end HBCaseI
end ResearchBankV12
end Erdos287
