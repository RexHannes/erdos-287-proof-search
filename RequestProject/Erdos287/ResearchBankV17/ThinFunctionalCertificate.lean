import RequestProject.Erdos287.ResearchBankV16.RouteCParameters
import RequestProject.Erdos287.ResearchBankV17.CorrectedLogP

/-!
# Erdős #287 — Research Bank V17 §2: the corrected thin functional certificate

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The corrected strict bounds of the hostile repair enter as **certified data** (EXTERNAL PROVIDER
class: the functional integrals are not formalized).  The audited numbers were not supplied to
this run, so the bounds are parameters `μ_lo`, `W_hi`, `err` and the rational margin check
`ThinMarginCheck` is a decidable `ℚ` inequality.

Kept strictly separate:
* `ThinFunctionalCertificate` — functional constants `μ_F`, `W_F` only;
* `ThinArithmeticMoments` — the actual arithmetic moments `S0, S1, N` (a different structure).

Kernel-proved (LEAN BANK):
* `thin_margin_pos` — certificate + exact check ⟹ `μ_F − (A_C W_F + 90 + err)/99 − 350 > 0`;
* `certificate_does_not_give_moments` — a certificate instance coexists with arithmetic moments
  violating the zeroth-moment contract: S0/S1 are NOT inferred from the functional certificate.
-/

namespace Erdos287
namespace ResearchBankV17
namespace ThinFunctional

open ResearchBankV16.RouteCParameters

/-- **The corrected thin functional certificate** (certified input, never constructed). -/
structure ThinFunctionalCertificate (muLo WHi : ℚ) (muF WF : ℝ) : Prop where
  muF_gt : ((muLo : ℚ) : ℝ) < muF
  WF_lt : WF < ((WHi : ℚ) : ℝ)
  WF_nonneg : 0 ≤ WF

/-- The exact rational thin margin check. -/
def ThinMarginCheck (muLo WHi err : ℚ) : Prop := RouteCMarginCheck muLo WHi err

/-- **The actual arithmetic moments** (a separate structure: no functional constant here). -/
structure ThinArithmeticMoments where
  S0 : ℕ → ℝ
  S1 : ℕ → ℝ
  N : ℕ → ℝ

/-- The thin certificate yields the Route-C certificate shape (same functional fields). -/
theorem toRouteC {muLo WHi : ℚ} {muF WF : ℝ} (C : ThinFunctionalCertificate muLo WHi muF WF) :
    RouteCFunctionalCertificate muLo WHi muF WF := ⟨C.muF_gt, C.WF_lt, C.WF_nonneg⟩

/-- **Positive thin margin** from the certificate and the exact check. -/
theorem thin_margin_pos {muLo WHi err : ℚ} {muF WF : ℝ}
    (C : ThinFunctionalCertificate muLo WHi muF WF) (h : ThinMarginCheck muLo WHi err) :
    0 < muF - (((A_C : ℚ) : ℝ) * WF + 90 + ((err : ℚ) : ℝ)) / 99 - 350 :=
  routeC_margin_pos (toRouteC C) h

/-- **The certificate does not construct the arithmetic moments.** -/
theorem certificate_does_not_give_moments :
    ThinFunctionalCertificate 0 1 1 0 ∧
      ∃ m : ThinArithmeticMoments,
        ¬ ∀ η > (0 : ℝ), ∃ M₀ : ℕ, ∀ M ≥ M₀, 0 < m.N M ∧ |m.S0 M / m.N M - 1| ≤ η := by
  refine ⟨⟨by norm_num, by norm_num, le_rfl⟩, ⟨fun _ => 0, fun _ => 0, fun _ => 1⟩, fun h => ?_⟩
  obtain ⟨M₀, hM⟩ := h (1 / 2) (by norm_num)
  have := (hM M₀ le_rfl).2
  norm_num at this

end ThinFunctional
end ResearchBankV17
end Erdos287
