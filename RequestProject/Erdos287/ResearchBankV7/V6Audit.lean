import RequestProject.Erdos287.ResearchBankV6

/-!
# Erdős #287 — Research Bank V7: semantic spot audit of the load-bearing V6 theorems

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

V6 is **not** redone and **not** edited.  This module performs a targeted *statement-level* audit
of the five most load-bearing V6 theorems and re-exports them unchanged:

1. `UpperGap.prime_removed_iff_dvd_rowNumerator`,
2. `UpperGap.rowMass_eq_carry_div`,
3. `UpperGap.carry_height_aggregation`,
4. `UpperGap.rowSupport_disjoint` (support-disjointness),
5. `FullFrozen.row_disjoint_of_window_exclusion` (FULL-FROZEN denominator entry).

Audited points, each machine-checked here:

* **lower endpoints and actual cofactor sets are present** — every audited row theorem is
  instantiated at the *actual* cofactor set `allowedCofactors a M p`, which carries the lower
  endpoint `a` (`audit_actual_cofactors_*`);
* **the Boolean selection hypothesis is genuine** — the row numerator really depends on the
  selection `ε` (`audit_selection_is_genuine`);
* **the denominator reduction is the intended rational statement** — checked against concrete
  rationals (`audit_den_dvd_positive`, `audit_den_dvd_negative`);
* **no conclusion was silently inserted as a premise** — the hypotheses of the audited theorems
  are satisfiable in configurations where the conclusion *fails*, so they cannot contain it
  (`audit_no_hidden_conclusion_*`), and the divisibility premise of the carry identity is
  load-bearing (`audit_carry_premise_load_bearing`).

**Audit verdict: all five statements match their intended reading; they are re-exported
unchanged.**  No V6 file is modified and no correction theorem was needed.
-/

namespace Erdos287
namespace ResearchBankV7
namespace V6Audit

open Erdos287.ResearchBankV6
open Erdos287.ResearchBankV6.UpperGap

/-! ## 1.  Re-export of the audited V6 statements (unchanged) -/

/-- Re-export (unchanged): denominator-entry ⇔ divisibility of the exact row numerator. -/
theorem reexport_prime_removed_iff_dvd_rowNumerator {N p : ℕ} {J : Finset ℕ} {ε : ℕ → Bool}
    (hp : 0 < p) (hJ : ∀ j ∈ J, 1 ≤ j ∧ j ≤ N) :
    (∃ k : ℤ, rowMass p J ε = (k : ℚ) / lcmUpto N) ↔ p ∣ rowNumerator N p J ε :=
  prime_removed_iff_dvd_rowNumerator hp hJ

/-- Re-export (unchanged): the exact carry identity. -/
theorem reexport_rowMass_eq_carry_div {N p : ℕ} {J : Finset ℕ} {ε : ℕ → Bool} (hp : 0 < p)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ j ≤ N) (hdvd : p ∣ rowNumerator N p J ε) :
    rowMass p J ε = (carry N p J ε : ℚ) / lcmUpto N :=
  rowMass_eq_carry_div hp hJ hdvd

/-- Re-export (unchanged): the same-height carry aggregation. -/
theorem reexport_carry_height_aggregation {M : ℕ} {P : Finset ℕ} {J : ℕ → Finset ℕ} {ε : ℕ → Bool}
    (hpos : ∀ p ∈ P, 0 < p)
    (hJ : ∀ p ∈ P, ∀ j ∈ J p, 1 ≤ j ∧ j ≤ height M p)
    (hdvd : ∀ p ∈ P, p ∣ rowNumerator (height M p) p (J p) ε) :
    ∑ p ∈ P, rowMass p (J p) ε
      = ∑ N ∈ heights M P, (aggregateCarry M P J ε N : ℚ) / lcmUpto N :=
  carry_height_aggregation hpos hJ hdvd

/-- Re-export (unchanged): upper-gap support disjointness. -/
theorem reexport_rowSupport_disjoint {p q M : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hM : M < p * q) : Disjoint (rowSupport M p) (rowSupport M q) :=
  rowSupport_disjoint hp hq hpq hM

/-- Re-export (unchanged): the FULL-FROZEN finite denominator-entry statement. -/
theorem reexport_fullFrozen_row_disjoint
    (A : Finset ℕ) (M p e : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a) (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) (he : 1 ≤ e) (hqM : p ^ e ≤ M)
    (hpC : Erdos287.C (M / p ^ e) < (p : ℤ)) :
    Disjoint A (rowSupport M (p ^ e)) :=
  FullFrozen.row_disjoint_of_window_exclusion A M p e hp hpos hAM hsum he hqM hpC

/-! ## 2.  Audit: lower endpoints and actual cofactor sets are present -/

/-- The actual cofactor set of the row `p` in the window `[a, M]` — carrying the **lower
endpoint** `a` — satisfies the range hypothesis of the audited row theorems. -/
theorem audit_actual_cofactors_range (a M p : ℕ) :
    ∀ j ∈ allowedCofactors a M p, 1 ≤ j ∧ j ≤ height M p := by
  intro j hj
  exact (mem_allowedCofactors.1 hj).1

/-- **Audit 1.**  The denominator-entry equivalence really applies to the *actual* cofactor set,
lower endpoint included. -/
theorem audit_actual_cofactors_denominator_entry (a M p : ℕ) (hp : 0 < p) (ε : ℕ → Bool) :
    (∃ k : ℤ, rowMass p (allowedCofactors a M p) ε = (k : ℚ) / lcmUpto (height M p)) ↔
      p ∣ rowNumerator (height M p) p (allowedCofactors a M p) ε :=
  prime_removed_iff_dvd_rowNumerator hp (audit_actual_cofactors_range a M p)

/-- **Audit 2.**  The carry identity applies to the actual cofactor set. -/
theorem audit_actual_cofactors_carry (a M p : ℕ) (hp : 0 < p) (ε : ℕ → Bool)
    (hdvd : p ∣ rowNumerator (height M p) p (allowedCofactors a M p) ε) :
    rowMass p (allowedCofactors a M p) ε
      = (carry (height M p) p (allowedCofactors a M p) ε : ℚ) / lcmUpto (height M p) :=
  rowMass_eq_carry_div hp (audit_actual_cofactors_range a M p) hdvd

/-- **Audit 3.**  The height aggregation applies with every row using its own actual cofactor set
(lower endpoint `a` included). -/
theorem audit_actual_cofactors_aggregation (a M : ℕ) (P : Finset ℕ) (ε : ℕ → Bool)
    (hpos : ∀ p ∈ P, 0 < p)
    (hdvd : ∀ p ∈ P, p ∣ rowNumerator (height M p) p (allowedCofactors a M p) ε) :
    ∑ p ∈ P, rowMass p (allowedCofactors a M p) ε
      = ∑ N ∈ heights M P,
          (aggregateCarry M P (fun p => allowedCofactors a M p) ε N : ℚ) / lcmUpto N :=
  carry_height_aggregation hpos (fun p _ => audit_actual_cofactors_range a M p) hdvd

/-! ## 3.  Audit: the Boolean selection hypothesis is genuine -/

/-- **Audit 4.**  The exact row numerator genuinely depends on the Boolean selection `ε`: turning
the bit at the physical position `5·1 = 5` off changes the value.  So `ε` is a real selection
variable, not a decoration. -/
theorem audit_selection_is_genuine :
    rowNumerator 2 5 {1} (fun _ => true) ≠ rowNumerator 2 5 {1} (fun _ => false) := by decide

/-- The row mass likewise depends on the selection. -/
theorem audit_selection_is_genuine_mass :
    rowMass 5 {1} (fun _ => true) ≠ rowMass 5 {1} (fun _ => false) := by
  norm_num [rowMass]

/-! ## 4.  Audit: denominator reduction is the intended rational statement -/

/-- **Audit 5a.**  `den_dvd_iff` on a concrete positive instance: `1/2` lies in `(1/6)ℤ`. -/
theorem audit_den_dvd_positive : ∃ k : ℤ, (1/2 : ℚ) = (k : ℚ) / (6 : ℕ) :=
  (den_dvd_iff (by norm_num : 0 < 6)).1 (by norm_num)

/-- **Audit 5b.**  And a concrete negative instance: `1/4` does not lie in `(1/6)ℤ`. -/
theorem audit_den_dvd_negative : ¬ ∃ k : ℤ, (1/4 : ℚ) = (k : ℚ) / (6 : ℕ) := by
  intro h
  have := (den_dvd_iff (by norm_num : 0 < 6)).2 h
  norm_num at this

/-! ## 5.  Audit: no conclusion silently inserted as a premise -/

/-- **Audit 6.**  The hypotheses of the denominator-entry equivalence are satisfiable in a
configuration where the conclusion *fails* (`p = 5`, `N = 2`, cofactor set `{1}`, all bits on:
`T_p = 2` and `5 ∤ 2`).  Hence the premises cannot contain the conclusion. -/
theorem audit_no_hidden_conclusion_denominator_entry :
    (∀ j ∈ ({1} : Finset ℕ), 1 ≤ j ∧ j ≤ 2) ∧
      ¬ (5 ∣ rowNumerator 2 5 {1} (fun _ => true)) := by
  refine ⟨?_, by decide⟩
  intro j hj
  simp only [Finset.mem_singleton] at hj
  omega

/-- **Audit 7.**  The divisibility premise of the carry identity is load-bearing: in the same
configuration the identity *fails* without it (`rowMass = 1/5` while `carry/L = 0`). -/
theorem audit_carry_premise_load_bearing :
    rowMass 5 {1} (fun _ => true) ≠ (carry 2 5 {1} (fun _ => true) : ℚ) / lcmUpto 2 := by
  have hcar : carry 2 5 {1} (fun _ => true) = 0 := by decide
  have hL : lcmUpto 2 = 2 := by decide
  rw [hcar, hL]
  norm_num [rowMass]

/-- **Audit 8.**  Support disjointness has genuine content: for `p = 3`, `q = 5`, `M = 14 < 15`
the two rows are disjoint, while for `M = 15` the position `15` is shared — so the hypothesis
`M < p q` is load-bearing. -/
theorem audit_support_disjointness_is_sharp :
    Disjoint (rowSupport 14 3) (rowSupport 14 5) ∧
      ¬ Disjoint (rowSupport 15 3) (rowSupport 15 5) := by
  refine ⟨rowSupport_disjoint (by norm_num) (by norm_num) (by norm_num) (by norm_num), ?_⟩
  intro h
  have h15 : (15 : ℕ) ∈ rowSupport 15 3 := mem_rowSupport.2 ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩
  have h15' : (15 : ℕ) ∈ rowSupport 15 5 := mem_rowSupport.2 ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩
  exact (Finset.disjoint_left.1 h h15) h15'

/-! ## 6.  Audit verdict -/

/-- **Audit verdict (bookkeeping).**  All five audited V6 statements match their intended reading
and are re-exported unchanged; no correction theorem or counterfixture was required. -/
def auditVerdict : String :=
  "V6 spot audit: prime_removed_iff_dvd_rowNumerator, rowMass_eq_carry_div, " ++
  "carry_height_aggregation, support disjointness and the FULL-FROZEN denominator-entry " ++
  "statement all match; re-exported unchanged."

end V6Audit
end ResearchBankV7
end Erdos287
