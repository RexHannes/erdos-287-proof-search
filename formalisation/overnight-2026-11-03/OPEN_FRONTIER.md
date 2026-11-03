# OPEN_FRONTIER — overnight 2026-11-03 (erdos287 Gold 4.1 local frontier)

## Build / audit artifacts
- New-module build log: `formalisation/overnight-2026-11-03/results/gold41_build.log`
- New-module axiom/type audit: `formalisation/overnight-2026-11-03/results/gold41_axioms.log`
- Baseline build status record: `formalisation/overnight-2026-11-03/results/baseline_lake_build_status.txt`

## Principal claims status ledger

### KERNEL PROVED
1. `Erdos287.Gold41.upperHalfPrime_not_mem`
   - Type (from audit):
     - `∀ (S : Erdos287.Gold41.SelectedSet) {p : Nat}, Nat.Prime p → S.M < 2 * p → p < S.M → p ∉ S.A`
2. `Erdos287.Gold41.upperHalfPrime_natIndicator_zero`
   - Type:
     - `∀ (S : Erdos287.Gold41.SelectedSet) {p : Nat}, Nat.Prime p → S.M < 2 * p → p < S.M → natIndicator S.A p = 0`
3. `Erdos287.Gold41.Gap2CE.upperHalfPrime_not_mem`
   - Type:
     - `∀ (ce : Erdos287.Gap2CE) {p : Nat}, Nat.Prime p → ce.M < 2 * p → p ≤ ce.M → p ∉ ce.A`
4. `Erdos287.Gold41.Gap2CE.forced_neighbors_of_upperHalfPrime`
   - Type:
     - `∀ (ce : Erdos287.Gap2CE) {p : Nat}, Nat.Prime p → ce.N + 1 ≤ p → p + 1 ≤ ce.M → ce.M < 2 * p → (p - 1 ∈ ce.A ∧ p + 1 ∈ ce.A)`
5. `Erdos287.Gold41.Gap2CE.forced_neighbors_natIndicator`
   - Type:
     - `∀ (ce : Erdos287.Gap2CE) {p : Nat}, Nat.Prime p → ce.N + 1 ≤ p → p + 1 ≤ ce.M → ce.M < 2 * p → (natIndicator ce.A (p - 1) = 1 ∧ natIndicator ce.A (p + 1) = 1)`

### CONDITIONAL ON NAMED HYPOTHESES
- None added in this run.

### NOT FORMALIZED
1. Four-value retained-cofactor lemma target
   - Requested form involves congruence
     - `6*q*r*S_q ≡ 3 + 6*x_{qr} + 2*x_{3qr} (mod r)`
     - and retained valuation conclusion `v_r(b_q)=1`.
   - Exact manuscript-side size/primality/localization hypotheses needed to make this statement precise in current Lean source were not fully specified in available repository inputs (`INPUT_INVENTORY.md` explicitly flags this gap).
2. Cleaning obstruction / final reduced q-row denominator exclusion claim
   - Full formal statement depends on a precise retained-residue compatibility interface that is not completely specified by available source files.
3. Global Chen alternative formalization
   - Analytic ingredients (published Chen-prime supply and uniform balanced-semiprime sieve bound) remain external in this run; no new conditional theorem was added here.

### FALSE / REQUIRES REPAIR
- No new false claim was introduced in this run.

## Notes on scope
- This run adds only fully local finite definitions/results under `RequestProject/Erdos287/Gold41` and does not claim closure of Erdős #287.
- Missing legacy manuscripts/files listed in `INPUT_INVENTORY.md` were not fabricated.
