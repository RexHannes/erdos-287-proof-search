import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V21 §6: the mod-11 spectator-square counterfixture

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

RETIRED inference (V17 style): "spectator-square weighting leaves the local sieve density of
`L_j` equal to `1/(p-1)`".

Fixture (FINITE REGRESSION, kernel-checked by `decide`): `p = 11`,

    L_i(t) = t + 1,   L_j(t) = 2t + 1,   L_k(t) = 3t + 1,

on the residues `t ∈ ZMod 11` with `L_i(t) ≠ 0`, with the spectator-square weight

    W(t) = (1 - ½ · 1_{L_k(t) = 0})².

* `raw_density` — the unweighted density of `L_j = 0` is `1/10 = 1/(p-1)`;
* `weighted_density` — the `W`-weighted density of `L_j = 0` is exactly `4/37`;
* **`spectator_square_density_not_invariant`** — `4/37 ≠ 1/10`: the weighting changes the
  density, so the V17 shortcut is false;
* `counterfixture_within_envelope` — consistent with the REPAIRED theory: `4/37 ≤ 1/9 =
  h(11) = 1/(p-r-1)` with `r = 1` spectator form.
-/

namespace Erdos287
namespace ResearchBankV21
namespace DensityCounterfixture

open Finset

/-- `L_i(t) = t + 1`. -/
def Li (t : ZMod 11) : ZMod 11 := t + 1
/-- `L_j(t) = 2t + 1`. -/
def Lj (t : ZMod 11) : ZMod 11 := 2 * t + 1
/-- `L_k(t) = 3t + 1` (the spectator form). -/
def Lk (t : ZMod 11) : ZMod 11 := 3 * t + 1

/-- The spectator-square weight `W(t) = (1 - ½ 1_{L_k = 0})²`. -/
def W (t : ZMod 11) : ℚ := (1 - (1 / 2) * (if Lk t = 0 then 1 else 0)) ^ 2

/-- The residues with `L_i ≠ 0`. -/
def support : Finset (ZMod 11) := univ.filter fun t => Li t ≠ 0

/-- `W`-weighted density of `L_j = 0`. -/
def weightedDensity : ℚ :=
  (∑ t ∈ support, W t * (if Lj t = 0 then 1 else 0)) / ∑ t ∈ support, W t

/-- Unweighted density of `L_j = 0`. -/
def rawDensity : ℚ :=
  (∑ t ∈ support, (if Lj t = 0 then (1 : ℚ) else 0)) / (support.card : ℚ)

theorem support_eq : support = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide

theorem raw_density : rawDensity = 1 / 10 := by
  rw [rawDensity, support_eq]
  simp (config := { decide := true }) [Finset.filter_insert, Finset.filter_singleton, Lj]

theorem weighted_density : weightedDensity = 4 / 37 := by
  rw [weightedDensity, support_eq]
  simp (config := { decide := true }) [Lj, W, Lk]
  norm_num

/-- **RETIRED V17 shortcut**: spectator-square weighting does NOT preserve the density
`1/(p-1)`. -/
theorem spectator_square_density_not_invariant :
    weightedDensity = 4 / 37 ∧ rawDensity = 1 / (11 - 1) ∧ (4 / 37 : ℚ) ≠ 1 / 10 ∧
      weightedDensity ≠ rawDensity := by
  refine ⟨weighted_density, by rw [raw_density]; norm_num, by norm_num, ?_⟩
  rw [weighted_density, raw_density]; norm_num

/-- The repaired envelope `h(11) = 1/(11 - 1 - 1) = 1/9` does dominate the weighted density. -/
theorem counterfixture_within_envelope : weightedDensity ≤ 1 / (11 - 1 - 1) := by
  rw [weighted_density]; norm_num

end DensityCounterfixture
end ResearchBankV21
end Erdos287
