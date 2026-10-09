import RequestProject.Erdos287.PostV64V71.AnalyticFrontier
import RequestProject.Erdos287.PostV64V71.RoughPart
import RequestProject.Erdos287.PostV64V71.SourcePinned
import RequestProject.Erdos287.PostV64V71.ComponentFactorisation

/-!
# Erdős #287 — V67–V71 regression fixtures

**These fixtures verify exact algebra / finite combinatorics only.**  They do **not** establish
any prime-distribution statement, the major-arc asymptotic, a minor-arc bound, or all-`M`
closure.  Finite checks use `decide` / `decide +kernel` (kernel evaluation; no `native_decide`).
-/

open scoped BigOperators

namespace Erdos287.PostV64V71.Fixtures

open Erdos287 Erdos287.PostV64V71

/-! ## `Ξ_H` numerator fingerprint -/

/-- `S_3 = {0, 1, 1/2, 1/3, 3/2, 4/3, 5/6, 11/6}` has 8 distinct values. -/
theorem recipSums_three_card : (recipSums 3).card = 8 := by decide +kernel

/-- `Ξ_2 = 1 · 1 · 3 = 3`. -/
theorem Xi_two : Xi 2 = 3 := by decide +kernel

/-- `Ξ_3 = 1·1·1·3·4·5·11 = 660` (distinct nonzero values; reduced numerators). -/
theorem Xi_three : Xi 3 = 660 := by decide +kernel

/-- `B_3 = 6/1 + 6/2 + 6/3 = 11`. -/
theorem BH_three : BH 3 = 11 := by decide

/-- The integer size bank at `H = 3`: `660 ≤ 11^7`. -/
theorem Xi_three_size : Xi 3 ≤ BH 3 ^ ((recipSums 3).card - 1) := Xi_le_BH_pow 3

/-! ## Good-row emptiness (contrapositive use) -/

/-- `A = {2, 4, 6, 12}` has `∑ 1/a = 1` and contains the multiple `6` of `3`, with
`⌊12/3⌋ = 4`; hence, by `good_large_prime_row_empty`, `3 ∣ Ξ_4`. -/
theorem three_dvd_Xi_four : 3 ∣ Xi 4 := by
  by_contra h
  exact good_large_prime_row_empty {2, 4, 6, 12} 12 4 3 Nat.prime_three
    (by decide) (by decide) (by norm_num [Finset.sum_insert]) (by norm_num) h 6 (by decide)
    (by norm_num)

/-- Independent kernel check of the same divisibility. -/
theorem three_dvd_Xi_four' : 3 ∣ Xi 4 := by decide +kernel

/-! ## Determinant tuples and the subbox dictionary -/

/-- `(k, q, t, r, ε) = (2, 7, 1, 13, 1)`: `2·7 - 1·13 = 1`, `10 < 14 < 15`, so it lies in the
box for `M = 20`, `H = 4` (`y = 5`). -/
theorem tuple_mem_box : ((2, 7, 1, 13, 1) : DTup) ∈ detBox 20 4 := by
  rw [mem_detBox]; norm_num

/-- `det [[2, 1], [13, 7]] = 2·7 - 1·13 = 1`. -/
theorem tuple_det : Matrix.det !![(2 : ℤ), 1; 13, 7] = 1 := by
  rw [det_eq]; norm_num

/-- The subbox dictionary sends `(n, m, k, t) = (14, 13, 2, 1)` to `(2, 7, 1, 13, 1)`. -/
theorem quad_fixture : quadToTup ((14, 13), (2, 1)) = ((2, 7, 1, 13, 1) : DTup) := by
  simp [quadToTup]

theorem quad_fixture_mem : quadToTup ((14, 13), (2, 1)) ∈ detBox 20 8 := by
  refine quadToTup_mem (K := 2) (by norm_num) ?_
  simp only [quadSet, Finset.mem_filter, Finset.mem_product, mem_Iset, Finset.mem_Icc, Adj]
  norm_num

/-- Rough factor ⟺ determinant tuple, on the fixture: `13 ∣ 2·7 - 1`. -/
theorem rough_fixture : (13 : ℤ) ∣ ((2 * 7 : ℕ) : ℤ) - 1 := ⟨1, by norm_num⟩

/-! ## Weighted accounting identities -/

/-- With no exceptions, nothing is deleted: `D_θ^{gg}(∅) = D_θ`. -/
theorem Dgg_empty (M H : ℕ) : Dgg M H ∅ = Dtheta M H := by
  unfold Dgg Dtheta Dw
  congr 1
  exact Finset.filter_true_of_mem fun x _ => ⟨Finset.notMem_empty _, Finset.notMem_empty _⟩

/-- Prime-power contamination fixture: `Λ(4) = log 2` but `θ*(4) = 0`. -/
theorem contamination_fixture : LambdaW 4 = Real.log 2 ∧ thetaStar 4 = 0 := by
  refine ⟨?_, thetaStar_of_not_prime (by decide)⟩
  unfold LambdaW
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- On primes the two weights agree: `Λ(13) = θ*(13)`. -/
theorem prime_weight_fixture : thetaStar 13 = LambdaW 13 := thetaStar_of_prime (by norm_num)

/-! ## Local admissibility / parity -/

/-- `2·1 - 1·1 = 1`; modulo `5 ∤ 2·1` there are exactly two forbidden residues. -/
theorem forbidden_count_five :
    (Finset.univ.filter (fun u : ZMod 5 =>
      (((1 : ℕ) : ZMod 5) * u + ((1 : ℤ) : ZMod 5)) *
        (((2 : ℕ) : ZMod 5) * u + ((1 : ℤ) : ZMod 5)) = 0)).card = 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [local_forbidden_residue_count 5 (k := 2) (t := 1) (a := 1) (b := 1) (ε := 1) (Or.inl rfl)
    (by norm_num)]
  decide

/-- Direct kernel cross-check of the same count. -/
theorem forbidden_count_five' :
    (Finset.univ.filter (fun u : ZMod 5 => (u + 1) * (2 * u + 1) = 0)).card = 2 := by decide

/-- Parity collapse: modulo `2 ∣ 2·1` there is exactly one forbidden residue. -/
theorem forbidden_count_two :
    (Finset.univ.filter (fun u : ZMod 2 =>
      (((1 : ℕ) : ZMod 2) * u + ((1 : ℤ) : ZMod 2)) *
        (((2 : ℕ) : ZMod 2) * u + ((1 : ℤ) : ZMod 2)) = 0)).card = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [local_forbidden_residue_count 2 (k := 2) (t := 1) (a := 1) (b := 1) (ε := 1) (Or.inl rfl)
    (by norm_num)]
  decide

/-- Admissibility of the fixture tuple `2·7 - 1·13 = 1`. -/
theorem admissible_fixture : Nat.Coprime 2 1 ∧ Odd (2 + 1) ∧ (7 : ℕ) ≠ 13 :=
  local_determinant_admissibility (k := 2) (t := 1) (q := 7) (r := 13) (ε := 1) (Or.inl rfl)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Local factor ratio at `ℓ = 3`: `(3-1)/(3-2) = 2`. -/
theorem local_ratio_three : localDensity 1 3 / localDensity 2 3 = 2 := by
  rw [local_factor_ratio (by norm_num)]; norm_num

/-! ## V67 pinned identity, component factorisation -/

/-- The repair fixture for the literal `D ∣ X(E)` reading. -/
example : ∃ P D Y : ℕ, 0 < Y ∧ Y < 2 * D ∧ (D : ℤ) ∣ (P : ℤ) * ((D : ℤ) - Y) ∧ Y ≠ D :=
  pinned_D_dvd_counterfixture

/-- Immediate arithmetic death: a negative target has no independent solution. -/
example : compCount (fun n => n) {1, 3} (-1) = 0 := compCount_of_neg _ _ (by norm_num)

/-- `{1}` and `{3}` are separated, so `F_{{1,3}} = F_{{1}} · F_{{3}}`. -/
example : compPoly (fun n => n) ({1} ∪ {3}) = compPoly (fun n => n) {1} * compPoly (fun n => n) {3} :=
  compPoly_union _ ⟨by decide, by decide⟩

end Erdos287.PostV64V71.Fixtures
