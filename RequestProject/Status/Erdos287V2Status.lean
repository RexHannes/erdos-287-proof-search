import RequestProject.Erdos287.V2SophieBand
import RequestProject.Erdos287.V2BandSupplyChecks
import RequestProject.Erdos287.SophieBandCompiler

/-!
# Status ledger — Erdős #287 V1 (Sophie) and V2 (finite/top-layer) routes

This file records the audit status of the two Sophie routes and prints the axiom
dependencies of every new theorem.  It adds no mathematics.

## Controlling banked inputs of the V2 route

* `Erdos287.topLayer_congruence` — `RequestProject/Erdos287/TopLayer.lean`,
  namespace `Erdos287`; hypothesis shape
  `(A : Finset ℕ) (p : ℕ) (hp : p.Prime) (hpos : ∀ a ∈ A, 0 < a)`
  `(hsum : ∑ a ∈ A, (1:ℚ)/a = 1) (he : 1 ≤ topExp A p)`,
  conclusion `(∑ a ∈ topLayer A p, ((ordCompl[p] a : ℕ) : ZMod p)⁻¹) = 0`.
  Types: `Finset ℕ`, valuation `topExp A p = A.sup (fun a => Nat.factorization a p)`,
  layer `topLayer A p = A.filter (fun a => Nat.factorization a p = topExp A p)`,
  cofactors `ordCompl[p] a`.  No nonemptiness hypothesis (it follows from `1 ≤ topExp`),
  no coprimality hypothesis (it is automatic for `ordCompl`), and the theorem is stated for
  a general layer — the singleton/pair/triple versions
  `Erdos287.topLayer_card_ne_one`, `Erdos287.topLayer_two_obstruction`,
  `Erdos287.topLayer_three_obstruction` are separate corollaries in the same file.

* `Erdos287.Gap2CE.holes_isolated` — `RequestProject/Erdos287/Counterexample.lean`,
  namespace `Erdos287.Gap2CE`; shape
  `∀ n : ℕ, ce.N ≤ n → n + 1 ≤ ce.M → (n ∈ ce.A ∨ n + 1 ∈ ce.A)`,
  with `ce.N = ce.A.min' ce.hne`, `ce.M = ce.A.max' ce.hne`, and "hole at `x`" meaning
  `x ∉ ce.A`.  Endpoints are the closed window `[N, M]`.

## NOT controlling dependencies of the V2 route

* the analytic placement inequality `Erdos287.Gap2CE.exp_lower` (`e·(N-1) < M`, with `e`
  literally `Real.exp 1`) and the derived `Erdos287.Gap2CE.N_le_of_M_lt_two_mul`;
* the numerator threshold `Erdos287.C` and the value `Erdos287.C_two` (`C 2 = 3`), and with
  them `Erdos287.primePower_window_exclusion` / `Erdos287.ExcludedPP`.

These remain in the bank, untouched, as historical and (for the V2 route) redundant lemmas;
the V1 files `Erdos287/SophieOptimal.lean` and `Erdos287/SophieBandCompiler.lean` still use
them.  The V2 files use neither.
-/

namespace RequestProject.Status.Erdos287V2

open Erdos287

/-! ## Axiom inspection — V2 route -/

#print axioms Erdos287.topExp_le_one_of_lt_sq
#print axioms Erdos287.topHalf_prime_hole
#print axioms Erdos287.q_and_two_mul_q_holes
#print axioms Erdos287.Gap2CE.halfRange_min_le
#print axioms Erdos287.Gap2CE.holes_q_two_q
#print axioms Erdos287.Gap2CE.hole_topHalf_prime
#print axioms Erdos287.Gap2CE.v2_plus_sophie_blocker
#print axioms Erdos287.Gap2CE.v2_minus_sophie_blocker
#print axioms Erdos287.v2Band_hypotheses
#print axioms Erdos287.Gap2CE.v2_band_plus_blocker
#print axioms Erdos287.Gap2CE.v2_band_minus_blocker
#print axioms Erdos287.Gap2CE.v2_finite_compiler
#print axioms Erdos287.no_Gap2CE_M_eq_104
#print axioms Erdos287.Gap2CE.v2_exact_compiler
#print axioms Erdos287.no_Gap2CE_of_sophieWitness
#print axioms Erdos287.sophieWitness_sweep
#print axioms Erdos287.no_Gap2CE_of_M_in_39_250
#print axioms Erdos287.not_sophieWitness_35
#print axioms Erdos287.v2Band_supply_gap_152

/-! ## Axiom inspection — V1 (C-threshold / analytic-placement) route, kept for the record -/

#print axioms Erdos287.excludedPP_of_window_two
#print axioms Erdos287.window_ge_two_of_two_mul_le
#print axioms Erdos287.Gap2CE.N_le_of_M_lt_two_mul
#print axioms Erdos287.Gap2CE.plus_sophie_blocker
#print axioms Erdos287.Gap2CE.minus_sophie_blocker
#print axioms Erdos287.band_hypotheses
#print axioms Erdos287.Gap2CE.band_plus_blocker
#print axioms Erdos287.Gap2CE.band_minus_blocker
#print axioms Erdos287.no_Gap2CE_of_sophieBandSupply

end RequestProject.Status.Erdos287V2
