import RequestProject.Erdos287.ClosureInputs

/-!
# Erdős #287 — end-to-end status ledger and axiom audit

This file prints the axiom dependencies of every principal theorem added in the
end-to-end pass, and records — in Lean, not in prose — what is and is not available.

**What is proved unconditionally.**

* the exact public predicate `Erdos287Counterexample` and the one-way bridge to the
  historical compiler type `Gap2CE`, together with the ordered-sequence form of the
  public statement;
* the sign-sensitive Sophie interface and the master finite reduction;
* the maximum-divisor prime blocker (in particular: no counterexample has a prime
  maximum);
* the window-certificate interval engine and the kernel-checked finite range
  `3 ≤ M ≤ 4·10⁹`;
* the deterministic end-to-end compiler `Erdos287ClosureInputs → Erdos287Statement`.

**What is not available.**  No inhabitant of `Erdos287ClosureInputs` is constructed
anywhere in this repository: its `supply` field is an arithmetic statement about large
`M` that is not proved here.  Consequently **no theorem named `erdos287` is declared**,
and Erdős #287 is *not* claimed to be solved.

`#print axioms` below must show only `propext`, `Classical.choice`, `Quot.sound`
(ordinary Mathlib axioms); there is no user axiom, no `sorry`, no `native_decide`,
and no `unsafe` anywhere in the project.
-/

namespace Erdos287

section EndToEndAudit

-- Exact statement and bridge
#print axioms Erdos287.Erdos287Counterexample.toGap2CE
#print axioms Erdos287.Erdos287Counterexample.four_le_max
#print axioms Erdos287.not_erdos287Counterexample_one
#print axioms Erdos287.erdos287_seq_of_no_counterexample

-- Sign-sensitive Sophie interface and master reduction
#print axioms Erdos287.Gap2CE.no_of_plusSophieWitness
#print axioms Erdos287.Gap2CE.no_of_minusSophieWitness
#print axioms Erdos287.Gap2CE.no_of_sophieWitness
#print axioms Erdos287.no_Erdos287Counterexample_of_sophieWitness
#print axioms Erdos287.sophieWitness_imp
#print axioms Erdos287.sophieWitnessB_sweep
#print axioms Erdos287.no_Erdos287Counterexample_of_max_in_39_250

-- The free divisor-of-`M` blocker
#print axioms Erdos287.Gap2CE.maxDivisorPrime_blocker
#print axioms Erdos287.Gap2CE.no_Gap2CE_of_prime_max
#print axioms Erdos287.Gap2CE.no_Gap2CE_of_max_eq_two_mul_prime
#print axioms Erdos287.no_Erdos287Counterexample_of_prime_max

-- The window-certificate engine and the finite range
#print axioms Erdos287.C_le_CVal
#print axioms Erdos287.excludedPP_of_window_le
#print axioms Erdos287.Gap2CE.blocker_window
#print axioms Erdos287.Gap2CE.no_of_M_le_4e9
#print axioms Erdos287.no_Erdos287Counterexample_of_max_le_4e9

-- The remaining interface and the end-to-end compiler
#print axioms Erdos287.Gap2CE.no_of_windowPairSupply
#print axioms Erdos287.windowPairSupply_of_sophieWitness
#print axioms Erdos287.no_Erdos287Counterexample_of_closure
#print axioms Erdos287.erdos287_seq_of_closure

-- Preserved V1/V2 bank (regression check)
#print axioms Erdos287.Gap2CE.halfRange_min_le
#print axioms Erdos287.topExp_le_one_of_lt_sq
#print axioms Erdos287.topHalf_prime_hole
#print axioms Erdos287.q_and_two_mul_q_holes
#print axioms Erdos287.Gap2CE.v2_plus_sophie_blocker
#print axioms Erdos287.Gap2CE.v2_minus_sophie_blocker
#print axioms Erdos287.Gap2CE.v2_finite_compiler
#print axioms Erdos287.Gap2CE.v2_exact_compiler
#print axioms Erdos287.no_Gap2CE_M_eq_104
#print axioms Erdos287.sophieWitness_sweep
#print axioms Erdos287.no_Gap2CE_of_M_in_39_250

end EndToEndAudit

/-! ## One numeric item from the Ford geometry ledger

The only part of the published Ford–Maynard positive geometry that can be checked here is
the rational comparison of the exponent `1/6` with the numerical margin quoted in the
dossier.  Everything else about that geometry is external to this repository and is
recorded as an uninhabited input, never as a theorem. -/

/-- `1/6 > 1663/10000`. -/
theorem one_sixth_gt_margin : (1 : ℚ) / 6 > 1663 / 10000 := by norm_num

end Erdos287
