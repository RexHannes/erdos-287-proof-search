import RequestProject.Erdos287.FixedCertificateSingletonCompiler

/-!
# V13 status ledger — the canonical singleton reduction

**Erdős #287 remains OPEN.**  Nothing in this run proves it, and nothing in this run
proves the Twin Prime Conjecture, Gate 1A/1B analytic closure, H8/H9 smallness, the
seven-prime analytic Kummer bound, the fixed-certificate full leakage, the Ford
lower-bound application for the #287 affine sequence, or `WindowPairSupply` for all large
`M`.

## Final ledger

```
K0-SMOOTH-LEAKAGE-SOURCE45                            SOURCE_BLOCKED
MU-SPLITTABLE45 / Ford–Maynard Lemma 7.17             PUBLISHED_EXTERNAL_INPUT
FordSmoothFragmentCertificate (s,r ≤ 20)              CONDITIONAL_INTERFACE
CANONICAL-SINGLETON-E45                               PROVED_ALGEBRAIC
SINGLETON-COMPLEMENT-DEPTH39                          PROVED_FINITE
SINGLETON PARAMETER LEDGER (exact ℚ)                  PROVED_ALGEBRAIC
NORMALISED SMOOTH-VECTOR LEMMA                        PROVED_ALGEBRAIC
REAL-POWER TRANSLATION                                PROVED_ALGEBRAIC
287-SMOOTH-PARITY-FRAGMENT-TO-SINGLETON-TYPEII45      PROVED_COMPILER
287-SMOOTH-PARITY-SINGLETON-GENERATED-TYPEII45        OPEN_ANALYTIC
SMOOTH-PARITY                                         CONDITIONAL_INTERFACE / OPEN_ANALYTIC
FCL                                                   OPEN_ANALYTIC
ERDOS287                                              OPEN_ANALYTIC
```

## Hostile checks (Part N)

1. `ε < ν₀/100 ⇒ ε < σ/3`?  **YES** — `epsilon_lt_sigma_div_three`; equivalent to
   `5ε < ν₀`, and `ε < ν₀/100` gives `5ε < ν₀/20`.
2. `σ < 1/6` strict with exact rational `ν₀`?  **YES** — `sigma_lt_one_sixth`, and even
   the unshrunk `nu0R_lt_one_sixth` (`99738 < 100000`).
3. Is `s = r = 1` impossible under the exact terminal convention?  **YES, but not by the
   route in the brief.**  The interface does *not* force a singleton side to be terminal,
   so the `1 ≤ 2σ/3` argument needs the extra hypothesis; it is recorded as
   `fragment_singleton_terminal_contradiction`.  The unconditional proof used downstream
   is `fragment_seven_le_card` (`1 ≤ (s+r)σ` and `6σ < 1`, hence `s + r ≥ 7`), which is
   strictly stronger and terminality-free.
4. Does each side have at most one terminal factor?  **YES by construction** — `tu`, `tv`
   are `Option ℕ`.
5. Does `s = 1 ⇒ r ≥ 2` follow with no omitted zero-factor case?  **YES** —
   `s_pos`/`r_pos` exclude empty sides, and `fragment_r_ge_of_s_eq_one` gives `r ≥ 6`.
6. Does the selected first factor have nonterminal support?  **YES, and only because of
   the terminal-position convention** `tu_last`/`tv_last` (terminal piece is last).  With
   the selected side of length `≥ 2`, index `0 ≠ length − 1`.  See `chosen_nonterminal`.
7. Complement depth `39`, not `40`?  **YES** — `singleton_complement_depth_le_39` also
   proves the complement equals `fragmentDepth − 1`.
8. Does any step silently use the analytic singleton estimate?  **NO** — Parts C, D, F, G,
   H are independent of `SingletonGeneratedTypeIIInput`; the Part J compilers take it as
   an explicit named antecedent.
9. Is `cell_identity` proved from source definitions or assumed?  **ASSUMED, and flagged**
   — `K0CellIdentitySource` is an antecedent everywhere; the packet is never inhabited.
10. Is any external Ford theorem disguised as a Lean axiom?  **NO** — there is no `axiom`
    declaration anywhere in the project; Lemma 7.17 appears only as the never-inhabited
    `FordSmoothFragmentCertificate`.

## Provider firewall (Part K)

No inhabited bridge is declared from `SingletonClass.mobius` to Gate 1B, from
`SingletonClass.model` to QK56, or from `SingletonGeneratedTypeIIInput` to Gate 1A, H8/H9,
Pascadi, or a well-factorable theorem.  `depth = 1` implies no historical gate object.
-/

namespace Erdos287
namespace SingletonV13Status

open Erdos287.Singleton

/-! ## Part D — parameter ledger -/

#print axioms Erdos287.Singleton.nu0R_eq_cast_nu0
#print axioms Erdos287.Singleton.nu0R_lt_one_sixth
#print axioms Erdos287.Singleton.admissibleEps_nonempty
#print axioms Erdos287.Singleton.sigma_pos
#print axioms Erdos287.Singleton.sigma_le_nu0
#print axioms Erdos287.Singleton.epsilon_lt_sigma
#print axioms Erdos287.Singleton.epsilon_lt_sigma_div_three
#print axioms Erdos287.Singleton.sigma_lt_one_sixth
#print axioms Erdos287.Singleton.two_sigma_div_three_lt_one
#print axioms Erdos287.Singleton.two_sigma_lt_one
#print axioms Erdos287.Singleton.sigma_lt_epsilon_add_sigma
#print axioms Erdos287.Singleton.six_sigma_lt_one
#print axioms Erdos287.Singleton.seven_mul_sigma_gt_one
#print axioms Erdos287.Singleton.sigma_div_three_lt_sigma
#print axioms Erdos287.Singleton.epsilon_le_one

/-! ## Part C — the normalised smooth-vector lemma -/

#print axioms Erdos287.Singleton.exists_subset_sum_in_typeII_window
#print axioms Erdos287.Singleton.exists_singleton_subset_sum_in_typeII_window

/-! ## Parts E/F — fragmentation interface and the canonical singleton theorem -/

#print axioms Erdos287.Singleton.FordSmoothFragmentCertificate.zu_le_sigma
#print axioms Erdos287.Singleton.FordSmoothFragmentCertificate.zv_le_sigma
#print axioms Erdos287.Singleton.FordSmoothFragmentCertificate.total_le_card_mul_sigma
#print axioms Erdos287.Singleton.fragment_seven_le_card
#print axioms Erdos287.Singleton.fragment_not_both_singleton
#print axioms Erdos287.Singleton.fragment_singleton_terminal_contradiction
#print axioms Erdos287.Singleton.fragment_r_ge_of_s_eq_one
#print axioms Erdos287.Singleton.chosen_nonterminal
#print axioms Erdos287.Singleton.canonical_singleton_typeII
#print axioms Erdos287.Singleton.canonical_singleton_card_eq_one
#print axioms Erdos287.Singleton.singleton_supersedes_depth_five
#print axioms Erdos287.Singleton.chosenClass_mobius_iff

/-! ## Part G — real-power translation -/

#print axioms Erdos287.Singleton.singleton_real_power_window
#print axioms Erdos287.Singleton.singleton_real_power_window_shifted

/-! ## Part H — complement depth -/

#print axioms Erdos287.Singleton.fragment_depth_le_40
#print axioms Erdos287.Singleton.two_le_fragment_depth
#print axioms Erdos287.Singleton.singleton_complement_depth_le_39

/-! ## Parts B/J — the conditional compiler -/

#print axioms Erdos287.Singleton.k0CellIdentitySource_is_cell_identity
#print axioms Erdos287.Singleton.smoothParity_of_singletonTypeII
#print axioms Erdos287.Singleton.parentLeakage_of_singletonTypeII
#print axioms Erdos287.Singleton.primeMassPos_of_singletonTypeII

/-! ## Non-vacuity guards -/

#print axioms Erdos287.Singleton.epsWitness_admissible
#print axioms Erdos287.Singleton.fragmentWitness_depth
#print axioms Erdos287.Singleton.fragmentWitness_chosen

/-! ## Interfaces that remain uninhabited

The following are stated but never inhabited anywhere in the project.  They are listed
here so that the claim is checkable by `#check` rather than by prose. -/

#check @Erdos287.Singleton.FordSmoothFragmentCertificate
#check @Erdos287.Singleton.SingletonGeneratedTypeIIInput
#check @Erdos287.Singleton.SingletonPacketReduction
#check @Erdos287.Singleton.K0CellIdentitySource
#check @Erdos287.SmoothParity.FixedCertificateSmoothParityPacket

end SingletonV13Status
end Erdos287
