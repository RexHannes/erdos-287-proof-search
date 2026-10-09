import RequestProject.Erdos287.AnchoredV3.OpenOwners

/-!
# Anchored V3 — the append-only reconciliation ledger

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Anchored V2 is frozen and unchanged: no V2 statement is edited, renamed, weakened, deleted or
re-proved by this layer; Route S, Route D and Anchored V1 are untouched; the certified finite
frontier `67108856338751594` is unchanged and is **not** extended, and `U2` remains pending.

## BANKED EXACTLY (proved in this layer, no analytic input)

* `globalNeutral_of_rowwiseNeutral` — rowwise neutrality implies global neutrality.
* `rowwise_sufficient_not_necessary`, `exists_globalNeutral_not_rowwiseNeutral` — rowwise
  neutrality is **not** necessary; an explicit finite witness is globally neutral but not
  rowwise neutral.
* `modulus_eq_core_mul_mult` — the exact `D = D_core * U_mult` decomposition under explicit
  coprimality.
* `OldEmptyNewHit.same_bank_old_empty_new_global_hit` — the exact old-empty / new-global-hit
  finite certificate on one fixed bank.
* `sum_recip_zeroPattern`, `Bank.globalColumnCompiler` — exact zero-pattern integer weights and
  the complete fixed-bank global column compiler.
* `ColumnPackets.exists_disjoint_packets`, `ColumnPackets.sum_biUnion_eq_zero` — column zero-sum
  packet extraction and neutrality of unions of packets.
* `ColumnLattice.boolean_column_gcd`, `ColumnLattice.sharpness_witness_two` — the Boolean
  column-lattice gcd theorem and its sharpness witness at `n = 2q - 2`.
* `MobilityData.den_dvd_Dcore`, `MobilityData.target_movement` — fixed-bank target mobility.
* `MobilityFamily.card_targets`, `MobilityFamily.no_three_term_ap`,
  `MobilityFamily.card_targets_add_targets` — distinct mobility targets, AP-free mobility
  family, and the exact `3 ^ H` sumset count.
* `AlignedBank.alignment_coefficient`, `AlignedBank.alignment_sumset` — the exact combined
  terminal × mobility coefficient identity.
* `mobility_cofactor_gcd` — the exact mobility congruence coset `gcd {D/n} = D/G`.

## BANKED ONLY AS CONDITIONAL INTERFACES

* `RowFibreData.card_image_ge` — the support-size lower bound *from* a uniform row-fibre input.
* `CentralityToBoundedTilt` — bounded tilt from a central compatible baseline (OPEN).
* `Resonance.SparseResonanceArcBudget`, `Resonance.CentralLobeBudget`,
  `Resonance.RemainingSpectrumBudget` — the three spectrum estimates (OPEN).
* `conditional_terminal_closure` — the exact terminal HIT **from all analytic hypotheses
  together**, via `AntiHoleBridge` (OPEN) and a coefficient model.

## NOT BANKED

* existence of an actual compatible baseline;
* existence of a central actual baseline;
* any asymptotic exact target HIT;
* any Erdős #287 proof or counterexample;
* any extension of the certified finite frontier;
* the source-side asymptotic conclusion `log |support| = (1 + o(1)) √M`;
* the additive-energy identity `6 ^ H`.

## RETIRED / FALSE AS UNIVERSAL SHORTCUTS

* per-row multiplier neutrality as a *necessary* condition
  (refuted: `exists_globalNeutral_not_rowwiseNeutral`);
* “many packets ⇒ target hit” (refuted: `ColumnPackets.manyNeutralPackets_not_exactTarget`);
* “support huge ⇒ target hit”;
* “gcd 1 ⇒ target hit” (the gcd theorem is about the integer span only, and overlapping
  patterns plus subtraction are used);
* “mass bracket contains target ⇒ exact hit”;
* “many movable targets ⇒ long arithmetic progression”
  (refuted: `MobilityFamily.no_three_term_ap`);
* “global CLT ⇒ local exact positivity”.

## DEPENDENCY CHAIN

```
Anchored V2 (frozen)
  → GlobalNeutrality  (global-neutral legality)
  → ColumnZeroPatterns → GlobalColumnCompiler   (fixed-bank global compiler)
  → TargetMobility → MobilityStructure          (target mobility, negative structure)
  → AlignmentPolynomial                          (exact terminal × mobility coefficient)
  → FourierHitInterface / ResonanceInterfaces / BaselineCentrality  (conditional interfaces)
  → ConditionalClosure                           (dependency theorem)
  → OpenOwners                                   (actual-baseline / spectrum owners, OPEN)
```

Verdict of this layer: `BANKED_ANCHORED_V3_GLOBAL_TERMINAL_MOBILITY`.
-/

namespace Erdos287
namespace AnchoredV3

/-- The V3 ledger marker: this layer banks exact finite algebra and conditional interfaces
only.  Erdős #287 remains `OPEN`. -/
def ledgerVerdict : String := "BANKED_ANCHORED_V3_GLOBAL_TERMINAL_MOBILITY"

end AnchoredV3
end Erdos287
