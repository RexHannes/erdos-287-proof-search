import RequestProject.Erdos287.CurrentTail.ClosureDAG

/-!
# Erdős #287 — current tail consolidation: trust / axiom / provider audit (build time)

* `#ct_assert_std_axioms foo` — fails the build unless `foo` depends only on `propext`,
  `Classical.choice`, `Quot.sound` (rejects `sorryAx`, custom axioms and `Lean.ofReduceBool`,
  i.e. `native_decide`).
* `#ct_audit_providers` — fails if any declaration of `Erdos287.CurrentTail` *concludes* a
  provider / framework / dictionary / tail statement without taking a guarded hypothesis, or
  takes a hypothesis of type `False` / `IsEmpty _` (no fake instances, no `False.elim`
  providers).  Constructors / recursors are skipped.
* `#ct_assert_avoids P [consts]` — the statement and every field of `P` avoid the listed
  constants: **no provider mentions `R_Σ^P`, the tail statement, counterexamples or exact
  words**; the source dictionary does not mention `R_Σ^P` or the tail statement.
* `#ct_assert_mentions T [consts]` — the conditional tail theorem visibly carries every provider.
-/

open Lean Elab Command Meta

/-- Fail unless `id` depends only on the three standard axioms. -/
elab "#ct_assert_std_axioms " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| Lean.collectAxioms n
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for a in axs do
    unless ok.contains a do
      throwError "{n} depends on non-standard axiom {a}"
  logInfo m!"{n} : standard axioms only {axs}"

/-- Guarded constants: providers, frameworks, dictionaries and the tail statement. -/
def guardedCT : List Name :=
  [`Erdos287.CurrentTail.MaynardE1Estimate, `Erdos287.CurrentTail.PascadiE2Printed,
   `Erdos287.CurrentTail.QuantitativeTH, `Erdos287.CurrentTail.BDHStatement,
   `Erdos287.CurrentTail.BDHFamily, `Erdos287.CurrentTail.ReciprocalDivisorMoment,
   `Erdos287.CurrentTail.SpectatorMomentFamily, `Erdos287.CurrentTail.BaseSWProvider,
   `Erdos287.CurrentTail.AuxPieceProviders, `Erdos287.CurrentTail.OrderingBSourceDictionary,
   `Erdos287.CurrentTail.SevenBlockTailFramework,
   `Erdos287.CurrentTail.SevenBlockMainTermDictionary,
   `Erdos287.CurrentTail.NearDiagonalRangeComparison, `Erdos287.CurrentTail.Tail287Statement,
   `Erdos287.CurrentTail.EffectiveOnset, `Erdos287.CurrentTail.FiniteBank,
   `Erdos287.CurrentTail.IntermediateRange, `Erdos287.CurrentTail.Erdos287Global]

elab "#ct_audit_providers" : command => do
  let env ← getEnv
  let pre : Name := `Erdos287.CurrentTail
  for p in guardedCT do
    unless env.contains p do throwError "guarded constant {p} not found"
  let skipSuffix : List String :=
    ["mk", "casesOn", "recOn", "rec", "brecOn", "binductionOn", "below", "ibelow",
     "noConfusion", "noConfusionType", "ctorIdx", "ctorElim", "ctorElimType", "injEq", "inj",
     "sizeOf_spec"]
  let mut checked : Array Name := #[]
  for (n, ci) in env.constants.toList do
    unless pre.isPrefixOf n do continue
    if n.isInternal then continue
    if guardedCT.contains n then continue
    let last := n.getString!
    if skipSuffix.contains last then continue
    if (← liftCoreM <| isProjectionFn n) then continue
    let r ← liftTermElabM <| forallTelescope ci.type fun xs body => do
      match body.getAppFn.constName? with
      | some c =>
        if guardedCT.contains c then
          let mut guarded := false
          let mut vacuous := false
          for x in xs do
            let ty ← inferType x
            if let some h := ty.getAppFn.constName? then
              if guardedCT.contains h then guarded := true
              if h == ``False || h == ``IsEmpty then vacuous := true
          return some (guarded, vacuous)
        else return none
      | none => return none
    if let some (g, v) := r then
      checked := checked.push n
      unless g do throwError "{n} concludes a guarded statement without a guarded hypothesis"
      if v then throwError "{n} concludes a guarded statement from a vacuous hypothesis"
  logInfo m!"CurrentTail provider audit passed; guarded-conclusion declarations: {checked}"

elab "#ct_assert_avoids " id:ident " [" cs:ident,* "]" : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let mut used := (← getConstInfo n).type.getUsedConstants
  if let some v := (← getConstInfo n).value? then
    used := used ++ v.getUsedConstants
  if let some info := getStructureInfo? env n then
    for f in info.fieldNames do
      if let some pf := getProjFnForField? env n f then
        used := used ++ (← getConstInfo pf).type.getUsedConstants
  for c in cs.getElems do
    let cn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo c
    if used.contains cn then throwError "{n} mentions forbidden {cn}"
  logInfo m!"{n} avoids all forbidden constants"

elab "#ct_assert_mentions " id:ident " [" cs:ident,* "]" : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let used := (← getConstInfo n).type.getUsedConstants
  for c in cs.getElems do
    let cn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo c
    unless used.contains cn do throwError "{n} does not mention {cn}"
  logInfo m!"{n} mentions all required constants"

#ct_audit_providers

/-! ## No provider contains its downstream conclusion -/

#ct_assert_avoids Erdos287.CurrentTail.MaynardE1Estimate [Erdos287.CurrentTail.TensorSource.RSigmaP,
  Erdos287.CurrentTail.Tail287Statement, Erdos287.Erdos287Counterexample,
  Erdos287.PostV71V87.ExactWord, Erdos287.CurrentTail.IsLittleOTarget]
#ct_assert_avoids Erdos287.CurrentTail.PascadiE2Printed [Erdos287.CurrentTail.TensorSource.RSigmaP,
  Erdos287.CurrentTail.Tail287Statement, Erdos287.Erdos287Counterexample,
  Erdos287.PostV71V87.ExactWord, Erdos287.CurrentTail.IsLittleOTarget]
#ct_assert_avoids Erdos287.CurrentTail.QuantitativeTH [Erdos287.CurrentTail.TensorSource.RSigmaP,
  Erdos287.CurrentTail.Tail287Statement, Erdos287.Erdos287Counterexample,
  Erdos287.PostV71V87.ExactWord, Erdos287.CurrentTail.IsLittleOTarget]
#ct_assert_avoids Erdos287.CurrentTail.BDHStatement [Erdos287.CurrentTail.TensorSource.RSigmaP,
  Erdos287.CurrentTail.Tail287Statement, Erdos287.Erdos287Counterexample,
  Erdos287.PostV71V87.ExactWord, Erdos287.CurrentTail.DeltaRel, Erdos287.CurrentTail.Vrel]
#ct_assert_avoids Erdos287.CurrentTail.BDHFamily [Erdos287.CurrentTail.TensorSource.RSigmaP,
  Erdos287.CurrentTail.Tail287Statement, Erdos287.Erdos287Counterexample,
  Erdos287.PostV71V87.ExactWord, Erdos287.CurrentTail.DeltaRel, Erdos287.CurrentTail.Vrel]
#ct_assert_avoids Erdos287.CurrentTail.ReciprocalDivisorMoment
  [Erdos287.CurrentTail.TensorSource.RSigmaP, Erdos287.CurrentTail.Tail287Statement,
  Erdos287.Erdos287Counterexample, Erdos287.PostV71V87.ExactWord]
#ct_assert_avoids Erdos287.CurrentTail.SpectatorMomentFamily
  [Erdos287.CurrentTail.TensorSource.RSigmaP, Erdos287.CurrentTail.Tail287Statement,
  Erdos287.Erdos287Counterexample, Erdos287.PostV71V87.ExactWord]
#ct_assert_avoids Erdos287.CurrentTail.BaseSWProvider [Erdos287.CurrentTail.TensorSource.RSigmaP,
  Erdos287.CurrentTail.Tail287Statement, Erdos287.Erdos287Counterexample,
  Erdos287.PostV71V87.ExactWord]
#ct_assert_avoids Erdos287.CurrentTail.AuxPieceProviders [Erdos287.CurrentTail.TensorSource.RSigmaP,
  Erdos287.CurrentTail.Tail287Statement, Erdos287.Erdos287Counterexample,
  Erdos287.PostV71V87.ExactWord]
#ct_assert_avoids Erdos287.CurrentTail.OrderingBSourceDictionary
  [Erdos287.CurrentTail.TensorSource.RSigmaP, Erdos287.CurrentTail.Tail287Statement,
  Erdos287.Erdos287Counterexample, Erdos287.PostV71V87.ExactWord]
#ct_assert_avoids Erdos287.CurrentTail.SevenBlockTailFramework
  [Erdos287.CurrentTail.Tail287Statement, Erdos287.CurrentTail.IsLittleOTarget,
  Erdos287.Erdos287Counterexample]
#ct_assert_avoids Erdos287.CurrentTail.SevenBlockMainTermDictionary
  [Erdos287.CurrentTail.Tail287Statement, Erdos287.CurrentTail.IsLittleOTarget,
  Erdos287.Erdos287Counterexample, Erdos287.PostV71V87.ExactWord]

/-! ## The conditional tail theorem visibly carries every input -/

#ct_assert_mentions Erdos287.CurrentTail.Tail287_of_AnalyticProviders
  [Erdos287.CurrentTail.MaynardE1Estimate, Erdos287.CurrentTail.PascadiE2Printed,
  Erdos287.CurrentTail.QuantitativeTH, Erdos287.CurrentTail.BDHFamily,
  Erdos287.CurrentTail.SpectatorMomentFamily, Erdos287.CurrentTail.BaseSWProvider,
  Erdos287.CurrentTail.AuxPieceProviders, Erdos287.CurrentTail.OrderingBSourceDictionary,
  Erdos287.CurrentTail.SevenBlockTailFramework]

/-! ## Axioms of the principal theorems -/

-- exact source
#ct_assert_std_axioms Erdos287.CurrentTail.v99_relative_centering
#ct_assert_std_axioms Erdos287.CurrentTail.TensorSource.RSigmaP_eq_Rrel_add_Rpaid
#ct_assert_std_axioms Erdos287.CurrentTail.TensorSource.Rrel_indep_main
#ct_assert_std_axioms Erdos287.CurrentTail.TensorSource.Rpaid_factor
#ct_assert_std_axioms Erdos287.CurrentTail.TensorSource.Rpaid_bound
-- relative BDH
#ct_assert_std_axioms Erdos287.CurrentTail.modEq_crt_iff
#ct_assert_std_axioms Erdos287.CurrentTail.sum_units_ind_modEq
#ct_assert_std_axioms Erdos287.CurrentTail.rbdh_crt_identity
#ct_assert_std_axioms Erdos287.CurrentTail.variance_contraction
#ct_assert_std_axioms Erdos287.CurrentTail.rbdh_variance_contraction
#ct_assert_std_axioms Erdos287.CurrentTail.crt_mapsTo_units
#ct_assert_std_axioms Erdos287.CurrentTail.crt_injOn
#ct_assert_std_axioms Erdos287.CurrentTail.rbdh_full_contraction
#ct_assert_std_axioms Erdos287.CurrentTail.card_factorization_le_tau
#ct_assert_std_axioms Erdos287.CurrentTail.divisor_weight_transport
#ct_assert_std_axioms Erdos287.CurrentTail.rbdh_pairs_le_weighted
#ct_assert_std_axioms Erdos287.CurrentTail.DeltaRel_eq_Delta_restrict
#ct_assert_std_axioms Erdos287.CurrentTail.relativeSW_of_SW
#ct_assert_std_axioms Erdos287.CurrentTail.RBDH_of_BDH
#ct_assert_std_axioms Erdos287.CurrentTail.relative_term_eq_DeltaRel
-- spectator norm / family payment
#ct_assert_std_axioms Erdos287.CurrentTail.card_fibre_le
#ct_assert_std_axioms Erdos287.CurrentTail.fibre_regroup
#ct_assert_std_axioms Erdos287.CurrentTail.spectator_norm_finite
#ct_assert_std_axioms Erdos287.CurrentTail.spectator_norm_of_moment
#ct_assert_std_axioms Erdos287.CurrentTail.family_payment
#ct_assert_std_axioms Erdos287.CurrentTail.fibre_weight_transport
#ct_assert_std_axioms Erdos287.CurrentTail.family_payment_tau
-- near diagonal
#ct_assert_std_axioms Erdos287.CurrentTail.count_congr_le
#ct_assert_std_axioms Erdos287.CurrentTail.count_congr_window_le
#ct_assert_std_axioms Erdos287.CurrentTail.pairs_congr_window_le
#ct_assert_std_axioms Erdos287.CurrentTail.pairs_congr_window_real
#ct_assert_std_axioms Erdos287.CurrentTail.nearDiagonal_to_reciprocalDensity
-- orderings
#ct_assert_std_axioms Erdos287.CurrentTail.CharacterBeforeCauchy_retired
#ct_assert_std_axioms Erdos287.CurrentTail.orderingB_bound_valid
#ct_assert_std_axioms Erdos287.CurrentTail.orderingA_loses_density
#ct_assert_std_axioms Erdos287.CurrentTail.orderingA_loss_ge_two
#ct_assert_std_axioms Erdos287.CurrentTail.TensorSource.Rrel_eq_main_sub_coprimality
#ct_assert_std_axioms Erdos287.CurrentTail.orderingB_first_cauchy
#ct_assert_std_axioms Erdos287.CurrentTail.orderingB_expand
#ct_assert_std_axioms Erdos287.CurrentTail.orderingB_pair_congr
#ct_assert_std_axioms Erdos287.CurrentTail.orderingB_pairs_subset
#ct_assert_std_axioms Erdos287.CurrentTail.orderingB_routing
-- E1 / E2 source side
#ct_assert_std_axioms Erdos287.CurrentTail.coefficient_placement
#ct_assert_std_axioms Erdos287.CurrentTail.Delta_convolution
#ct_assert_std_axioms Erdos287.CurrentTail.DeltaRel_convolution
#ct_assert_std_axioms Erdos287.CurrentTail.fixedLocal_totient
#ct_assert_std_axioms Erdos287.CurrentTail.fixedLocal_bound
#ct_assert_std_axioms Erdos287.CurrentTail.crt_phase_split
#ct_assert_std_axioms Erdos287.CurrentTail.crt_phase_split_real
#ct_assert_std_axioms Erdos287.CurrentTail.dualLength_enlarged
#ct_assert_std_axioms Erdos287.CurrentTail.forgetting_enlargement_wrong
#ct_assert_std_axioms Erdos287.CurrentTail.kloostermanForm_split
-- exponent ledger
#ct_assert_std_axioms Erdos287.CurrentTail.chooseSigma_pos
#ct_assert_std_axioms Erdos287.CurrentTail.netSaving_chooseSigma
#ct_assert_std_axioms Erdos287.CurrentTail.ledger_instance
#ct_assert_std_axioms Erdos287.CurrentTail.logCost_absorbed
#ct_assert_std_axioms Erdos287.CurrentTail.order_of_choice
-- ledger / recombination / seven block / tail
#ct_assert_std_axioms Erdos287.CurrentTail.allErrors_complete
#ct_assert_std_axioms Erdos287.CurrentTail.no_open_error
#ct_assert_std_axioms Erdos287.CurrentTail.IsLittleOTarget.sum_abs
#ct_assert_std_axioms Erdos287.CurrentTail.Rpaid_littleO
#ct_assert_std_axioms Erdos287.CurrentTail.RSigmaP_littleO_of_providers
#ct_assert_std_axioms Erdos287.CurrentTail.seven_block_margin_eq
#ct_assert_std_axioms Erdos287.CurrentTail.seven_block_margin
#ct_assert_std_axioms Erdos287.CurrentTail.seven_block_margin_rat
#ct_assert_std_axioms Erdos287.CurrentTail.alpha_Gamma72
#ct_assert_std_axioms Erdos287.CurrentTail.seven_block_moment_ineq
#ct_assert_std_axioms Erdos287.CurrentTail.seven_block_three_occupied
#ct_assert_std_axioms Erdos287.CurrentTail.seven_block_of_remainder
#ct_assert_std_axioms Erdos287.CurrentTail.seven_block_of_littleO
#ct_assert_std_axioms Erdos287.CurrentTail.seven_block_contact_false
#ct_assert_std_axioms Erdos287.CurrentTail.seven_block_contact_false_of_remainder
#ct_assert_std_axioms Erdos287.CurrentTail.tail_of_remainder_littleO
#ct_assert_std_axioms Erdos287.CurrentTail.Tail287_of_AnalyticProviders
#ct_assert_std_axioms Erdos287.CurrentTail.global_of_layers
#ct_assert_std_axioms Erdos287.CurrentTail.tail_of_effectiveOnset
-- regressions and DAG
#ct_assert_std_axioms Erdos287.CurrentTail.reg1_dilation_changes_discrepancy
#ct_assert_std_axioms Erdos287.CurrentTail.reg2_fixedResidue_breaks_SW
#ct_assert_std_axioms Erdos287.CurrentTail.reg3_characterBeforeCauchy
#ct_assert_std_axioms Erdos287.CurrentTail.reg4_packetwise_population
#ct_assert_std_axioms Erdos287.CurrentTail.reg5_provider_outside_hypotheses
#ct_assert_std_axioms Erdos287.CurrentTail.reg6_forgetting_fourier_enlargement
#ct_assert_std_axioms Erdos287.CurrentTail.reg7_TH_printed_not_quantitative
#ct_assert_std_axioms Erdos287.CurrentTail.reg8_abs_before_recombination
#ct_assert_std_axioms Erdos287.CurrentTail.reg9_existential_onset
#ct_assert_std_axioms Erdos287.CurrentTail.reg10_tail_alone_no_splice
#ct_assert_std_axioms Erdos287.CurrentTail.dag_acyclic
#ct_assert_std_axioms Erdos287.CurrentTail.orderingA_feeds_nothing
#ct_assert_std_axioms Erdos287.CurrentTail.retired_feeds_nothing
#ct_assert_std_axioms Erdos287.CurrentTail.global_preds
#ct_assert_std_axioms Erdos287.CurrentTail.tail_not_direct_to_global
