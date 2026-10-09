import RequestProject.Erdos287.W2984Publication.RegressionSuite

/-!
# W2.984 — axiom, provider and semantic-firewall audit (runs at build time)

* `#assert_std_axioms_v90 foo` (imported from the W3 audit) fails the build unless `foo` depends
  only on `propext`, `Classical.choice`, `Quot.sound` (so `sorryAx`, custom axioms and the
  `native_decide` axiom `Lean.ofReduceBool` are rejected).
* `#audit_providers_w2984` fails the build if any declaration of `Erdos287.W2984Publication`
  *produces* one of the provider structures without taking a provider as hypothesis, or takes a
  hypothesis of type `False` / `IsEmpty _`.
* `#assert_mentions foo [consts]` / `#assert_avoids foo [consts]` — statement-level firewall:
  the W2.984 theorem must visibly mention all four Chen providers and the W3 framework, and the
  providers must not mention `W3Statement`, `WindowMomentData`, `occupied`, `ContactWitness`
  (no provider contains W2.984 or an occupancy/contact conclusion).
-/

open Lean Elab Command Meta

/-- Providers of the W2.984 subtree. -/
def providersW2984 : List Name :=
  [`Erdos287.W2984Publication.W3FrameworkProvider,
   `Erdos287.W2984Publication.AffineChenS1Provider,
   `Erdos287.W2984Publication.AffineChenS2Provider,
   `Erdos287.W2984Publication.AffineChenS3Provider,
   `Erdos287.W2984Publication.AffineChenSquareTailProvider,
   `Erdos287.W2984Publication.PairBoundProvider]

/-- Fail if some declaration produces a provider unguardedly or from a vacuous hypothesis. -/
elab "#audit_providers_w2984" : command => do
  let env ← getEnv
  let pre : Name := `Erdos287.W2984Publication
  for p in providersW2984 do
    unless env.contains p do throwError "provider {p} not found"
  let skipSuffix : List String :=
    ["mk", "casesOn", "recOn", "rec", "brecOn", "binductionOn", "below", "ibelow",
     "noConfusion", "noConfusionType", "ctorIdx", "ctorElim", "ctorElimType", "injEq", "inj",
     "sizeOf_spec", "mk.injEq", "mk.inj", "mk.sizeOf_spec"]
  let mut checked : Array Name := #[]
  for (n, ci) in env.constants.toList do
    unless pre.isPrefixOf n do continue
    if n.isInternal then continue
    let last := n.getString!
    if skipSuffix.contains last then continue
    if (← liftCoreM <| isProjectionFn n) then continue
    let r ← liftTermElabM <| forallTelescopeReducing ci.type fun xs body => do
      let concl := body.getAppFn.constName?
      match concl with
      | some c =>
        if providersW2984.contains c then
          let mut guarded := false
          let mut vacuous := false
          for x in xs do
            let ty ← inferType x
            let ty ← whnf ty
            if let some h := ty.getAppFn.constName? then
              if providersW2984.contains h then guarded := true
              if h == ``False || h == ``IsEmpty then vacuous := true
          return some (guarded, vacuous)
        else return none
      | none => return none
    if let some (g, v) := r then
      checked := checked.push n
      unless g do throwError "{n} produces a provider without a provider hypothesis"
      if v then throwError "{n} produces a provider from a vacuous hypothesis"
  logInfo m!"W2.984 provider audit passed; guarded provider-producing declarations: {checked}"

/-- Fail unless the statement of `id` mentions every constant in the list. -/
elab "#assert_mentions " id:ident " [" cs:ident,* "]" : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let used := (← getConstInfo n).type.getUsedConstants
  for c in cs.getElems do
    let cn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo c
    unless used.contains cn do throwError "{n} does not mention {cn}"
  logInfo m!"{n} mentions all required constants"

/-- Fail if the statement or *any field type* of structure `id` mentions a listed constant. -/
elab "#assert_avoids " id:ident " [" cs:ident,* "]" : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let mut used := (← getConstInfo n).type.getUsedConstants
  if let some info := getStructureInfo? env n then
    for f in info.fieldNames do
      if let some pf := getProjFnForField? env n f then
        used := used ++ (← getConstInfo pf).type.getUsedConstants
  for c in cs.getElems do
    let cn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo c
    if used.contains cn then throwError "{n} mentions forbidden {cn}"
  logInfo m!"{n} avoids all forbidden constants"

namespace Erdos287.W2984Publication
open Erdos287.PostV87V90R
end Erdos287.W2984Publication

/-! ## Axioms of the principal kernel theorems -/

-- scalar layer
#assert_std_axioms_v90 Erdos287.W2984Publication.Omega1_sub_Omega2
#assert_std_axioms_v90 Erdos287.W2984Publication.Omega1_seventh
#assert_std_axioms_v90 Erdos287.W2984Publication.Omega2_seventh
#assert_std_axioms_v90 Erdos287.W2984Publication.buchstab_le
#assert_std_axioms_v90 Erdos287.W2984Publication.buchstab_dde_mid
#assert_std_axioms_v90 Erdos287.W2984Publication.buchstab_dde_tail
#assert_std_axioms_v90 Erdos287.W2984Publication.Flin_dde
#assert_std_axioms_v90 Erdos287.W2984Publication.flin_dde
#assert_std_axioms_v90 Erdos287.W2984Publication.Omega3_le
#assert_std_axioms_v90 Erdos287.W2984Publication.J_lower
#assert_std_axioms_v90 Erdos287.W2984Publication.log_three_halves_le
#assert_std_axioms_v90 Erdos287.W2984Publication.log_five_fourths_le
#assert_std_axioms_v90 Erdos287.W2984Publication.pairConstant_le_certificate
#assert_std_axioms_v90 Erdos287.W2984Publication.pairConstant_lt
#assert_std_axioms_v90 Erdos287.W2984Publication.certificate_room
#assert_std_axioms_v90 Erdos287.W2984Publication.flin_le_lipschitz
#assert_std_axioms_v90 Erdos287.W2984Publication.explicit_Cerr_lt
#assert_std_axioms_v90 Erdos287.W2984Publication.explicit_delta0
-- Chen decomposition
#assert_std_axioms_v90 Erdos287.W2984Publication.chen_pointwise
#assert_std_axioms_v90 Erdos287.W2984Publication.card_triples_ge
#assert_std_axioms_v90 Erdos287.W2984Publication.chen_weighted
#assert_std_axioms_v90 Erdos287.W2984Publication.affine_chen_weighted
#assert_std_axioms_v90 Erdos287.W2984Publication.merikoski_pointwise_fails
#assert_std_axioms_v90 Erdos287.W2984Publication.merikoski_weighted_fails
-- congruence transfer / CRT
#assert_std_axioms_v90 Erdos287.W2984Publication.dvd_form_iff
#assert_std_axioms_v90 Erdos287.W2984Publication.coprime_of_dvd_form
#assert_std_axioms_v90 Erdos287.W2984Publication.progression_iff
#assert_std_axioms_v90 Erdos287.W2984Publication.progression_surj
#assert_std_axioms_v90 Erdos287.W2984Publication.base_residue_unit
#assert_std_axioms_v90 Erdos287.W2984Publication.totient_mul_of_primeFactors_subset
#assert_std_axioms_v90 Erdos287.W2984Publication.coprime_of_dvd_forms
#assert_std_axioms_v90 Erdos287.W2984Publication.local_density_designated
#assert_std_axioms_v90 Erdos287.W2984Publication.overlap_empty
#assert_std_axioms_v90 Erdos287.W2984Publication.switched_identity
#assert_std_axioms_v90 Erdos287.W2984Publication.switched_progression
-- ledger
#assert_std_axioms_v90 Erdos287.W2984Publication.totalS1_eq
#assert_std_axioms_v90 Erdos287.W2984Publication.totalS1_lt_half
#assert_std_axioms_v90 Erdos287.W2984Publication.v92_core_lt_half
#assert_std_axioms_v90 Erdos287.W2984Publication.totalS3_le
#assert_std_axioms_v90 Erdos287.W2984Publication.reindex_fixed_base
-- downstream implication
#assert_std_axioms_v90 Erdos287.W2984Publication.pairExpect_eq_chenS
#assert_std_axioms_v90 Erdos287.W2984Publication.pairExpect_le_chen
#assert_std_axioms_v90 Erdos287.W2984Publication.pairBound_of_chen
#assert_std_axioms_v90 Erdos287.W2984Publication.E_Qcount_eq
#assert_std_axioms_v90 Erdos287.W2984Publication.E_Qcount_le
#assert_std_axioms_v90 Erdos287.W2984Publication.exists_ratio
#assert_std_axioms_v90 Erdos287.W2984Publication.width_of_pairBound
#assert_std_axioms_v90 Erdos287.W2984Publication.W2984
#assert_std_axioms_v90 Erdos287.W2984Publication.W2984_counterexample_form
#assert_std_axioms_v90 Erdos287.W2984Publication.W3_of_selbergPairBound
#assert_std_axioms_v90 Erdos287.W3Publication.counterexample_form
-- regressions
#assert_std_axioms_v90 Erdos287.W2984Publication.reg1_spectator_density
#assert_std_axioms_v90 Erdos287.W2984Publication.reg2_uncorrected_remainder
#assert_std_axioms_v90 Erdos287.W2984Publication.reg4_exponent
#assert_std_axioms_v90 Erdos287.W2984Publication.reg5_nonsquarefree
#assert_std_axioms_v90 Erdos287.W2984Publication.reg6_max_placement
#assert_std_axioms_v90 Erdos287.W2984Publication.reg8_delta_budget
#assert_std_axioms_v90 Erdos287.W2984Publication.reg11_narrow_windows_exist
#assert_std_axioms_v90 Erdos287.W2984Publication.reg13_sign

/-! ## Provider firewall -/

#audit_providers_w2984

#assert_mentions Erdos287.W2984Publication.W2984 [Erdos287.W2984Publication.W3FrameworkProvider,
  Erdos287.W2984Publication.AffineChenS1Provider, Erdos287.W2984Publication.AffineChenS2Provider,
  Erdos287.W2984Publication.AffineChenS3Provider,
  Erdos287.W2984Publication.AffineChenSquareTailProvider, Erdos287.PostV87V90R.W3Statement]

#assert_avoids Erdos287.W2984Publication.W3FrameworkProvider [Erdos287.PostV87V90R.W3Statement,
  Erdos287.PostV87V90R.WindowMomentData, Erdos287.PostV87V90R.occupied,
  Erdos287.PostV87V90R.ContactWitness, Erdos287.W2984Publication.pairExpect]
#assert_avoids Erdos287.W2984Publication.FrameworkFamily [Erdos287.PostV87V90R.W3Statement,
  Erdos287.PostV87V90R.WindowMomentData, Erdos287.PostV87V90R.occupied,
  Erdos287.PostV87V90R.ContactWitness, Erdos287.W2984Publication.pairExpect]
#assert_avoids Erdos287.W2984Publication.FrameworkWindowData [Erdos287.PostV87V90R.W3Statement,
  Erdos287.PostV87V90R.WindowMomentData, Erdos287.PostV87V90R.occupied,
  Erdos287.PostV87V90R.ContactWitness, Erdos287.W2984Publication.pairExpect]
#assert_avoids Erdos287.W2984Publication.AffineChenS1Provider [Erdos287.PostV87V90R.W3Statement,
  Erdos287.PostV87V90R.WindowMomentData, Erdos287.PostV87V90R.occupied,
  Erdos287.PostV87V90R.ContactWitness, Erdos287.W2984Publication.pairExpect]
#assert_avoids Erdos287.W2984Publication.AffineChenS2Provider [Erdos287.PostV87V90R.W3Statement,
  Erdos287.PostV87V90R.WindowMomentData, Erdos287.PostV87V90R.occupied,
  Erdos287.PostV87V90R.ContactWitness, Erdos287.W2984Publication.pairExpect]
#assert_avoids Erdos287.W2984Publication.AffineChenS3Provider [Erdos287.PostV87V90R.W3Statement,
  Erdos287.PostV87V90R.WindowMomentData, Erdos287.PostV87V90R.occupied,
  Erdos287.PostV87V90R.ContactWitness, Erdos287.W2984Publication.pairExpect]
#assert_avoids Erdos287.W2984Publication.AffineChenSquareTailProvider
  [Erdos287.PostV87V90R.W3Statement, Erdos287.PostV87V90R.WindowMomentData,
  Erdos287.PostV87V90R.occupied, Erdos287.PostV87V90R.ContactWitness,
  Erdos287.W2984Publication.pairExpect]
