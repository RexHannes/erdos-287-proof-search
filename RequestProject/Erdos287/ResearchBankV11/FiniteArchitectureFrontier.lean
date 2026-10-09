import RequestProject.Erdos287.ResearchBankV9

/-!
# Erdős #287 — Research Bank V11 §T: the finite architecture frontier

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `ArchitectureTag`, `killedArchitectures` — the old prescribed CRT architecture, the old
  small-graph / narrow-simplex positive-score route, the three-group `A < 3` architecture, the
  arbitrary-`F` moment route and Chen parameter tuning are **killed in their stated scope**;
* `FiniteArchitectureProvider arch c M_geom ai aj t` — the **OPEN** contract of a genuinely new
  finite architecture: `notKilled` (it is not a killed architecture), `realization` (a gcd-clique
  graph edge at every scale `M ≥ M_geom`), `primeSupply` (both affine forms prime),
  `rigidity` (bounded-cofactor rigidity), `localization` (physical contact in `[cM, M]`),
  `activation` (`c > 1/e`).  **No instance is constructed.**
* `eventual_exclusion_of_architecture` — the contract implies eventual exclusion from `M_geom`
  (through the frozen V9 graph-localization theorem);
* `killed_architecture_no_provider` — a killed architecture can never be reused as a provider;
* `kills_are_scoped` — the kills are architecture-scoped, not universal impossibility theorems:
  the killed list does not exhaust the tags, and nothing in the bank refutes the contract for a
  fresh tag;
* `graph_existence_frozen` — the V9 graph existence results remain valid (re-used verbatim);
* `currentArchitecture = none` — the current bank records no architecture.
-/

namespace Erdos287
namespace ResearchBankV11
namespace FiniteArchitectureFrontier

open ResearchBankV9 ResearchBankV9.GraphLocalization ResearchBankV9.AffineContact

/-- Architecture tags. -/
inductive ArchitectureTag
  | prescribedCRT
  | smallGraphNarrowSimplex
  | threeGroupBelow3
  | arbitraryFMoment
  | chenTuningBelow3
  | fresh (id : String)
  deriving DecidableEq, Repr

/-- The architectures killed in their stated scope. -/
def killedArchitectures : List ArchitectureTag :=
  [.prescribedCRT, .smallGraphNarrowSimplex, .threeGroupBelow3, .arbitraryFMoment,
    .chenTuningBelow3]

/-- **The OPEN finite-architecture contract** (never instantiated here). -/
structure FiniteArchitectureProvider (arch : ArchitectureTag) (c : ℝ) (M_geom : ℕ)
    (ai aj t : ℕ → ℕ) : Prop where
  notKilled : arch ∉ killedArchitectures
  realization : ∀ M ≥ M_geom, ai M < aj M ∧ Nat.gcd (ai M) (aj M) = aj M - ai M
  primeSupply : ∀ M ≥ M_geom, (F (ai M) (t M)).Prime ∧ (F (aj M) (t M)).Prime
  rigidity : ∀ M ≥ M_geom, C (M / F (ai M) (t M)) < (F (ai M) (t M) : ℤ) ∧
    C (M / F (aj M) (t M)) < (F (aj M) (t M) : ℤ)
  localization : ∀ M ≥ M_geom, c * M ≤ ((ai M / (aj M - ai M)) * F (aj M) (t M) : ℕ) ∧
    (ai M / (aj M - ai M)) * F (aj M) (t M) + 1 ≤ M
  activation : 1 / Real.exp 1 < c

/-- The contract yields useful edge data at every scale `M ≥ M_geom`. -/
def FiniteArchitectureProvider.edge {arch : ArchitectureTag} {c : ℝ} {M_geom : ℕ}
    {ai aj t : ℕ → ℕ} (h : FiniteArchitectureProvider arch c M_geom ai aj t) (M : ℕ)
    (hM : M ≥ M_geom) : UsefulEdgeData M c where
  ai := ai M
  aj := aj M
  t := t M
  hij := (h.realization M hM).1
  hg := (h.realization M hM).2
  rigid_i := ⟨(h.primeSupply M hM).1, (h.rigidity M hM).1⟩
  rigid_j := ⟨(h.primeSupply M hM).2, (h.rigidity M hM).2⟩
  lower := (h.localization M hM).1
  upper := (h.localization M hM).2

/-- **The contract implies eventual exclusion from `M_geom`.** -/
theorem eventual_exclusion_of_architecture {arch : ArchitectureTag} {c : ℝ} {M_geom : ℕ}
    {ai aj t : ℕ → ℕ} (h : FiniteArchitectureProvider arch c M_geom ai aj t) :
    Splice.EventualNoCounterexampleFrom M_geom := by
  intro A hA
  by_contra hge
  push_neg at hge
  exact no_counterexample_above_of_edge_supply h.activation (fun M hM => ⟨h.edge M hM⟩) hA hge

/-- **Killed architectures cannot be reused.** -/
theorem killed_architecture_no_provider {arch : ArchitectureTag} (hk : arch ∈ killedArchitectures)
    (c : ℝ) (M_geom : ℕ) (ai aj t : ℕ → ℕ) :
    ¬ FiniteArchitectureProvider arch c M_geom ai aj t :=
  fun h => h.notKilled hk

/-- **The kills are architecture-scoped**: some tag is not killed (so the killed list is not a
universal impossibility statement). -/
theorem kills_are_scoped : ∃ arch : ArchitectureTag, arch ∉ killedArchitectures :=
  ⟨.fresh "new", by decide⟩

/-- The V9 graph existence results remain valid (frozen, re-used verbatim). -/
theorem graph_existence_frozen :
    Gates.AlphaEq 145 38 ∧ Gates.ChiFEq 145 38 (145 / 39) ∧ Gates.AlphaEq 13 3 :=
  ⟨Gates.gate_145_38.1, Gates.gate_145_38.2, Gates.gate_13_3.1⟩

/-- A recorded architecture (data + proof of the contract). -/
structure ArchitectureRecord where
  arch : ArchitectureTag
  c : ℝ
  M_geom : ℕ
  ai : ℕ → ℕ
  aj : ℕ → ℕ
  t : ℕ → ℕ
  provider : FiniteArchitectureProvider arch c M_geom ai aj t

/-- **The current bank records no finite architecture.** -/
def currentArchitecture : Option ArchitectureRecord := none

theorem currentArchitecture_eq_none : currentArchitecture = none := rfl

/-- A recorded architecture is never a killed one. -/
theorem record_not_killed (r : ArchitectureRecord) : r.arch ∉ killedArchitectures :=
  r.provider.notKilled

end FiniteArchitectureFrontier
end ResearchBankV11
end Erdos287
