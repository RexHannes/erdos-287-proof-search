import RequestProject.CurrentProgramme.Run1BCenteringAndSourceRouter

/-!
# RUN1B / d*wp provider — §9  the RUN1B conditional compiler

```
Run1BSourceExhaustiveInput                       : finite/source, INHABITED (kernel-proved)
PhysicalQMuPrimeReciprocalPaperInput             : PAPER_CLOSED_EXTERNAL, never proved here
CenteringLocalInput                              : explicit hypothesis
exhaustive + paper provider + centering/local
  → Run1BConclusion                              : CONDITIONAL KERNEL-PROVED
```

The two inputs are kept **separate** on purpose: the source-exhaustiveness statement is
finite and is proved here; the analytic `d·w'` provider is an external paper result and is
*never* labelled kernel-proved.  It stays visible in the assumption chain of every theorem
that uses it.

This module is **append-only** and project-neutral: it mentions no downstream project.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Run1B
namespace Compiler

open Run1B.Source Run1B.EffectiveModulus Run1B.SourceRouter

/-! ## §9.1  The finite source-exhaustiveness input -/

/-- **`Run1BSourceExhaustiveInput`** — the *finite* part: routing of the 1B source classes is
total, deterministic and every class is reachable. -/
structure Run1BSourceExhaustiveInput : Prop where
  /-- Routing is total. -/
  routing_total : ∀ d : SourceDatum, ∃ c : SourceClass, route d = c
  /-- Routing is deterministic. -/
  routing_unique : ∀ (d : SourceDatum) (c c' : SourceClass), route d = c → route d = c' → c = c'
  /-- Every class is reachable, so no class is a vacuous label. -/
  classes_reachable : ∀ c : SourceClass, ∃ d : SourceDatum, route d = c

/-- **`run1BSourceExhaustiveInput_inhabited`.**  `KERNEL-PROVED`.  The finite input holds. -/
theorem run1BSourceExhaustiveInput_inhabited : Run1BSourceExhaustiveInput where
  routing_total := fun d => ⟨route d, rfl⟩
  routing_unique := fun _ _ _ h h' => h ▸ h'
  classes_reachable := route_is_surjective

/-! ## §9.2  The principal (`h = 0`) part of a `d·w'` source -/

/-- The `h = 0` principal part of the `d·w'` bilinear sum at the effective modulus. -/
noncomputable def dwpPrincipal (s : DwpSource) : ℂ :=
  (1 / ((rSharp s.A s.r : ℕ) : ℂ)) * ∑ a ∈ s.Dset, ∑ b ∈ s.Wset, s.alpha a * s.beta b

/-- The centred `d·w'` bilinear sum. -/
noncomputable def dwpCentred (s : DwpSource) : ℂ := s.dwpSum - dwpPrincipal s

/-- **`dwp_decomposition`.**  `KERNEL-PROVED`.  The principal term is *retained*, never
deleted: the source sum is exactly principal plus centred. -/
theorem dwp_decomposition (s : DwpSource) : s.dwpSum = dwpPrincipal s + dwpCentred s := by
  unfold dwpCentred
  ring

/-! ## §9.3  The external analytic provider and the local/centering input -/

/-- **`PhysicalQMuPrimeReciprocalPaperInput`** — `PAPER_CLOSED_EXTERNAL`.

The literal analytic `d·w'` provider: a bound for the *centred* bilinear sum of a physical
`q = d w'` source.  It is an explicit hypothesis, never a Lean theorem here. -/
structure PhysicalQMuPrimeReciprocalPaperInput (s : DwpSource) (bound : ℝ) : Prop where
  /-- The paper-level saving for the centred bilinear sum. -/
  saving : ‖dwpCentred s‖ ≤ bound

/-- **`CenteringLocalInput`** — the centering / local-term input: a bound for the retained
principal term.  Also an explicit hypothesis. -/
structure CenteringLocalInput (s : DwpSource) (localBound : ℝ) : Prop where
  /-- The principal term is bounded. -/
  principal : ‖dwpPrincipal s‖ ≤ localBound

/-- **`paperInput_is_a_genuine_constraint`.**  `KERNEL-PROVED` counterguard: the analytic
provider is not a `True`-like proposition. -/
theorem paperInput_is_a_genuine_constraint (s : DwpSource) :
    ¬ PhysicalQMuPrimeReciprocalPaperInput s (-1) := by
  intro h
  exact absurd h.saving
    (not_le.mpr (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (norm_nonneg _)))

/-! ## §9.4  The conditional compiler -/

/-- The RUN1B conclusion for a family of `d·w'` sources: each source sum obeys the combined
paper-plus-local bound. -/
def Run1BConclusion {ι : Type} (sources : ι → DwpSource) (bound localBound : ℝ) : Prop :=
  ∀ i : ι, ‖(sources i).dwpSum‖ ≤ bound + localBound

/-- **`run1B_conditional_compiler`.**  `CONDITIONAL KERNEL-PROVED`.

```
source exhaustiveness  +  paper analytic provider  +  centering/local input
      →  Run1BConclusion.
```

The proof is the triangle inequality applied to the kernel-proved decomposition; the analytic
content is entirely carried by the two explicit hypotheses. -/
theorem run1B_conditional_compiler {ι : Type} (sources : ι → DwpSource) (bound localBound : ℝ)
    (_exhaustive : Run1BSourceExhaustiveInput)
    (paper : ∀ i : ι, PhysicalQMuPrimeReciprocalPaperInput (sources i) bound)
    (centering : ∀ i : ι, CenteringLocalInput (sources i) localBound) :
    Run1BConclusion sources bound localBound := by
  intro i
  rw [dwp_decomposition (sources i)]
  refine le_trans (norm_add_le _ _) ?_
  have h1 := (centering i).principal
  have h2 := (paper i).saving
  linarith

/-- **`run1B_conclusion_needs_the_analytic_provider`.**  `KERNEL-PROVED` counterguard.

The finite source-exhaustiveness input alone does **not** give the conclusion: at the explicit
sample source with `bound = localBound = 0` the conclusion is false, while the finite input
holds. -/
theorem run1B_conclusion_needs_the_analytic_provider :
    Run1BSourceExhaustiveInput ∧
      ¬ Run1BConclusion (fun _ : Unit => sampleSource) 0 0 := by
  refine ⟨run1BSourceExhaustiveInput_inhabited, ?_⟩
  intro h
  have h1 := h ()
  rw [sampleSource_dwpSum] at h1
  simp only [norm_one, add_zero] at h1
  linarith

end Compiler
end Run1B
