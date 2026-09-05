import RequestProject.CurrentProgramme.Erdos287September4BsrcLocalMobiusCollapse

/-!
# Erdős #287 — September-4 signed-floor bank, §5: the boundary divisor lattice

```
BOUNDARY DATATYPE (7 source-native causes)      : BUILT
BOUNDARY RECORD (reconstructs the omitted fibre): BUILT + KERNEL-PROVED reconstruction
INTERIOR CONSUMPTION BY THE MÖBIUS COLLAPSE     : KERNEL-PROVED
INTERIOR-OR-BOUNDARY DICHOTOMY                  : KERNEL-PROVED
PHYSICAL CAUSE-LIST EXHAUSTIVENESS              : PARTIAL (obligation isolated, §5.5)
COLLAPSE ON A TRUNCATED FIBRE                   : REFUTED (firewall, §5.4)
```

This module is **append-only**.  Its purpose is the exact distinction

    complete divisor cube      → interior local Möbius collapse (§4);
    incomplete/truncated cube  → boundary record.

A *divisor assignment* for a squarefree modulus `q` is a point `s` of the divisor cube
`q.primeFactors.powerset` (equivalently the divisor `d = ∏ s`).  A *physical selector*
`sel : Finset ℕ → Bool` says which assignments the physical source actually keeps.  The
fibre is **complete/interior** exactly when the selector keeps the whole cube; then §4
consumes it exactly.  Otherwise at least one assignment is omitted, and the omission is
recorded by a `BoundaryRecord` carrying enough data to reconstruct it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287
namespace September4BoundaryLattice

open September4BsrcCollapse

/-! ## §5.1  The boundary datatype -/

/-- The source-native boundary causes: the reasons a divisor-assignment fibre can fail to be
the complete cube.  Each constructor names an actual truncation of the physical source; no
cause without a source meaning is introduced. -/
inductive BoundaryKind
  /-- The `γ`-cutoff `d ≤ n^γ` truncates the fibre from above. -/
  | gammaUpper
  /-- The doubled cutoff `2d ≤ n^γ` (the `T²` comparison) truncates the fibre. -/
  | gammaDouble
  /-- Lower edge of the two-high shell. -/
  | twoHighShellLower
  /-- Upper edge of the two-high shell. -/
  | twoHighShellUpper
  /-- The one-high collar `d ≤ n^γ < 2d`. -/
  | oneHighCollar
  /-- Termination caused by a repeated high prime (loss of squarefreeness). -/
  | repeatedHighTermination
  /-- The canonical `n^ν` split threshold. -/
  | canonicalThreshold
  deriving DecidableEq, Fintype, Repr

/-- The parity / squarefreeness metadata of the physical source state at a boundary. -/
structure SourceState where
  /-- Is the modulus `d` odd? -/
  dOdd : Bool
  /-- Is the modulus `d` squarefree? -/
  dSquarefree : Bool
  /-- The high depth `j = ω(d_high)` of the active `g`-state. -/
  highDepth : ℕ
  deriving DecidableEq, Repr

/-- A boundary record: the data needed to reconstruct one omitted (or non-constant)
divisor-assignment fibre. -/
structure BoundaryRecord where
  /-- The modulus whose divisor cube is truncated. -/
  q : ℕ
  /-- The omitted divisor `d = ∏ s` (for squarefree `q` this determines the cube point). -/
  d : ℕ
  /-- Which source truncation caused the omission. -/
  kind : BoundaryKind
  /-- Lower endpoint of the `L = log X` interval on which the record is charged. -/
  LLower : ℚ
  /-- Upper endpoint of that interval. -/
  LUpper : ℚ
  /-- The exact rational coefficient carried by the omitted assignment. -/
  coefficient : ℚ
  /-- Parity / squarefreeness metadata of the source state. -/
  state : SourceState
  deriving Repr

/-! ## §5.2  Fibres, selectors, and interiority -/

/-- The exact term of the divisor cube at the assignment `s`. -/
def cubeTerm (Bloc bloc : ℕ → ℚ) (q : ℕ) (s : Finset ℕ) : ℚ :=
  (moebius (∏ p ∈ s, p) : ℚ) * Bsrc Bloc (∏ p ∈ s, p) * beta bloc (q / ∏ p ∈ s, p)

/-- A physical fibre: a modulus together with the selector actually applied to its divisor
cube. -/
structure Fibre where
  /-- The modulus. -/
  q : ℕ
  /-- The physical selector on divisor assignments. -/
  sel : Finset ℕ → Bool

/-- The fibre is **interior** (complete) when the selector is constantly `true` on the whole
divisor cube. -/
def IsInterior (F : Fibre) : Prop := ∀ s ∈ divisorCube F.q, F.sel s = true

instance (F : Fibre) : Decidable (IsInterior F) := by
  unfold IsInterior; infer_instance

/-- The selector-weighted fibre sum. -/
def fibreSum (Bloc bloc : ℕ → ℚ) (F : Fibre) : ℚ :=
  ∑ s ∈ divisorCube F.q, (if F.sel s then cubeTerm Bloc bloc F.q s else 0)

/-! ## §5.3  Interior consumption -/

/-- **`interior_consumed`.**  `KERNEL-PROVED`.  Every *complete* divisor assignment is
consumed by the interior local Möbius collapse of §4: the selector-weighted fibre sum of an
interior fibre is exactly the collapsed local product. -/
theorem interior_consumed (Bloc bloc : ℕ → ℚ) (F : Fibre) (hq : Squarefree F.q)
    (hint : IsInterior F) :
    fibreSum Bloc bloc F = ∏ p ∈ F.q.primeFactors, (bloc p - Bloc p) := by
  classical
  rw [fibreSum, Finset.sum_congr rfl (fun s hs => by rw [if_pos (hint s hs)])]
  exact cubeLocalMobiusCollapse Bloc bloc hq

/-- **`interior_or_boundary`.**  `KERNEL-PROVED`.  Exhaustive dichotomy for a divisor
assignment fibre: either it is interior — and then it is consumed by
`interiorLocalMobiusCollapse45` (via `cubeLocalMobiusCollapse`) — or some cube point is
omitted, and that omission is recorded by a `BoundaryRecord` from which the omitted
assignment can be reconstructed (`rec.d.primeFactors = s`). -/
theorem interior_or_boundary (Bloc bloc : ℕ → ℚ) (F : Fibre) (hq : Squarefree F.q)
    (cause : Finset ℕ → BoundaryKind) (Llo Lhi : Finset ℕ → ℚ) (state : Finset ℕ → SourceState) :
    (fibreSum Bloc bloc F = ∏ p ∈ F.q.primeFactors, (bloc p - Bloc p)) ∨
      (∃ s ∈ divisorCube F.q, F.sel s = false ∧
        ∃ rec : BoundaryRecord,
          rec.q = F.q ∧ rec.d = ∏ p ∈ s, p ∧ rec.d.primeFactors = s ∧
            rec.kind = cause s ∧ rec.LLower = Llo s ∧ rec.LUpper = Lhi s ∧
            rec.coefficient = cubeTerm Bloc bloc F.q s ∧ rec.state = state s) := by
  classical
  by_cases hint : IsInterior F
  · exact Or.inl (interior_consumed Bloc bloc F hq hint)
  · refine Or.inr ?_
    simp only [IsInterior, not_forall] at hint
    obtain ⟨s, hs, hsel⟩ := hint
    have hsel' : F.sel s = false := by
      simpa using hsel
    have hprime : ∀ p ∈ s, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_powerset.1 hs hp)
    exact ⟨s, hs, hsel',
      ⟨F.q, ∏ p ∈ s, p, cause s, Llo s, Lhi s, cubeTerm Bloc bloc F.q s, state s⟩,
      rfl, rfl, Nat.primeFactors_prod hprime, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §5.4  Firewall: the collapse fails on a truncated fibre -/

/-- **`collapse_fails_on_truncated_fibre`.**  `KERNEL-PROVED` *counterexample*.  The interior
collapse is **not** available on an incomplete cube: for `q = 3` with the single assignment
`s = {3}` omitted, the selector-weighted fibre sum is `0` while the collapsed local product
is `−1`. -/
theorem collapse_fails_on_truncated_fibre :
    ∃ (Bloc bloc : ℕ → ℚ) (F : Fibre), Squarefree F.q ∧ ¬ IsInterior F ∧
      fibreSum Bloc bloc F ≠ ∏ p ∈ F.q.primeFactors, (bloc p - Bloc p) := by
  classical
  refine ⟨fun _ => 1, fun _ => 0, ⟨3, fun s => decide (s = (∅ : Finset ℕ))⟩,
    Nat.prime_three.squarefree, ?_, ?_⟩
  · intro hint
    have hmem : ({3} : Finset ℕ) ∈ divisorCube 3 := by
      simp [divisorCube, Nat.Prime.primeFactors Nat.prime_three]
    have := hint _ hmem
    simp at this
  · have hpf : Nat.primeFactors 3 = {3} := Nat.Prime.primeFactors Nat.prime_three
    have hcube : divisorCube 3 = {∅, {3}} := by
      rw [divisorCube, hpf]
      exact Finset.val_inj.mp rfl
    have hne : (∅ : Finset ℕ) ≠ ({3} : Finset ℕ) := by simp
    rw [fibreSum, hcube, Finset.sum_pair hne, hpf]
    norm_num [cubeTerm, Bsrc, beta, hpf]

/-! ## §5.5  The exhaustiveness obligation (PARTIAL) -/

/-- The physical-exhaustiveness obligation, isolated as a *statement*, not asserted.

`interior_or_boundary` is exhaustive as a **dichotomy** (interior, or an omitted assignment
carrying a record).  What is *not* certified here is that the seven constructors of
`BoundaryKind` are the complete list of physical causes of omission: that would require the
source-native cause classifier of the research run.  The obligation says exactly that every
omission of the supplied physical family `omitted` is produced by one of the seven causes,
through a *sound* classifier `cause` — i.e. one whose verdict is backed by the supplied
per-cause predicate `caused`. -/
def PhysicalBoundaryCauseComplete
    (omitted : Fibre → Finset ℕ → Prop) (caused : BoundaryKind → Fibre → Finset ℕ → Prop) : Prop :=
  ∀ F : Fibre, ∀ s ∈ divisorCube F.q, omitted F s → ∃ k : BoundaryKind, caused k F s

/-- **`boundary_cause_list_is_finite`.**  `KERNEL-PROVED`.  The cause list is a finite,
explicitly enumerated type with exactly seven constructors: the classification is a total
function into a finite alphabet, which is what the certificate checker of §8 consumes. -/
theorem boundary_cause_list_card : Fintype.card BoundaryKind = 7 := by decide

/-- **`exhaustiveness_is_relative`.**  `KERNEL-PROVED`.  Given *any* sound classifier, the
dichotomy of `interior_or_boundary` upgrades to: every unconsumed assignment carries at
least one boundary cause.  The soundness of a physical classifier is exactly the
`PhysicalBoundaryCauseComplete` obligation, which this development does **not** discharge. -/
theorem exhaustiveness_is_relative
    (omitted : Fibre → Finset ℕ → Prop) (caused : BoundaryKind → Fibre → Finset ℕ → Prop)
    (hcomplete : PhysicalBoundaryCauseComplete omitted caused)
    (F : Fibre) (s : Finset ℕ) (hs : s ∈ divisorCube F.q) (homit : omitted F s) :
    ∃ k : BoundaryKind, caused k F s :=
  hcomplete F s hs homit

end September4BoundaryLattice
end Erdos287
