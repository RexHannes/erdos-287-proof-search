import RequestProject.CurrentProgramme.Erdos287K0SP2FourClassPartition

/-!
# The regular Perron parent — interface only, and the reconstruction firewall

```
REGULAR PERRON PARENT INTERFACE     : DEFINED (definition only)
REGULAR PERRON ANALYTIC INPUT       : UNINHABITED
PERRON MAIN / BOUNDARY / TRUNCATION : separate uninhabited interfaces
```

This module is **append-only**.

**§1 — the coefficient interface.**  The intended parent coefficient is

```
F_z^{reg}(n) = 1_R(n) · n^{γ* z} · ∏_{p ∣ n} (1 − p^{−z}).
```

Complex exponentiation `n^{γ* z}` has no clean executable definition here, so the
object is carried as an **abstract coefficient structure with explicit
reconstruction fields**: a regular-support predicate, an abstract scale factor,
an abstract local factor, and the two identities that pin the shape (vanishing
off the regular set, and the Euler-product reconstruction on it).

**§2 — the parent analytic input.**  `RegularPerronSmoothMobiusCorrelationInput`
states the exact remaining analytic object

```
∑_{s = ±1} ∫ |C_s^{reg}(X; c + iτ)| / |c + iτ| dτ = o(X / log X)
```

in the form of an **explicit fixed-budget sufficient inequality**.  It is
**left uninhabited**: nothing in this repository constructs one, and
`regularPerronInput_not_inhabited_here` exhibits data refuting it.

**§3 — the Perron reconstruction firewall.**  `PerronMainInput`,
`PerronBoundaryInput` and `PerronTruncationInput` are three *separate*
interfaces.  Only the finite algebraic reassembly

```
regular source = Perron parent + boundary + truncation
```

is proved, and only *conditionally* on the three explicit inputs.  No contour
estimate is formalised.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos287
namespace RegularPerron

/-! ## §1.  The abstract regular coefficient interface -/

/-- **`RegularPerronCoefficients`** — the abstract stand-in for

```
F_z^{reg}(n) = 1_R(n) · n^{γ* z} · ∏_{p ∣ n} (1 − p^{−z}).
```

The two reconstruction fields pin exactly the shape of the coefficient; the scale factor
`scale n z` (intended `n^{γ* z}`) and the local factor `local_ p z` (intended `p^{−z}`)
are abstract, so no complex exponentiation is required. -/
structure RegularPerronCoefficients where
  /-- The regular support `R`. -/
  Reg : ℕ → Prop
  /-- The coefficient itself. -/
  F : ℕ → ℂ → ℂ
  /-- The abstract scale factor, intended `n^{γ* z}`. -/
  scale : ℕ → ℂ → ℂ
  /-- The abstract local factor, intended `p^{−z}`. -/
  local_ : ℕ → ℂ → ℂ
  /-- **Reconstruction field 1**: the coefficient vanishes off the regular support. -/
  vanish_off_reg : ∀ n z, ¬ Reg n → F n z = 0
  /-- **Reconstruction field 2**: on the regular support the coefficient is the scale
  factor times the Euler product over the prime support. -/
  euler_on_reg : ∀ n z, Reg n → F n z = scale n z * ∏ p ∈ n.primeFactors, (1 - local_ p z)

namespace RegularPerronCoefficients

variable (c : RegularPerronCoefficients)

/-- The finite correlation of the parent coefficient against a weight on a finite row set. -/
noncomputable def correlation (S : Finset ℕ) (w : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ n ∈ S, w n * c.F n z

/-- **Support identity.**  The parent correlation only sees the regular rows. -/
theorem correlation_eq_filter (S : Finset ℕ) (w : ℕ → ℂ) (z : ℂ) :
    c.correlation S w z = c.correlation (S.filter c.Reg) w z := by
  unfold correlation
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : c.Reg n
  · simp [h]
  · simp [h, c.vanish_off_reg n z h]

/-- A row outside the regular support contributes nothing. -/
theorem correlation_insert_irregular {S : Finset ℕ} {n : ℕ} (hn : n ∉ S) (hreg : ¬ c.Reg n)
    (w : ℕ → ℂ) (z : ℂ) :
    c.correlation (insert n S) w z = c.correlation S w z := by
  unfold correlation
  rw [Finset.sum_insert hn, c.vanish_off_reg n z hreg]
  ring

end RegularPerronCoefficients

/-! ## §2.  The parent analytic input — left uninhabited -/

/-- **`RegularPerronSmoothMobiusCorrelationInput`** — `OPEN ANALYTIC / UNINHABITED`.

The exact remaining analytic object of the K0-SP2 programme:

```
∑_{s = ±1} ∫ |C_s^{reg}(X; c + iτ)| / |c + iτ| dτ = o(X / log X),
```

stated as an **explicit fixed-budget sufficient inequality**: the total two-sign
contour mass at scale `X` is at most `κ · X / (log X)^{1+η}` with `η > 0` and `κ ≥ 0`.

The τ-integral is carried as an abstract nonnegative function `mass : Bool → ℕ → ℝ`
(one value per sign and scale), because no contour integration is formalised here.

**Nothing in this repository inhabits this structure.** -/
structure RegularPerronSmoothMobiusCorrelationInput where
  /-- The abstract two-sign contour mass at each scale. -/
  mass : Bool → ℕ → ℝ
  /-- The fixed budget constant. -/
  kappa : ℝ
  /-- The saving exponent. -/
  eta : ℝ
  /-- The budget constant is nonnegative. -/
  kappa_nonneg : 0 ≤ kappa
  /-- The saving is genuine. -/
  eta_pos : 0 < eta
  /-- The mass is nonnegative. -/
  mass_nonneg : ∀ s X, 0 ≤ mass s X
  /-- The fixed-budget bound.  **Not proved anywhere in this repository.** -/
  budget : ∀ X : ℕ, 3 ≤ X →
    mass true X + mass false X ≤ kappa * (X : ℝ) / (Real.log X) ^ (1 + eta)

/-- **`regularPerronInput_not_inhabited_here`.**  `KERNEL-PROVED`.

The parent analytic input is a genuine restriction: an explicit choice of the abstract
mass refutes it.  Nothing in this repository constructs one. -/
theorem regularPerronInput_not_inhabited_here :
    ¬ ∃ I : RegularPerronSmoothMobiusCorrelationInput,
        I.mass = (fun _ _ => 1) ∧ I.kappa = 0 := by
  rintro ⟨I, hm, hk⟩
  have h := I.budget 3 le_rfl
  rw [hm, hk] at h
  norm_num at h

/-! ## §3.  The Perron reconstruction firewall -/

/-- **`PerronMainInput`** — `OPEN ANALYTIC / UNINHABITED`.  The main contour term. -/
structure PerronMainInput where
  /-- The value produced by the main contour term. -/
  value : ℂ
  /-- Its certified size at the working scale. -/
  size : ℝ
  /-- The size is an upper bound for the modulus. -/
  bound : ‖value‖ ≤ size

/-- **`PerronBoundaryInput`** — `OPEN ANALYTIC / UNINHABITED`.  The boundary term. -/
structure PerronBoundaryInput where
  /-- The value produced by the boundary term. -/
  value : ℂ
  /-- Its certified size at the working scale. -/
  size : ℝ
  /-- The size is an upper bound for the modulus. -/
  bound : ‖value‖ ≤ size

/-- **`PerronTruncationInput`** — `OPEN ANALYTIC / UNINHABITED`.  The truncation term. -/
structure PerronTruncationInput where
  /-- The value produced by the truncation term. -/
  value : ℂ
  /-- Its certified size at the working scale. -/
  size : ℝ
  /-- The size is an upper bound for the modulus. -/
  bound : ‖value‖ ≤ size

/-- **`PerronReconstruction`** — the *finite, algebraic* reassembly schema

```
regular source = Perron parent + boundary + truncation,
```

carried as an explicit identity between the regular source value and the three
inputs.  The identity is a **hypothesis**, not a theorem: the analytic contour shift
that would produce it is not formalised. -/
structure PerronReconstruction where
  /-- The regular source value being reconstructed. -/
  regularValue : ℂ
  /-- The main term input. -/
  main : PerronMainInput
  /-- The boundary term input. -/
  boundary : PerronBoundaryInput
  /-- The truncation term input. -/
  truncation : PerronTruncationInput
  /-- The reconstruction identity. -/
  decomposition : regularValue = main.value + boundary.value + truncation.value

/-- **`perron_reconstruction_identity`.**  `KERNEL-PROVED CONDITIONAL`.

Given the three explicit Perron inputs and the reconstruction identity, the regular
source is exactly their sum.  This is pure bookkeeping; it asserts nothing analytic. -/
theorem perron_reconstruction_identity (r : PerronReconstruction) :
    r.regularValue = r.main.value + r.boundary.value + r.truncation.value :=
  r.decomposition

/-- **`perron_reconstruction_triangle`.**  `KERNEL-PROVED CONDITIONAL`.

The only inequality that the reconstruction schema supports: the modulus of the regular
source is at most the sum of the three certified sizes.  It is available **only after**
the parent identity has been used. -/
theorem perron_reconstruction_triangle (r : PerronReconstruction) :
    ‖r.regularValue‖ ≤ r.main.size + r.boundary.size + r.truncation.size := by
  rw [r.decomposition]
  have hab := norm_add_le (r.main.value + r.boundary.value) r.truncation.value
  have hbc := norm_add_le r.main.value r.boundary.value
  have h1 := r.main.bound
  have h2 := r.boundary.bound
  have h3 := r.truncation.bound
  linarith

/-- **`perron_reconstruction_not_inhabited_here`.**  `KERNEL-PROVED`.

The reconstruction bundle is a genuine restriction: the decomposition identity can fail. -/
theorem perron_reconstruction_not_inhabited_here :
    ¬ ∃ r : PerronReconstruction,
        r.regularValue = 1 ∧ r.main.value = 0 ∧ r.boundary.value = 0 ∧
          r.truncation.value = 0 := by
  rintro ⟨r, h0, h1, h2, h3⟩
  have := r.decomposition
  rw [h0, h1, h2, h3] at this
  norm_num at this

end RegularPerron
end Erdos287
