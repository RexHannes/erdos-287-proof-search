import Mathlib

/-!
# Erdős #287 — master physical source: **interface only**

This module is part of the append-only master-source frontier bank.  It contains **no**
new analytic claim about Erdős #287 and it does **not** construct the missing master
physical source.

What is provided:

* `Erdos287.MasterSource.unprojectedSource` — a *finite test model* of an unprojected
  source, `∑_ξ weight ξ · kernel ξ`, with its elementary deterministic consequences;
* `Erdos287.MasterSource.SourceSpec` — the *demanded* data an eventual realisation must
  match (authoritative parent expression, the required physical weight and kernel, the
  exact coefficient, the shared-gcd coordinate, the required outer variables);
* `Erdos287.MasterSource.MasterPhysicalSourceRealisation` — the realisation interface.
  It is a `structure`, **left uninhabited**: nothing in this repository constructs a term
  of it, and no `axiom` supplies one;
* `Erdos287.MasterSource.SourceDictionary` — the strictly weaker notion of a populated
  *dictionary*, together with the kernel-checked firewall showing that a dictionary is
  **not** a realisation (an explicit finite countermodel where the dictionary exists but
  the claimed physical equality fails).

The finite test model is a *model*; it is never claimed to be the physical theorem.  The
physical statement is expressed by the uninhabited interface, not by the finite model.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace MasterSource

/-! ## §1  The finite test model of an unprojected source -/

/-- **Finite test model.**  The unprojected source attached to a finite physical index
family, `∑_{ξ ∈ I} weight ξ · kernel ξ`.  This is a finite surrogate, not the physical
asymptotic source. -/
noncomputable def unprojectedSource {ι : Type*} (I : Finset ι) (weight kernel : ι → ℂ) : ℂ :=
  ∑ xi ∈ I, weight xi * kernel xi

@[simp] theorem unprojectedSource_empty {ι : Type*} (weight kernel : ι → ℂ) :
    unprojectedSource (∅ : Finset ι) weight kernel = 0 := by
  simp [unprojectedSource]

theorem unprojectedSource_insert {ι : Type*} [DecidableEq ι] {I : Finset ι} {a : ι}
    (ha : a ∉ I) (weight kernel : ι → ℂ) :
    unprojectedSource (insert a I) weight kernel
      = weight a * kernel a + unprojectedSource I weight kernel := by
  simp [unprojectedSource, Finset.sum_insert ha]

/-- Deterministic triangle bound for the finite test model. -/
theorem norm_unprojectedSource_le {ι : Type*} (I : Finset ι) (weight kernel : ι → ℂ) :
    ‖unprojectedSource I weight kernel‖ ≤ ∑ xi ∈ I, ‖weight xi‖ * ‖kernel xi‖ := by
  refine (norm_sum_le _ _).trans_eq ?_
  exact Finset.sum_congr rfl fun xi _ => by rw [norm_mul]

/-- Deterministic mass bound: nuclear weight mass times a uniform kernel bound. -/
theorem norm_unprojectedSource_le_mass {ι : Type*} (I : Finset ι) (weight kernel : ι → ℂ)
    (K : ℝ) (hK : ∀ xi ∈ I, ‖kernel xi‖ ≤ K) :
    ‖unprojectedSource I weight kernel‖ ≤ (∑ xi ∈ I, ‖weight xi‖) * K := by
  refine (norm_unprojectedSource_le I weight kernel).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun xi hxi => ?_
  exact mul_le_mul_of_nonneg_left (hK xi hxi) (norm_nonneg _)

/-! ## §2  What a realisation must match -/

/-- **The demanded source data.**  A `SourceSpec` records what an eventual master
physical source realisation has to reproduce *exactly*: the value of the authoritative
parent expression, the required physical weight and kernel families, the exact
coefficient, the shared-gcd coordinate, and the outer variables that must occur in the
physical index family. -/
structure SourceSpec where
  /-- Value of the authoritative parent expression the source must be identified with. -/
  parent : ℂ
  /-- The physical weight family demanded by the parent expression. -/
  requiredWeight : ℕ → ℂ
  /-- The physical kernel family demanded by the parent expression. -/
  requiredKernel : ℕ → ℂ
  /-- The exact coefficient the physical weights must factor through. -/
  coefficient : ℂ
  /-- The shared-gcd coordinate carried by the source. -/
  sharedGcd : ℕ
  /-- The outer variables that must be present in the physical index family. -/
  outerVars : Finset ℕ

/-- **The master physical source realisation interface.**

A term of this type is exactly what is missing: an identification of the physical,
unprojected master source with the authoritative parent expression, carrying the exact
physical index family, the exact coefficient factorisation, a *positive* shared-gcd
coordinate together with the source coprimality data, and all required outer variables.

**This structure is deliberately left uninhabited.**  No constructor application for it
occurs anywhere in this repository, and no axiom supplies one. -/
structure MasterPhysicalSourceRealisation (spec : SourceSpec) where
  /-- The exact physical index family. -/
  index : Finset ℕ
  /-- A realisation carries indices. -/
  index_nonempty : index.Nonempty
  /-- All required outer variables occur. -/
  outerVars_present : spec.outerVars ⊆ index
  /-- The normalised local profile through which the exact coefficient acts. -/
  profile : ℕ → ℂ
  /-- Exact coefficient identification. -/
  coefficient_factorisation :
    ∀ xi ∈ index, spec.requiredWeight xi = spec.coefficient * profile xi
  /-- The shared-gcd coordinate is positive (a genuine physical coordinate). -/
  sharedGcd_pos : 0 < spec.sharedGcd
  /-- Source coprimality data. -/
  coprimality : ∀ xi ∈ index, Nat.Coprime xi spec.sharedGcd
  /-- **Identification with the authoritative parent expression.** -/
  realises :
    unprojectedSource index spec.requiredWeight spec.requiredKernel = spec.parent

/-- Alias used in the source-census prose. -/
abbrev PhysicalSourceRealisation (spec : SourceSpec) : Type :=
  MasterPhysicalSourceRealisation spec

/-- The identification field is load-bearing: from a realisation one really recovers the
parent expression as the finite unprojected source over the physical index family. -/
theorem MasterPhysicalSourceRealisation.parent_eq {spec : SourceSpec}
    (R : MasterPhysicalSourceRealisation spec) :
    spec.parent = unprojectedSource R.index spec.requiredWeight spec.requiredKernel :=
  R.realises.symm

/-- A realisation forces the weights on the index family to factor through the exact
coefficient; in particular a zero coefficient forces a zero parent. -/
theorem MasterPhysicalSourceRealisation.parent_eq_zero_of_coefficient_zero
    {spec : SourceSpec} (R : MasterPhysicalSourceRealisation spec)
    (hc : spec.coefficient = 0) : spec.parent = 0 := by
  rw [R.parent_eq, unprojectedSource]
  refine Finset.sum_eq_zero fun xi hxi => ?_
  rw [R.coefficient_factorisation xi hxi, hc, zero_mul, zero_mul]

/-! ## §3  Dictionaries are not realisations -/

/-- **A source dictionary.**  A dictionary merely *names* a physical index family and
records that it is populated.  It contains **no** identification with the parent
expression, no coefficient identity, no shared-gcd positivity and no coprimality data. -/
structure SourceDictionary (spec : SourceSpec) where
  /-- The named index family. -/
  index : Finset ℕ
  /-- The dictionary is populated. -/
  index_nonempty : index.Nonempty

/-- Every realisation yields a dictionary.  The converse direction is refuted below, so
the two notions are related by a strictly one-way map. -/
def MasterPhysicalSourceRealisation.toDictionary {spec : SourceSpec}
    (R : MasterPhysicalSourceRealisation spec) : SourceDictionary spec :=
  ⟨R.index, R.index_nonempty⟩

/-- The finite countermodel spec: the parent expression is `1`, but the required physical
weight family vanishes identically.  Any claimed realisation would have to prove `0 = 1`.
This is the formal content of the lesson that a *completed source* structure can be a
populated dictionary without the parent expression ever having been constructed. -/
def vanishingWeightSpec : SourceSpec where
  parent := 1
  requiredWeight := fun _ => 0
  requiredKernel := fun _ => 1
  coefficient := 1
  sharedGcd := 1
  outerVars := ∅

/-- The countermodel dictionary is populated. -/
def vanishingWeightDictionary : SourceDictionary vanishingWeightSpec :=
  ⟨{0}, ⟨0, by simp⟩⟩

/-- **Firewall (physical equality fails).**  For `vanishingWeightSpec` the dictionary is
populated, yet no physical source realisation exists. -/
theorem no_realisation_vanishingWeightSpec :
    ¬ Nonempty (MasterPhysicalSourceRealisation vanishingWeightSpec) := by
  rintro ⟨R⟩
  have h := R.realises
  simp only [unprojectedSource, vanishingWeightSpec, zero_mul, Finset.sum_const_zero] at h
  exact zero_ne_one h

/-- The countermodel spec with a degenerate shared-gcd coordinate. -/
def zeroGcdSpec : SourceSpec where
  parent := 0
  requiredWeight := fun _ => 0
  requiredKernel := fun _ => 0
  coefficient := 0
  sharedGcd := 0
  outerVars := ∅

/-- **Firewall (degenerate shared-gcd coordinate).**  A realisation must carry a positive
shared-gcd coordinate, so specs with `sharedGcd = 0` admit none — even though their
dictionaries are populated. -/
theorem no_realisation_zeroGcdSpec :
    ¬ Nonempty (MasterPhysicalSourceRealisation zeroGcdSpec) := by
  rintro ⟨R⟩
  exact absurd R.sharedGcd_pos (by simp [zeroGcdSpec])

/-- **`sourceDictionary_ne_physicalRealisation`.**  There is a spec whose dictionary is
inhabited while its physical source realisation type is empty.  Hence there is no
coercion, no definitional identification and no implication from
`SourceDictionary` to `MasterPhysicalSourceRealisation`. -/
theorem sourceDictionary_ne_physicalRealisation :
    ∃ spec : SourceSpec,
      Nonempty (SourceDictionary spec) ∧
        ¬ Nonempty (MasterPhysicalSourceRealisation spec) :=
  ⟨vanishingWeightSpec, ⟨vanishingWeightDictionary⟩, no_realisation_vanishingWeightSpec⟩

/-- **`dictionary_population_does_not_construct_parent`.**  Sharpened form: a populated
dictionary carries no information at all about the parent expression — the same
dictionary data is compatible with specs that do and specs that do not admit a
realisation, and in the exhibited case the realisation type is empty. -/
theorem dictionary_population_does_not_construct_parent
    (D : SourceDictionary vanishingWeightSpec) :
    D.index.Nonempty ∧ ¬ Nonempty (MasterPhysicalSourceRealisation vanishingWeightSpec) :=
  ⟨D.index_nonempty, no_realisation_vanishingWeightSpec⟩

/-! ## §4  A realisable spec exists (the interface is not vacuous by construction)

The interface would be worthless if it were unsatisfiable for *every* spec: a firewall
must separate two genuinely possible situations.  The following finite spec is realisable,
which shows that `MasterPhysicalSourceRealisation` is a real condition and not a disguised
`False`.  It is a **toy finite model**, and is emphatically *not* the physical
Erdős #287 source: no claim about the master physical source follows from it. -/

/-- A toy finite spec: one index, weight `1`, kernel `1`, parent `1`. -/
def toySpec : SourceSpec where
  parent := 1
  requiredWeight := fun _ => 1
  requiredKernel := fun _ => 1
  coefficient := 1
  sharedGcd := 1
  outerVars := ∅

/-- The toy spec is realisable, so the realisation interface is a genuine condition. -/
def toyRealisation : MasterPhysicalSourceRealisation toySpec where
  index := {0}
  index_nonempty := ⟨0, by simp⟩
  outerVars_present := by simp [toySpec]
  profile := fun _ => 1
  coefficient_factorisation := by intro xi _; simp [toySpec]
  sharedGcd_pos := by simp [toySpec]
  coprimality := by intro xi _; simp [toySpec, Nat.Coprime]
  realises := by simp [unprojectedSource, toySpec]

/-- **`toy_model_is_not_the_physical_source`.**  Explicit scope marker: the realisable toy
spec is a different spec from the countermodel spec, and realising the former yields no
realisation of the latter. -/
theorem toy_model_is_not_the_physical_source :
    Nonempty (MasterPhysicalSourceRealisation toySpec) ∧
      ¬ Nonempty (MasterPhysicalSourceRealisation vanishingWeightSpec) :=
  ⟨⟨toyRealisation⟩, no_realisation_vanishingWeightSpec⟩

end MasterSource
end Erdos287
