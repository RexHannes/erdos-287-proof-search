import RequestProject.CurrentProgramme.Erdos287MasterSourceInterface

/-!
# Erdős #287 — proof-local Ω: abstract dyadic partition, local finiteness, insertion firewall

This module introduces a **new** namespace `Erdos287.ProofOmega`.  It is deliberately kept
disjoint from the historical `Ω_H` objects of the earlier banks: nothing here identifies
the proof-local partition with any previously banked `Ω`-object, and no theorem of this
file transports a property across that distinction.

Contents:

* `DyadicPartition` — an abstract dyadic partition-of-unity certificate: non-negative
  weights indexed by a finite set of dyadic scales, an **exact** partition of unity, local
  support, and bounded overlap (stated without decidability side conditions);
* deterministic kernel consequences: weights are `≤ 1`, the pointwise reconstruction
  identity, and the exact finite insertion identity
  `unprojected source = ∑_H projected source`;
* `dyadicLocalFiniteness` — the discrete support-geometry theorem: for a fixed positive
  `g`, at most **three** dyadic scales `H = 2^k` satisfy `g/2 ≤ H ≤ 2g`;
* `ProofOmegaInsertionInput` — the *physical* insertion interface, which requires an
  actual master physical source realisation carrying a positive shared-gcd coordinate.
  It is **left uninhabited**, and
  `abstractProofOmegaPartition_does_not_construct_physicalInsertion` records in the kernel
  that owning an abstract partition does not produce one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace ProofOmega

/-! ## §1  The abstract dyadic partition certificate -/

/-- **Abstract dyadic partition certificate.**  `weight k x` is the mass given to the
point `x` by the dyadic scale `2^k`.  The certificate demands an exact partition of unity
over a finite scale set, non-negativity, local support, and bounded overlap. -/
structure DyadicPartition (H : Type*) where
  /-- The finite set of dyadic scale exponents in play. -/
  scales : Finset ℕ
  /-- The partition weights. -/
  weight : ℕ → H → ℝ
  /-- Weights are non-negative. -/
  weight_nonneg : ∀ k x, 0 ≤ weight k x
  /-- **Exact** partition of unity. -/
  partition_of_unity : ∀ x, ∑ k ∈ scales, weight k x = 1
  /-- The local support of each scale. -/
  support : ℕ → Set H
  /-- Local support: outside its support a scale contributes nothing. -/
  weight_eq_zero_of_not_mem : ∀ k x, x ∉ support k → weight k x = 0
  /-- The overlap budget. -/
  overlapBound : ℕ
  /-- Bounded overlap: at each point at most `overlapBound` scales are active. -/
  bounded_overlap :
    ∀ x, ∃ T : Finset ℕ, T ⊆ scales ∧ T.card ≤ overlapBound ∧
      ∀ k ∈ scales, k ∉ T → weight k x = 0

namespace DyadicPartition

variable {H : Type*}

/-- Every individual weight is at most `1`. -/
theorem weight_le_one (P : DyadicPartition H) (k : ℕ) (hk : k ∈ P.scales) (x : H) :
    P.weight k x ≤ 1 := by
  have h := P.partition_of_unity x
  have : P.weight k x ≤ ∑ j ∈ P.scales, P.weight j x :=
    Finset.single_le_sum (fun j _ => P.weight_nonneg j x) hk
  rwa [h] at this

/-- The scale set of a partition is non-empty as soon as the base type is. -/
theorem scales_nonempty (P : DyadicPartition H) (x : H) : P.scales.Nonempty := by
  by_contra hcon
  rw [Finset.not_nonempty_iff_eq_empty] at hcon
  have := P.partition_of_unity x
  rw [hcon] at this
  simp at this

/-- The overlap budget of a partition over a non-empty type is at least `1`. -/
theorem one_le_overlapBound (P : DyadicPartition H) (x : H) : 1 ≤ P.overlapBound := by
  obtain ⟨T, _, hcard, hzero⟩ := P.bounded_overlap x
  by_contra hcon
  have hT : T = ∅ := by
    have : T.card = 0 := by omega
    exact Finset.card_eq_zero.mp this
  have h1 : ∑ k ∈ P.scales, P.weight k x = 0 :=
    Finset.sum_eq_zero fun k hk => hzero k hk (by simp [hT])
  rw [P.partition_of_unity x] at h1
  exact one_ne_zero h1

/-- Pointwise reconstruction: the partition reproduces any complex value. -/
theorem reconstruction (P : DyadicPartition H) (f : H → ℂ) (x : H) :
    ∑ k ∈ P.scales, (P.weight k x : ℂ) * f x = f x := by
  rw [← Finset.sum_mul]
  have : ((∑ k ∈ P.scales, P.weight k x : ℝ) : ℂ) = (1 : ℂ) := by
    rw [P.partition_of_unity x]; norm_num
  rw [← Complex.ofReal_sum, this, one_mul]

end DyadicPartition

/-! ## §2  The exact finite insertion identity

This is the deterministic algebraic content of "inserting the partition into the source":
*given* an exact partition of unity on the physical index family, the unprojected finite
source equals the sum of its projections.  It is proved unconditionally as an identity of
finite sums; the *physical* insertion (that the actual master source is of this shape) is
a separate, uninhabited interface, see §4. -/

/-- The `k`-th projected source. -/
noncomputable def projectedSource {ι : Type*} (I : Finset ι) (w : ℕ → ι → ℝ) (k : ℕ)
    (weight kernel : ι → ℂ) : ℂ :=
  ∑ xi ∈ I, (w k xi : ℂ) * (weight xi * kernel xi)

/-- **Exact insertion identity.**  An exact partition of unity on the index family splits
the unprojected source into the sum of its projections. -/
theorem unprojectedSource_eq_sum_projectedSource {ι : Type*} (I : Finset ι)
    (scales : Finset ℕ) (w : ℕ → ι → ℝ)
    (hpart : ∀ xi ∈ I, ∑ k ∈ scales, w k xi = 1) (weight kernel : ι → ℂ) :
    MasterSource.unprojectedSource I weight kernel
      = ∑ k ∈ scales, projectedSource I w k weight kernel := by
  simp only [MasterSource.unprojectedSource, projectedSource]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun xi hxi => ?_
  rw [← Finset.sum_mul]
  have : ((∑ k ∈ scales, w k xi : ℝ) : ℂ) = (1 : ℂ) := by
    rw [hpart xi hxi]; norm_num
  rw [← Complex.ofReal_sum, this, one_mul]

/-- Same identity, packaged for an abstract partition certificate on the index type. -/
theorem unprojectedSource_eq_sum_projectedSource_of_partition {ι : Type*} (I : Finset ι)
    (P : DyadicPartition ι) (weight kernel : ι → ℂ) :
    MasterSource.unprojectedSource I weight kernel
      = ∑ k ∈ P.scales, projectedSource I P.weight k weight kernel :=
  unprojectedSource_eq_sum_projectedSource I P.scales P.weight
    (fun xi _ => P.partition_of_unity xi) weight kernel

/-! ## §3  Proof-local Ω: local finiteness of the dyadic support -/

/-- If any two elements of a finite set of naturals are within `2` of each other, the set
has at most three elements. -/
theorem card_le_three_of_spread_le_two {S : Finset ℕ} (h : ∀ a ∈ S, ∀ b ∈ S, b ≤ a + 2) :
    S.card ≤ 3 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hsub : S ⊆ Finset.Icc (S.min' hne) (S.min' hne + 2) := by
      intro a ha
      exact Finset.mem_Icc.2 ⟨S.min'_le a ha, h _ (S.min'_mem hne) a ha⟩
    calc S.card ≤ (Finset.Icc (S.min' hne) (S.min' hne + 2)).card := Finset.card_le_card hsub
      _ = 3 := by rw [Nat.card_Icc]; omega

/-- The set of dyadic exponents contributing to a fixed positive `g`, i.e. those `k ≤ N`
with `g/2 ≤ 2^k ≤ 2g` (written multiplicatively to avoid truncated division). -/
def contributingScales (g N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun k => g ≤ 2 * 2 ^ k ∧ 2 ^ k ≤ 2 * g)

/-- Two contributing dyadic exponents differ by at most `2`. -/
theorem contributingScales_spread {g N a b : ℕ} (ha : a ∈ contributingScales g N)
    (hb : b ∈ contributingScales g N) : b ≤ a + 2 := by
  simp only [contributingScales, Finset.mem_filter, Finset.mem_range] at ha hb
  have h1 : 2 ^ b ≤ 2 * g := hb.2.2
  have h2 : g ≤ 2 * 2 ^ a := ha.2.1
  have h3 : 2 ^ b ≤ 2 ^ (a + 2) := by
    calc 2 ^ b ≤ 2 * g := h1
      _ ≤ 2 * (2 * 2 ^ a) := by omega
      _ = 2 ^ (a + 2) := by ring
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3

/-- **`dyadicLocalFiniteness`.**  For a fixed positive `g`, at most **three** dyadic
scales `H = 2^k` satisfy `g/2 ≤ H ≤ 2g`.  A concrete finite theorem: no asymptotics. -/
theorem dyadicLocalFiniteness (g N : ℕ) : (contributingScales g N).card ≤ 3 :=
  card_le_three_of_spread_le_two fun _ ha _ hb => contributingScales_spread ha hb

/-- The bound is attained, so `3` is sharp: for `g = 4` the exponents `1, 2, 3` all
contribute. -/
theorem dyadicLocalFiniteness_sharp : (contributingScales 4 5).card = 3 := by
  decide

/-- A single dyadic scale always contributes to `g = 2^k` itself, so the contributing set
is non-empty for every dyadic `g`. -/
theorem contributingScales_nonempty (k N : ℕ) (hk : k ≤ N) :
    k ∈ contributingScales (2 ^ k) N := by
  simp only [contributingScales, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, by omega, by omega⟩

/-! ## §4  Physical Ω-insertion: interface, left uninhabited -/

/-- **The physical Ω-insertion input.**  To insert the proof-local partition into the
*physical* source one needs an actual master physical source realisation, a positive
shared-gcd coordinate, and an exact partition of unity on that realisation's index family.

This structure is **left uninhabited**: nothing in this repository builds one, because its
`source` field requires the (missing) master physical source realisation. -/
structure ProofOmegaInsertionInput (spec : MasterSource.SourceSpec) where
  /-- The missing master physical source realisation. -/
  source : MasterSource.MasterPhysicalSourceRealisation spec
  /-- The proof-local dyadic partition on the physical index family. -/
  partition : DyadicPartition ℕ
  /-- The shared-gcd coordinate carried by the source is positive. -/
  sharedGcd_pos : 0 < spec.sharedGcd

/-- **Conditional insertion theorem.**  *Given* a physical insertion input, the physical
unprojected source equals the sum over dyadic scales of its projections.  The hypothesis is
an actual physical input, not an abstract one. -/
theorem physical_insertion {spec : MasterSource.SourceSpec}
    (J : ProofOmegaInsertionInput spec) :
    spec.parent
      = ∑ k ∈ J.partition.scales,
          projectedSource J.source.index J.partition.weight k
            spec.requiredWeight spec.requiredKernel := by
  rw [J.source.parent_eq]
  exact unprojectedSource_eq_sum_projectedSource_of_partition _ J.partition _ _

/-- A concrete abstract partition on `ℕ`: a single scale carrying all the mass. -/
def trivialPartition : DyadicPartition ℕ where
  scales := {0}
  weight := fun k _ => if k = 0 then 1 else 0
  weight_nonneg := by intro k x; by_cases h : k = 0 <;> simp [h]
  partition_of_unity := by intro x; simp
  support := fun _ => Set.univ
  weight_eq_zero_of_not_mem := by intro k x hx; exact absurd (Set.mem_univ x) hx
  overlapBound := 1
  bounded_overlap := by
    intro x
    exact ⟨{0}, Finset.Subset.refl _, by simp, by intro k hk hk'; exact absurd hk hk'⟩

/-- **`abstractProofOmegaPartition_does_not_construct_physicalInsertion`.**  Owning an
abstract dyadic partition certificate — even one satisfying an exact partition of unity —
does **not** produce a physical Ω-insertion input: for the countermodel spec of the master
source bank the abstract partition exists while the insertion input type is empty. -/
theorem abstractProofOmegaPartition_does_not_construct_physicalInsertion :
    Nonempty (DyadicPartition ℕ) ∧
      ¬ Nonempty (ProofOmegaInsertionInput MasterSource.vanishingWeightSpec) := by
  refine ⟨⟨trivialPartition⟩, ?_⟩
  rintro ⟨J⟩
  exact MasterSource.no_realisation_vanishingWeightSpec ⟨J.source⟩

/-- **Scope firewall.**  The exact insertion identity of §2 is an identity of finite sums:
it holds for *arbitrary* weights summing to one and therefore carries no physical content
by itself.  Explicitly, it holds for data that admits no physical insertion input. -/
theorem insertion_identity_is_not_physical_insertion (weight kernel : ℕ → ℂ)
    (I : Finset ℕ) :
    MasterSource.unprojectedSource I weight kernel
        = ∑ k ∈ trivialPartition.scales,
            projectedSource I trivialPartition.weight k weight kernel ∧
      ¬ Nonempty (ProofOmegaInsertionInput MasterSource.vanishingWeightSpec) :=
  ⟨unprojectedSource_eq_sum_projectedSource_of_partition I trivialPartition weight kernel,
    abstractProofOmegaPartition_does_not_construct_physicalInsertion.2⟩

end ProofOmega
end Erdos287
