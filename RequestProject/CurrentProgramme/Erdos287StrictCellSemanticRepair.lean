import Mathlib
import RequestProject.CurrentProgramme.Erdos287StrictCellCanonicalSingleton
import RequestProject.CurrentProgramme.Erdos287RepeatedPrimePhysicalSource

/-!
# Semantic repair layer §2–§3 — Ford-`H` physical binding and the strict-collapse
classification

This file is **append-only**.  It deletes, renames and weakens nothing.  It sits *after* the
strict-cell canonical-singleton bank and classifies two of its objects, then supplies the
physical binding that the older layer did **not** contain.

## What is repaired

* `Erdos287.StrictCellSingleton.hStar` is a **combinatorial surrogate / finite certificate
  value**: by definition it is minus the number of depth-`3` subsets of a six-prime
  complement.  It is *not*, by definition, the literal Ford functional
  `H_{μ,σ*,g*}(P)`.  `combinatorial_hStar_is_surrogate` and
  `combinatorial_hStar_does_not_construct_FordHPhysicalBinding` make this machine-checkable.
* `Erdos287.StrictCellSingleton.StrictCellHypotheses.strict_collapse` is an **abstract finite
  certificate hypothesis**, not a physical source theorem.  The physical `k = 0`, `J = ∅`
  binding is isolated as `PhysicalCollapseBinding`, and the bridge
  `strictCellHypotheses_of_physicalCollapse` is proved *from the physical source dictionary*.

## What is newly proved

The literal Ford-`H` value, **conditionally on the physical binding only**:

```
    FordHPhysicalBinding Pset Hphys γ* cut  →  Hphys(∏ Pset) = −20,
```

via the exact finite chain

```
    H_phys(P) = truncMobius(P, ⌊P^{γ*}⌋)
              = ∑_{d ∣ P, ω(d) ≤ 3} μ(d)
              = ∑_{S ⊆ Pset, |S| ≤ 3} (−1)^{|S|}
              = ∑_{j ≤ 3} (−1)^j C(7,j) = −20.
```

No analytic input is used and no external theorem is assumed as an axiom.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open ArithmeticFunction

namespace Erdos287
namespace SemanticRepair

open Finset
open Erdos287.SP2Source
open Erdos287.SmoothParity
open Erdos287.StrictCellSingleton

/-! ## §1.  The semantic classification -/

/-- The semantic kind of a banked object. -/
inductive ObjectSemantics
  /-- A finite combinatorial certificate value; kernel-safe, but not a physical-source
  object by definition. -/
  | combinatorialSurrogate
  /-- An abstract finite certificate hypothesis. -/
  | abstractCertificate
  /-- A literal physical-source object. -/
  | physicalSource
  deriving DecidableEq, Repr

/-- `StrictCellSingleton.hStar` is classified as a combinatorial surrogate. -/
def hStarSemantics : ObjectSemantics := ObjectSemantics.combinatorialSurrogate

/-- `StrictCellHypotheses.strict_collapse` is classified as an abstract certificate. -/
def strictCollapseSemantics : ObjectSemantics := ObjectSemantics.abstractCertificate

theorem hStar_not_physicalSource : hStarSemantics ≠ ObjectSemantics.physicalSource := by
  decide

theorem strictCollapse_not_physicalSource :
    strictCollapseSemantics ≠ ObjectSemantics.physicalSource := by decide

/-- The surrogate reading of `hStar` is exactly its definition: minus the number of
depth-`3` subsets of the six-prime complement. -/
theorem combinatorial_hStar_is_surrogate (U : Finset (Fin 7)) :
    hStar U = -((depthSubsets U).card : ℤ) := rfl

/-! ## §2.  Finite subset algebra behind the depth-3 alternating value -/

/-- Small subsets are the disjoint union of the exact-cardinality layers. -/
theorem powerset_filter_card_le {α : Type*} [DecidableEq α] (s : Finset α) (k : ℕ) :
    s.powerset.filter (fun S => S.card ≤ k)
      = (Finset.range (k + 1)).biUnion (fun j => s.powersetCard j) := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_powersetCard]
  constructor
  · rintro ⟨hsub, hcard⟩
    exact ⟨S.card, by omega, hsub, rfl⟩
  · rintro ⟨j, hj, hsub, rfl⟩
    exact ⟨hsub, by omega⟩

/-- **`sum_over_small_subsets`.**  `LEAN_PROVED`.

Any function of the cardinality, summed over the subsets of size `≤ k`, collapses to the
binomial sum. -/
theorem sum_over_small_subsets {α : Type*} [DecidableEq α] (s : Finset α) (k : ℕ)
    (f : ℕ → ℤ) :
    ∑ S ∈ s.powerset.filter (fun S => S.card ≤ k), f S.card
      = ∑ j ∈ Finset.range (k + 1), (s.card.choose j : ℤ) * f j := by
  classical
  rw [powerset_filter_card_le s k]
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hval : ∀ S ∈ s.powersetCard j, f S.card = f j := by
      intro S hS
      rw [(Finset.mem_powersetCard.mp hS).2]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, Finset.card_powersetCard]
    simp [mul_comm]
  · intro a _ b _ hab
    simp only [Finset.disjoint_left, Finset.mem_powersetCard]
    rintro S ⟨-, rfl⟩ ⟨-, h⟩
    exact hab h

/-- The alternating depth-`3` subset sum of a seven-element set is `−20`. -/
theorem altSum_small_subsets_seven {α : Type*} [DecidableEq α] {s : Finset α}
    (h7 : s.card = 7) :
    ∑ S ∈ s.powerset.filter (fun S => S.card ≤ 3), ((-1 : ℤ)) ^ S.card = -20 := by
  rw [sum_over_small_subsets s 3 (fun j => ((-1 : ℤ)) ^ j), h7]
  decide

/-! ## §3.  Products of distinct primes -/

variable {Pset : Finset ℕ}

/-- `μ(∏ S) = (−1)^{|S|}` for a finite set of distinct primes. -/
theorem moebius_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    moebius (∏ p ∈ S, p) = (-1 : ℤ) ^ S.card := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_prod _ S ?_]
  · rw [Finset.prod_congr rfl (fun p hp => moebius_apply_prime (hS p hp))]
    simp
  · intro a ha b hb hab
    exact (Nat.coprime_primes (hS a ha) (hS b hb)).mpr hab

/-- The subset-product map is injective on subsets of a set of distinct primes. -/
theorem prod_subset_injOn (hp : ∀ p ∈ Pset, Nat.Prime p) :
    Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) (Pset.powerset : Set (Finset ℕ)) := by
  intro S hS T hT hST
  have hS' : ∀ p ∈ S, Nat.Prime p := fun p hpS =>
    hp p (Finset.mem_powerset.mp (by simpa using hS) hpS)
  have hT' : ∀ p ∈ T, Nat.Prime p := fun p hpT =>
    hp p (Finset.mem_powerset.mp (by simpa using hT) hpT)
  have := congrArg Nat.primeFactors hST
  rwa [Nat.primeFactors_prod hS', Nat.primeFactors_prod hT'] at this

/-- The product of distinct primes is squarefree. -/
theorem squarefree_prod_primes (hp : ∀ p ∈ Pset, Nat.Prime p) :
    Squarefree (∏ p ∈ Pset, p) := by
  classical
  induction Pset using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hpa : Nat.Prime a := hp a (Finset.mem_insert_self a s)
      have hps : ∀ p ∈ s, Nat.Prime p := fun p hps => hp p (Finset.mem_insert_of_mem hps)
      have hsq := ih hps
      refine (Nat.squarefree_mul ?_).mpr ⟨hpa.squarefree, hsq⟩
      rw [Nat.Prime.coprime_iff_not_dvd hpa]
      intro hdvd
      obtain ⟨q, hq, hqa⟩ := (Nat.Prime.prime hpa).exists_mem_finset_dvd hdvd
      have : a = q := ((Nat.prime_dvd_prime_iff_eq hpa (hps q hq)).mp hqa)
      exact ha (this ▸ hq)

/-- The divisors of a product of distinct primes are exactly the subset products. -/
theorem divisors_prod_primes (hp : ∀ p ∈ Pset, Nat.Prime p) :
    (∏ p ∈ Pset, p).divisors = Pset.powerset.image (fun S => ∏ p ∈ S, p) := by
  classical
  have hpos : 0 < ∏ p ∈ Pset, p :=
    Finset.prod_pos fun p hpP => (hp p hpP).pos
  have hsq := squarefree_prod_primes hp
  ext d
  simp only [Nat.mem_divisors, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨hdvd, -⟩
    refine ⟨d.primeFactors, ?_, ?_⟩
    · have := Nat.primeFactors_mono hdvd hpos.ne'
      rwa [Nat.primeFactors_prod hp] at this
    · exact Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd hdvd)
  · rintro ⟨S, hSsub, rfl⟩
    exact ⟨Finset.prod_dvd_prod_of_subset _ _ _ hSsub, hpos.ne'⟩

/-! ## §4.  The Ford-`H` physical binding -/

/-- **`FordHPhysicalBinding`** — the literal physical-source binding for the Ford functional

```
    H_phys(P) = H_{μ,σ*,g*}(P).
```

Its fields are exactly the source conditions required before the Ford `G/H` dictionary may
be applied:

* the physical seven-prime source (`seven_primes`, `all_prime`);
* the strict Ford smoothness window (`smooth_window`);
* the literal Ford cutoff `⌊P^{γ*}⌋` (`cutoff_literal`);
* the Ford `G/H` source dictionary `H_phys(P) = truncMobius(P, cut P)` (`ford_dictionary`);
* the literal depth truncation induced by the cutoff on the balanced source
  (`depth_cut`).

**This structure is not inhabited anywhere in the repository.** -/
structure FordHPhysicalBinding (Pset : Finset ℕ) (Hphys : ℕ → ℤ) (gammaStar : ℝ)
    (cut : ℕ → ℕ) : Prop where
  /-- The physical source carries exactly seven prime slots. -/
  seven_primes : Pset.card = 7
  /-- Every slot value is a physical prime. -/
  all_prime : ∀ p ∈ Pset, Nat.Prime p
  /-- Strict Ford smoothness: all seven primes lie in one balanced window. -/
  smooth_window : ∃ Y : ℝ, 1 < Y ∧ ∀ p ∈ Pset, Y < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (2 : ℕ)
  /-- The literal Ford cutoff. -/
  cutoff_literal : ∀ n : ℕ, cut n = ⌊(n : ℝ) ^ gammaStar⌋₊
  /-- The Ford `G/H` source dictionary. -/
  ford_dictionary :
    Hphys (∏ p ∈ Pset, p) = truncMobius (∏ p ∈ Pset, p) (cut (∏ p ∈ Pset, p))
  /-- The literal depth truncation carried by the cutoff on the balanced source: a divisor
  survives exactly when it is a product of at most three of the physical primes. -/
  depth_cut : ∀ d ∈ (∏ p ∈ Pset, p).divisors,
    (d ≤ cut (∏ p ∈ Pset, p) ↔ d.primeFactors.card ≤ 3)

/-- **`truncMobius_depthCut_eq_neg_twenty`.**  `LEAN_PROVED`.

The exact finite evaluation of the truncated Möbius weight of a product of seven distinct
primes, when the cutoff realises the depth-`3` truncation. -/
theorem truncMobius_depthCut_eq_neg_twenty (hp : ∀ p ∈ Pset, Nat.Prime p)
    (h7 : Pset.card = 7) {T : ℕ}
    (hcut : ∀ d ∈ (∏ p ∈ Pset, p).divisors, (d ≤ T ↔ d.primeFactors.card ≤ 3)) :
    truncMobius (∏ p ∈ Pset, p) T = -20 := by
  classical
  have hfilter :
      (∏ p ∈ Pset, p).divisors.filter (fun d => d ≤ T)
        = (∏ p ∈ Pset, p).divisors.filter (fun d => d.primeFactors.card ≤ 3) :=
    Finset.filter_congr (fun d hd => by simpa using hcut d hd)
  rw [truncMobius, hfilter, divisors_prod_primes hp]
  rw [Finset.filter_image]
  rw [Finset.sum_image (fun S hS T' hT' h => prod_subset_injOn hp (by simpa using
    (Finset.mem_filter.mp hS).1) (by simpa using (Finset.mem_filter.mp hT').1) h)]
  have hcongr : ∀ S ∈ Pset.powerset.filter
      (fun S => (∏ p ∈ S, p).primeFactors.card ≤ 3),
      moebius (∏ p ∈ S, p) = (-1 : ℤ) ^ S.card := by
    intro S hS
    exact moebius_prod_primes (fun p hpS =>
      hp p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1 hpS))
  rw [Finset.sum_congr rfl hcongr]
  have hset : Pset.powerset.filter (fun S => (∏ p ∈ S, p).primeFactors.card ≤ 3)
      = Pset.powerset.filter (fun S => S.card ≤ 3) := by
    refine Finset.filter_congr fun S hS => ?_
    have hS' : ∀ p ∈ S, Nat.Prime p := fun p hpS =>
      hp p (Finset.mem_powerset.mp hS hpS)
    rw [Nat.primeFactors_prod hS']
  rw [hset]
  exact altSum_small_subsets_seven h7

/-- **`fordH_physical_eq_neg_twenty`.**  `CONDITIONAL / LEAN_PROVED`.

Conditionally on the **physical** Ford-`H` binding — and on nothing else — the literal Ford
functional of the seven physical primes equals `−20`.  This is *not* inferred from
`StrictCellSingleton.hStar = −20`. -/
theorem fordH_physical_eq_neg_twenty {Hphys : ℕ → ℤ} {gammaStar : ℝ} {cut : ℕ → ℕ}
    (h : FordHPhysicalBinding Pset Hphys gammaStar cut) :
    Hphys (∏ p ∈ Pset, p) = -20 := by
  rw [h.ford_dictionary]
  exact truncMobius_depthCut_eq_neg_twenty h.all_prime h.seven_primes h.depth_cut

/-! ## §5.  Firewall: the surrogate does not construct the physical binding -/

/-- **`combinatorial_hStar_does_not_construct_FordHPhysicalBinding`.**  `LEAN_PROVED`.

The banked combinatorial identity `hStar U = −20` holds for *every* branch label, yet there
are physical data with `Hphys ≡ −20` for which the Ford binding fails.  Hence the
combinatorial surrogate never, by itself, constructs the physical binding. -/
theorem combinatorial_hStar_does_not_construct_FordHPhysicalBinding :
    (∀ U : Finset (Fin 7), hStar U = -20) ∧
      ∃ (Pset : Finset ℕ) (Hphys : ℕ → ℤ) (gammaStar : ℝ) (cut : ℕ → ℕ),
        (∀ n, Hphys n = -20) ∧ ¬ FordHPhysicalBinding Pset Hphys gammaStar cut := by
  refine ⟨hStar_eq_neg_twenty, ∅, fun _ => -20, 0, fun _ => 0, fun _ => rfl, ?_⟩
  intro h
  have := h.seven_primes
  simp at this

/-- **`fordHPhysicalBinding_not_automatic`.**  `LEAN_PROVED`.

The binding is a genuine restriction: explicit data refute it. -/
theorem fordHPhysicalBinding_not_automatic :
    ∃ (Pset : Finset ℕ) (Hphys : ℕ → ℤ) (gammaStar : ℝ) (cut : ℕ → ℕ),
      ¬ FordHPhysicalBinding Pset Hphys gammaStar cut :=
  ⟨∅, fun _ => -20, 0, fun _ => 0, fun h => by simpa using h.seven_primes⟩

/-! ## §6.  Strict collapse: abstract certificate versus physical binding -/

/-- **`PhysicalCollapseBinding`** — the *physical* `k = 0`, `J = ∅` source statement.

The abstract strict-cell certificate merely *hypothesises* `k + |J| = 0`.  This structure
records that the physical source dictionary literally supplies the level and the auxiliary
index set of the certificate. -/
structure PhysicalCollapseBinding (C : SP2FixedCertificateData) (srcK : ℕ)
    (srcJ : Finset ℕ) : Prop where
  /-- The certificate level is the level read off the source. -/
  level_from_source : C.k = srcK
  /-- The certificate index set is the index set read off the source. -/
  index_from_source : C.J = srcJ
  /-- The source dictionary supplies level zero. -/
  source_level_zero : srcK = 0
  /-- The source dictionary supplies the empty index set. -/
  source_index_empty : srcJ = ∅

/-- **`strict_collapse_of_physicalCollapse`.**  `LEAN_PROVED`.

If the source dictionary literally supplies `k = 0` and `J = ∅`, the abstract collapse
certificate is a *theorem*, not a hypothesis. -/
theorem strict_collapse_of_physicalCollapse {C : SP2FixedCertificateData} {srcK : ℕ}
    {srcJ : Finset ℕ} (h : PhysicalCollapseBinding C srcK srcJ) :
    C.k + C.J.card = 0 := by
  rw [h.level_from_source, h.index_from_source, h.source_level_zero, h.source_index_empty]
  simp

/-- **`strictCellHypotheses_of_physicalCollapse`.**  `LEAN_PROVED`.

The full strict-cell hypothesis package, with the collapse field supplied by the physical
source binding rather than assumed. -/
theorem strictCellHypotheses_of_physicalCollapse {C : SP2FixedCertificateData}
    {U : Finset (Fin 7)} {srcK : ℕ} {srcJ : Finset ℕ}
    (h : PhysicalCollapseBinding C srcK srcJ)
    (h7 : C.bigOmega = 7) (h3 : C.r = 3) (hs : C.s = 1 ∨ C.s = -1)
    (hprime : ∀ (i : Fin 7), ∀ p ∈ C.lam i, Nat.Prime p)
    (hne : ∀ i : Fin 7, (C.lam i).Nonempty) (hU : U.card ≤ 3) :
    StrictCellHypotheses C U :=
  ⟨strict_collapse_of_physicalCollapse h, h7, h3, hs, hprime, hne, hU⟩

/-- **`abstract_collapse_does_not_give_physicalCollapse`.**  `LEAN_PROVED`.

The converse fails: the abstract certificate holds for a datum for which the *physical*
binding to a given source is false, so the abstract hypothesis may not be described as a
physical source theorem. -/
theorem abstract_collapse_does_not_give_physicalCollapse :
    ∃ (C : SP2FixedCertificateData) (U : Finset (Fin 7)) (srcK : ℕ) (srcJ : Finset ℕ),
      StrictCellHypotheses C U ∧ ¬ PhysicalCollapseBinding C srcK srcJ := by
  obtain ⟨C, U, hC⟩ := strictCellHypotheses_inhabited
  refine ⟨C, U, 1, ∅, hC, ?_⟩
  intro h
  exact absurd h.source_level_zero one_ne_zero

end SemanticRepair
end Erdos287
