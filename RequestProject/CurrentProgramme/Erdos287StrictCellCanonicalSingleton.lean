import Mathlib
import RequestProject.Erdos287.SP2PrimeBoxWeights3221
import RequestProject.Erdos287.BalancedSevenFinite

/-!
# Erdős #287 — strict-cell canonical-singleton frontier (append-only)

`ERDOS287-SP2-STRICTCELL-CANONICALSINGLETON45`.

This module is **strictly append-only**: it adds new definitions and theorems on top of the
banked SP-2 prime-box layer (`Erdos287.SP2PrimeBox`) and edits nothing.

## What is formalised here

1. `OmegaSharp` — the *exact weighted prime-vector → integer pushforward* of a fixed smooth
   cell: a vector `v ∈ λ_0 × ⋯ × λ_6` is pushed to the integer `∏ i, v i`, and a weight is
   summed over each fibre.
2. `omegaSharp_one_not_automatic` — an explicit countermodel: the fibre mass is **not**
   automatically `1` (for the balanced cell `λ_i = {2,3}` the integer `2^6·3` has fibre mass
   `7`).  So "`Ω^♯_C = 1`" is a genuine hypothesis, never a consequence of the packet shape.
3. `StrictCellHypotheses` — the explicit strict-cell hypotheses, from which `k = 0` and
   `J = ∅` are **derived** (`strictCell_k_zero`, `strictCell_J_empty`).
4. The balanced-seven divisor-depth theorem and `HStar = -20` (`hStar_eq_neg_twenty`), which
   are *not* present anywhere else in the repository (checked: no `HStar` symbol was banked).
5. The physical, source-specific Ford coordinate count `s = |U| + 1`, `r = 8 - |U|`,
   `N = s + r = 9` (`ford_coordCount_eq_nine`).
6. `fordBranches_card` : `#{U ⊆ Fin 7 : |U| ≤ 3} = 64`.
7. Exactly seven nonterminal / nonunit *physical prime* coordinates and exactly two terminal
   *unit* coordinates (`physicalPrimeCoords_card`, `terminalUnitCoords_card`).
8. All physical `k = 0` (7.20) conditions as consequences of the strict-cell hypotheses
   (`PhysicalK0Conditions720`, `physicalK0_of_strictCell`).
9. No `d_{h,j}` variables for `k = 0` (`dIndex_eq_empty`).
10. The deterministic canonical singleton selection `i(U)` (`canonicalSingleton`) with its
    minimality/determinism characterisation.
11. The singleton Type-II *window* extracted from the physical prime size bounds
    (`singleton_mem_window`, `complement_pushforward_bounds`).
12. No generic subsum inclusion–exclusion is required: the total pushforward mass factorises
    exactly (`omegaSharp_total_mass`, `productWeight_total_mass`).
13. Zero Ford hard-condition Perron contour count (`perronContourCount_eq_zero`).
15. A counterguard: an arbitrary cell weight does **not** admit rank-one / product separation
    (`weight_not_product_separable`).
17. Complement depth `= 6` (`complementDepth_eq_six`).
18. Deterministic finite Cauchy / product-energy interfaces (`finite_cauchy_schwarz`,
    `productEnergy_factorises`).

Nothing here closes, or claims to close, Erdős #287, and nothing here proves the analytic
singleton Type-II estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace StrictCellSingleton

open Finset
open Erdos287.SP2Source

/-! ## §1.  The exact weighted prime-vector → integer pushforward `Ω^♯_C` -/

/-- The set of prime vectors of the fixed smooth cell: `v ∈ λ_0 × ⋯ × λ_6`. -/
def cellVectors (C : SP2FixedCertificateData) : Finset (Fin 7 → ℕ) :=
  Fintype.piFinset C.lam

/-- The pushforward map: a prime vector is sent to the integer it multiplies out to. -/
def pushforward (v : Fin 7 → ℕ) : ℕ := ∏ i, v i

/-- The fibre of the pushforward over an integer `n`. -/
def omegaSharpFibre (C : SP2FixedCertificateData) (n : ℕ) : Finset (Fin 7 → ℕ) :=
  (cellVectors C).filter (fun v => pushforward v = n)

/-- **`OmegaSharp`** — the exact weighted prime-vector → integer pushforward `Ω^♯_C`.

Given a weight `w` on prime vectors, `Ω^♯_C(w, n)` is the total weight of the vectors of the
fixed cell whose product is `n`.  It is an *exact* pushforward: no approximation, no error
term, and no inclusion–exclusion over subsums. -/
def OmegaSharp (C : SP2FixedCertificateData) (w : (Fin 7 → ℕ) → ℤ) (n : ℕ) : ℤ :=
  ∑ v ∈ omegaSharpFibre C n, w v

/-- The unit weight. -/
def unitWeight : (Fin 7 → ℕ) → ℤ := fun _ => 1

/-- The product ("rank-one") weight attached to a family of slot weights. -/
def productWeight (f : Fin 7 → ℕ → ℤ) : (Fin 7 → ℕ) → ℤ := fun v => ∏ i, f i (v i)

/-- With the unit weight, `Ω^♯_C` counts the fibre. -/
theorem OmegaSharp_unitWeight (C : SP2FixedCertificateData) (n : ℕ) :
    OmegaSharp C unitWeight n = ((omegaSharpFibre C n).card : ℤ) := by
  simp [OmegaSharp, unitWeight]

/-- Off the image of the pushforward, `Ω^♯_C` vanishes for every weight. -/
theorem OmegaSharp_eq_zero_of_not_mem_image (C : SP2FixedCertificateData)
    (w : (Fin 7 → ℕ) → ℤ) {n : ℕ} (hn : n ∉ (cellVectors C).image pushforward) :
    OmegaSharp C w n = 0 := by
  have : omegaSharpFibre C n = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.2 ?_
    intro v hv
    rw [omegaSharpFibre, Finset.mem_filter] at hv
    exact hn (Finset.mem_image.2 ⟨v, hv.1, hv.2⟩)
  simp [OmegaSharp, this]

/-- Every element of a fibre really is a cell vector pushing forward to `n`. -/
theorem mem_omegaSharpFibre_iff (C : SP2FixedCertificateData) (n : ℕ) (v : Fin 7 → ℕ) :
    v ∈ omegaSharpFibre C n ↔ (∀ i, v i ∈ C.lam i) ∧ pushforward v = n := by
  simp [omegaSharpFibre, cellVectors, Fintype.mem_piFinset, Finset.mem_filter, and_comm]

/-! ## §2.  Countermodel: `Ω^♯_C = 1` is not automatic -/

/-- The balanced countermodel certificate: every slot carries the cell `{2,3}`. -/
def countermodelCert : SP2FixedCertificateData where
  k := 0
  J := ∅
  bigOmega := 7
  r := 3
  s := 1
  lam := fun _ => {2, 3}

/-- The countermodel certificate satisfies the banked SP-2 packet normalisation, so it is a
legitimate packet, not a degenerate object. -/
theorem countermodelCert_packet : SP2PacketNormalization countermodelCert := by
  refine ⟨rfl, rfl, rfl, rfl, Or.inl rfl, ?_⟩
  intro i p hp
  have hp' : p = 2 ∨ p = 3 := by simpa [countermodelCert] using hp
  rcases hp' with h | h <;> subst h <;> norm_num

/-- The fibre of `2^6·3 = 192` in the balanced countermodel has exactly seven vectors. -/
theorem countermodel_fibre_card : (omegaSharpFibre countermodelCert 192).card = 7 := by
  decide

/-- **`omegaSharp_eq_seven`.**  `LEAN_PROVED`.  In the balanced countermodel the pushforward
mass at `192` is `7`. -/
theorem omegaSharp_eq_seven : OmegaSharp countermodelCert unitWeight 192 = 7 := by
  rw [OmegaSharp_unitWeight, countermodel_fibre_card]
  norm_num

/-- **`omegaSharp_one_not_automatic`.**  `LEAN_PROVED`.

`Ω^♯_C = 1` — i.e. "each surviving integer has a unique prime-vector preimage of unit
weight" — is **not** automatic: there is a certificate satisfying the full SP-2 packet
normalisation, and an integer in the image of the pushforward, whose mass is `7 ≠ 1`.
Any argument that needs `Ω^♯_C = 1` must therefore assume it (a strict-cell hypothesis),
never derive it from the packet shape. -/
theorem omegaSharp_one_not_automatic :
    ∃ (C : SP2FixedCertificateData) (n : ℕ),
      SP2PacketNormalization C ∧ (omegaSharpFibre C n).Nonempty ∧
        OmegaSharp C unitWeight n ≠ 1 := by
  refine ⟨countermodelCert, 192, countermodelCert_packet, ?_, ?_⟩
  · rw [← Finset.card_pos, countermodel_fibre_card]; norm_num
  · rw [omegaSharp_eq_seven]; norm_num

/-! ## §3.  Strict-cell hypotheses; `k = 0` and `J = ∅` -/

/-- **`StrictCellHypotheses`** — the explicit strict-cell hypotheses of the SP-2 packet.

The collapse hypothesis is stated as `C.k + C.J.card = 0`, so `k = 0` and `J = ∅` are
*derived*, not assumed separately. -/
structure StrictCellHypotheses (C : SP2FixedCertificateData) (U : Finset (Fin 7)) : Prop where
  /-- Strict-cell collapse of the level and the auxiliary index set. -/
  strict_collapse : C.k + C.J.card = 0
  /-- The balanced-seven prescription `Ω(n) = 7`. -/
  omega_seven : C.bigOmega = 7
  /-- The surviving divisor depth is `3`. -/
  depth_three : C.r = 3
  /-- The sign is a unit. -/
  sign_unit : C.s = 1 ∨ C.s = -1
  /-- The cell is literally supported on primes. -/
  cell_prime : ∀ (i : Fin 7), ∀ p ∈ C.lam i, Nat.Prime p
  /-- Every slot of the cell is occupied. -/
  cell_nonempty : ∀ i : Fin 7, (C.lam i).Nonempty
  /-- The branch label is one of the 64 small subsets. -/
  branch_small : U.card ≤ 3

/-- **`strictCell_k_zero`.**  `LEAN_PROVED` (conditional on the strict-cell hypotheses). -/
theorem strictCell_k_zero {C : SP2FixedCertificateData} {U : Finset (Fin 7)}
    (h : StrictCellHypotheses C U) : C.k = 0 := by
  have := h.strict_collapse; omega

/-- **`strictCell_J_empty`.**  `LEAN_PROVED` (conditional on the strict-cell hypotheses). -/
theorem strictCell_J_empty {C : SP2FixedCertificateData} {U : Finset (Fin 7)}
    (h : StrictCellHypotheses C U) : C.J = ∅ := by
  have h1 := h.strict_collapse
  have : C.J.card = 0 := by omega
  exact Finset.card_eq_zero.1 this

/-- The strict-cell hypotheses imply the banked SP-2 packet normalisation. -/
theorem strictCell_packetNormalization {C : SP2FixedCertificateData} {U : Finset (Fin 7)}
    (h : StrictCellHypotheses C U) : SP2PacketNormalization C :=
  ⟨strictCell_k_zero h, strictCell_J_empty h, h.omega_seven, h.depth_three, h.sign_unit,
    h.cell_prime⟩

/-- The strict-cell hypotheses are consistent: an explicit certificate satisfies them.  (This
is a *non-vacuity* guard; it is not a physical source claim.) -/
theorem strictCellHypotheses_inhabited :
    ∃ (C : SP2FixedCertificateData) (U : Finset (Fin 7)), StrictCellHypotheses C U := by
  refine ⟨countermodelCert, ∅, ⟨rfl, rfl, rfl, Or.inl rfl, ?_, ?_, by simp⟩⟩
  · intro i p hp
    have hp' : p = 2 ∨ p = 3 := by simpa [countermodelCert] using hp
    rcases hp' with h | h <;> subst h <;> norm_num
  · intro i; exact ⟨2, by simp [countermodelCert]⟩

/-! ## §4.  No `d_{h,j}` variables for `k = 0` -/

/-- The index set of the `d_{h,j}` variables: pairs `(h, j)` with `h < k` and `j ∈ J`. -/
def dIndex (C : SP2FixedCertificateData) : Finset (ℕ × ℕ) := (Finset.range C.k) ×ˢ C.J

/-- **`dIndex_eq_empty`.**  `LEAN_PROVED` (conditional).  For `k = 0` there are no `d_{h,j}`
variables at all. -/
theorem dIndex_eq_empty {C : SP2FixedCertificateData} {U : Finset (Fin 7)}
    (h : StrictCellHypotheses C U) : dIndex C = ∅ := by
  rw [dIndex, strictCell_k_zero h]
  simp

/-- The `d`-variable count is zero. -/
theorem dIndex_card_zero {C : SP2FixedCertificateData} {U : Finset (Fin 7)}
    (h : StrictCellHypotheses C U) : (dIndex C).card = 0 := by
  rw [dIndex_eq_empty h]; simp

/-- The `d`-variable index set is not empty in general: a level-`1` datum with `J = {1}` has
one such variable, so `dIndex_eq_empty` genuinely uses `k = 0`. -/
theorem dIndex_not_automatically_empty :
    ∃ C : SP2FixedCertificateData, dIndex C ≠ ∅ := by
  refine ⟨⟨1, {1}, 7, 3, 1, fun _ => {2}⟩, ?_⟩
  intro h
  have : ((0, 1) : ℕ × ℕ) ∈ dIndex (⟨1, {1}, 7, 3, 1, fun _ => {2}⟩ :
      SP2FixedCertificateData) := by
    simp [dIndex]
  rw [h] at this
  simp at this

/-! ## §5.  The physical Ford coordinate count `s`, `r`, `N` -/

/-- The source-specific slot count `s = |U| + 1`. -/
def slotCount (U : Finset (Fin 7)) : ℕ := U.card + 1

/-- The source-specific rank count `r = 8 - |U|`. -/
def rankCount (U : Finset (Fin 7)) : ℕ := 8 - U.card

/-- The total Ford coordinate count `N = s + r`. -/
def coordCount (U : Finset (Fin 7)) : ℕ := slotCount U + rankCount U

/-- **`ford_coordCount_eq_nine`.**  `LEAN_PROVED`.

The physical, source-specific Ford coordinate count: `s = |U| + 1`, `r = 8 - |U|`,
`N = s + r = 9`, for **every** branch label `U ⊆ Fin 7`. -/
theorem ford_coordCount_eq_nine (U : Finset (Fin 7)) : coordCount U = 9 := by
  have h : U.card ≤ 7 := by
    have := Finset.card_le_univ U
    simpa using this
  simp only [coordCount, slotCount, rankCount]
  omega

/-- The slot count in the small branches. -/
theorem slotCount_le_four {U : Finset (Fin 7)} (h : U.card ≤ 3) : slotCount U ≤ 4 := by
  simp only [slotCount]; omega

/-- The rank count in the small branches. -/
theorem rankCount_ge_five {U : Finset (Fin 7)} (h : U.card ≤ 3) : 5 ≤ rankCount U := by
  simp only [rankCount]; omega

/-! ## §6.  The 64 branches -/

/-- The Ford branch labels of the packet: subsets of the seven prime coordinates of size at
most three. -/
def fordBranches : Finset (Finset (Fin 7)) :=
  (Finset.univ : Finset (Finset (Fin 7))).filter (fun U => U.card ≤ 3)

/-- **`fordBranches_card`.**  `LEAN_PROVED`.  There are exactly `64` branches:
`1 + 7 + 21 + 35 = 64`. -/
theorem fordBranches_card : fordBranches.card = 64 := by decide

/-- Membership in the branch list is exactly the strict-cell smallness condition. -/
theorem mem_fordBranches (U : Finset (Fin 7)) : U ∈ fordBranches ↔ U.card ≤ 3 := by
  simp [fordBranches]

/-! ## §7.  Seven physical prime coordinates, two terminal unit coordinates -/

/-- The two kinds of Ford coordinate in this packet. -/
inductive CoordKind
  /-- A nonterminal, nonunit *physical prime* coordinate. -/
  | physicalPrime
  /-- A terminal *unit* coordinate. -/
  | terminalUnit
  deriving DecidableEq, Fintype, Repr

/-- The coordinate classification of the nine Ford coordinates: `0,…,6` are the physical
prime coordinates, `7,8` are the two terminal unit coordinates. -/
def coordKind : Fin 9 → CoordKind := fun i =>
  if i.val < 7 then CoordKind.physicalPrime else CoordKind.terminalUnit

/-- **`physicalPrimeCoords_card`.**  `LEAN_PROVED`.  Exactly seven nonterminal, nonunit
physical prime coordinates. -/
theorem physicalPrimeCoords_card :
    ((Finset.univ : Finset (Fin 9)).filter
      (fun i => coordKind i = CoordKind.physicalPrime)).card = 7 := by
  decide

/-- **`terminalUnitCoords_card`.**  `LEAN_PROVED`.  Exactly two terminal unit coordinates. -/
theorem terminalUnitCoords_card :
    ((Finset.univ : Finset (Fin 9)).filter
      (fun i => coordKind i = CoordKind.terminalUnit)).card = 2 := by
  decide

/-- The two classes exhaust the nine Ford coordinates, matching `N = 9`. -/
theorem coordKind_partition :
    ((Finset.univ : Finset (Fin 9)).filter
        (fun i => coordKind i = CoordKind.physicalPrime)).card +
      ((Finset.univ : Finset (Fin 9)).filter
        (fun i => coordKind i = CoordKind.terminalUnit)).card = 9 := by
  decide

/-! ## §8.  The deterministic canonical singleton `i(U)` -/

/-- **`canonicalSingleton`** — the deterministic canonical singleton selection `i(U)`: the
least prime coordinate outside the branch label `U`.  It is a *function* of `U` alone, hence
deterministic, and it is characterised below by minimality. -/
def canonicalSingleton (U : Finset (Fin 7)) : Fin 7 := (Uᶜ : Finset (Fin 7)).min.getD 0

/-- The complement of a small branch label is nonempty. -/
theorem compl_nonempty_of_card_le_three {U : Finset (Fin 7)} (h : U.card ≤ 3) :
    (Uᶜ : Finset (Fin 7)).Nonempty := by
  rw [← Finset.card_pos, Finset.card_compl]
  simp only [Fintype.card_fin]
  omega

/-- The canonical singleton lies outside `U`. -/
theorem canonicalSingleton_not_mem {U : Finset (Fin 7)} (h : U.card ≤ 3) :
    canonicalSingleton U ∉ U := by
  obtain ⟨a, ha⟩ := Finset.min_of_nonempty (compl_nonempty_of_card_le_three h)
  have he : canonicalSingleton U = a := by unfold canonicalSingleton; rw [ha]; rfl
  have : a ∈ (Uᶜ : Finset (Fin 7)) := Finset.mem_of_min ha
  rw [he]
  simpa using this

/-- Minimality: the canonical singleton is the least available coordinate. -/
theorem canonicalSingleton_le {U : Finset (Fin 7)} (h : U.card ≤ 3) {j : Fin 7} (hj : j ∉ U) :
    canonicalSingleton U ≤ j := by
  obtain ⟨a, ha⟩ := Finset.min_of_nonempty (compl_nonempty_of_card_le_three h)
  have he : canonicalSingleton U = a := by unfold canonicalSingleton; rw [ha]; rfl
  have hle : (a : WithTop (Fin 7)) ≤ (j : WithTop (Fin 7)) :=
    ha ▸ Finset.min_le (by simpa using hj)
  rw [he]
  exact_mod_cast hle

/-- **`canonicalSingleton_unique`.**  `LEAN_PROVED`.  The selection is pinned by its
specification: any coordinate outside `U` that is `≤` all coordinates outside `U` equals
`i(U)`.  In particular the selection rule is deterministic. -/
theorem canonicalSingleton_unique {U : Finset (Fin 7)} (h : U.card ≤ 3) {a : Fin 7}
    (ha : a ∉ U) (hmin : ∀ j ∉ U, a ≤ j) : a = canonicalSingleton U :=
  le_antisymm (hmin _ (canonicalSingleton_not_mem h)) (canonicalSingleton_le h ha)

/-! ## §9.  The six-prime complement and the depth-`6` theorem -/

/-- **`sixPrimeComplement`** — the six prime coordinates other than the canonical
singleton. -/
def sixPrimeComplement (U : Finset (Fin 7)) : Finset (Fin 7) :=
  (Finset.univ : Finset (Fin 7)).erase (canonicalSingleton U)

/-- The complement depth. -/
def complementDepth (U : Finset (Fin 7)) : ℕ := (sixPrimeComplement U).card

/-- **`complementDepth_eq_six`.**  `LEAN_PROVED`.  The six-prime complement really has
depth `6`. -/
theorem complementDepth_eq_six (U : Finset (Fin 7)) : complementDepth U = 6 := by
  simp [complementDepth, sixPrimeComplement, Finset.card_erase_of_mem]

/-- The canonical singleton is not in its own complement. -/
theorem canonicalSingleton_not_mem_complement (U : Finset (Fin 7)) :
    canonicalSingleton U ∉ sixPrimeComplement U := by
  simp [sixPrimeComplement]

/-- The singleton together with the six-prime complement recovers all seven prime
coordinates. -/
theorem singleton_union_complement (U : Finset (Fin 7)) :
    insert (canonicalSingleton U) (sixPrimeComplement U) = (Finset.univ : Finset (Fin 7)) := by
  simp [sixPrimeComplement, Finset.insert_erase]

/-! ## §10.  Balanced-seven divisor depth and `H^*(P) = -20` -/

/-- The depth-`3` divisor subsets of the six-prime complement. -/
def depthSubsets (U : Finset (Fin 7)) : Finset (Finset (Fin 7)) :=
  (sixPrimeComplement U).powersetCard 3

/-- **`balancedSeven_divisorDepth`.**  `LEAN_PROVED`.  The balanced-seven divisor-depth
theorem: with surviving divisor depth `3`, the six-prime complement carries exactly
`C(6,3) = 20` depth-`3` divisor patterns. -/
theorem balancedSeven_divisorDepth (U : Finset (Fin 7)) : (depthSubsets U).card = 20 := by
  rw [depthSubsets, Finset.card_powersetCard,
    show (sixPrimeComplement U).card = 6 from complementDepth_eq_six U]
  decide

/-- **`hStar`** — the balanced-seven Ford functional `H^*`: minus the number of depth-`3`
divisor patterns carried by the six-prime complement. -/
def hStar (U : Finset (Fin 7)) : ℤ := -((depthSubsets U).card : ℤ)

/-- **`hStar_eq_neg_twenty`.**  `LEAN_PROVED`.  `H^*(P) = -20` for every branch label. -/
theorem hStar_eq_neg_twenty (U : Finset (Fin 7)) : hStar U = -20 := by
  rw [hStar, balancedSeven_divisorDepth]
  norm_num

/-- **`hStar_eq_balancedSevenLowSum`.**  `LEAN_PROVED`.  Consistency with the already banked
balanced-seven binomial value `∑_{j≤3} (−1)^j C(7,j) = −20`
(`Erdos287.BalancedSeven.balancedSeven_lowSum_eq_neg20`): the divisor-depth reading of `H^*`
introduced here agrees with the banked alternating-sum reading, so no second, incompatible
`−20` has been created. -/
theorem hStar_eq_balancedSevenLowSum (U : Finset (Fin 7)) :
    hStar U = ∑ j ∈ Finset.range 4, (-1 : ℤ) ^ j * (Nat.choose 7 j) := by
  rw [hStar_eq_neg_twenty, Erdos287.BalancedSeven.balancedSeven_lowSum_eq_neg20]

/-- `H^*` is branch-independent: the value `-20` does not depend on `U`. -/
theorem hStar_constant (U V : Finset (Fin 7)) : hStar U = hStar V := by
  rw [hStar_eq_neg_twenty, hStar_eq_neg_twenty]

/-! ## §11.  The physical `k = 0` (7.20) conditions -/

/-- **`PhysicalK0Conditions720`** — the package of physical `k = 0` conditions (7.20) for the
source-specific packet: level zero, empty auxiliary index set, no `d`-variables, divisor
depth `3`, balanced seven, the `N = 9` Ford coordinate count with its `7 + 2` split, the
`64`-branch census, and the `H^* = -20` value. -/
structure PhysicalK0Conditions720 (C : SP2FixedCertificateData) (U : Finset (Fin 7)) :
    Prop where
  /-- `k = 0`. -/
  k_zero : C.k = 0
  /-- `J = ∅`. -/
  J_empty : C.J = ∅
  /-- No `d_{h,j}` variables. -/
  no_d_variables : dIndex C = ∅
  /-- Divisor depth `3`. -/
  depth_three : C.r = 3
  /-- Balanced seven. -/
  omega_seven : C.bigOmega = 7
  /-- Ford coordinate count `N = 9`. -/
  coord_nine : coordCount U = 9
  /-- Seven physical prime coordinates. -/
  seven_prime_coords :
    ((Finset.univ : Finset (Fin 9)).filter
      (fun i => coordKind i = CoordKind.physicalPrime)).card = 7
  /-- Two terminal unit coordinates. -/
  two_unit_coords :
    ((Finset.univ : Finset (Fin 9)).filter
      (fun i => coordKind i = CoordKind.terminalUnit)).card = 2
  /-- The `64`-branch census. -/
  sixtyFour_branches : fordBranches.card = 64
  /-- The canonical singleton is available. -/
  singleton_available : canonicalSingleton U ∉ U
  /-- Complement depth `6`. -/
  complement_six : complementDepth U = 6
  /-- `H^* = -20`. -/
  hStar_value : hStar U = -20

/-- **`physicalK0_of_strictCell`.**  `LEAN_PROVED` (conditional on the strict-cell
hypotheses).  Every physical `k = 0` (7.20) condition is a *consequence* of the explicit
strict-cell hypotheses; none of them is an extra assumption. -/
theorem physicalK0_of_strictCell {C : SP2FixedCertificateData} {U : Finset (Fin 7)}
    (h : StrictCellHypotheses C U) : PhysicalK0Conditions720 C U :=
  { k_zero := strictCell_k_zero h
    J_empty := strictCell_J_empty h
    no_d_variables := dIndex_eq_empty h
    depth_three := h.depth_three
    omega_seven := h.omega_seven
    coord_nine := ford_coordCount_eq_nine U
    seven_prime_coords := physicalPrimeCoords_card
    two_unit_coords := terminalUnitCoords_card
    sixtyFour_branches := fordBranches_card
    singleton_available := canonicalSingleton_not_mem h.branch_small
    complement_six := complementDepth_eq_six U
    hStar_value := hStar_eq_neg_twenty U }

/-! ## §12.  No generic subsum inclusion–exclusion: exact mass factorisation -/

/-- The cell has exactly `∏ |λ_i|` prime vectors. -/
theorem cellVectors_card (C : SP2FixedCertificateData) :
    (cellVectors C).card = ∏ i, (C.lam i).card :=
  Fintype.card_piFinset C.lam

/-- **`omegaSharp_total_mass`.**  `LEAN_PROVED`.

The total pushforward mass is the *exact* product of the slot sizes.  No generic subsum
inclusion–exclusion is needed for this source-specific packet: the fibres of the pushforward
partition the cell, so summing `Ω^♯_C` over the image is an exact identity. -/
theorem omegaSharp_total_mass (C : SP2FixedCertificateData) :
    ∑ n ∈ (cellVectors C).image pushforward, OmegaSharp C unitWeight n
      = ((∏ i, (C.lam i).card : ℕ) : ℤ) := by
  have h : ∀ n ∈ (cellVectors C).image pushforward,
      OmegaSharp C unitWeight n = (((cellVectors C).filter (fun v => pushforward v = n)).card : ℤ) := by
    intro n _
    rw [OmegaSharp_unitWeight, omegaSharpFibre]
  rw [Finset.sum_congr rfl h, ← Nat.cast_sum, ← cellVectors_card C]
  congr 1
  exact (Finset.card_eq_sum_card_image pushforward (cellVectors C)).symm

/-- **`productWeight_total_mass`.**  `LEAN_PROVED`.

The weighted version: a product (rank-one) weight integrates to the exact product of the
slot masses.  Again an exact identity, with no inclusion–exclusion correction. -/
theorem productWeight_total_mass (C : SP2FixedCertificateData) (f : Fin 7 → ℕ → ℤ) :
    ∑ v ∈ cellVectors C, productWeight f v = ∏ i, ∑ p ∈ C.lam i, f i p := by
  simp only [productWeight, cellVectors]
  exact (Finset.prod_univ_sum C.lam f).symm

/-! ## §13.  Zero Ford hard-condition Perron contour count -/

/-- The Ford *hard* conditions of the packet are indexed by the `d`-variables: with no
`d`-variables there is no hard condition, hence no Perron contour to open. -/
def fordHardConditions (C : SP2FixedCertificateData) : Finset (ℕ × ℕ) := dIndex C

/-- The number of Perron contours forced by Ford hard conditions. -/
def perronContourCount (C : SP2FixedCertificateData) : ℕ := (fordHardConditions C).card

/-- **`perronContourCount_eq_zero`.**  `LEAN_PROVED` (conditional).  The source-specific
strict-cell packet opens **zero** Ford hard-condition Perron contours. -/
theorem perronContourCount_eq_zero {C : SP2FixedCertificateData} {U : Finset (Fin 7)}
    (h : StrictCellHypotheses C U) : perronContourCount C = 0 := by
  rw [perronContourCount, fordHardConditions, dIndex_eq_empty h]
  simp

/-! ## §14.  The singleton Type-II window from the physical prime size bounds -/

/-- **`singleton_mem_window`.**  `LEAN_PROVED`.

The singleton coordinate of any cell vector lies in the window `[Y, Z]` cut out by the
physical prime size bounds.  This is the *window*, not the analytic Type-II estimate. -/
theorem singleton_mem_window {C : SP2FixedCertificateData} {Y Z : ℕ} {U : Finset (Fin 7)}
    (hlo : ∀ (i : Fin 7), ∀ p ∈ C.lam i, Y ≤ p) (hhi : ∀ (i : Fin 7), ∀ p ∈ C.lam i, p ≤ Z)
    {v : Fin 7 → ℕ} (hv : v ∈ cellVectors C) :
    v (canonicalSingleton U) ∈ Finset.Icc Y Z := by
  have hmem : ∀ i, v i ∈ C.lam i := by
    intro i; exact (Fintype.mem_piFinset.1 hv) i
  exact Finset.mem_Icc.2
    ⟨hlo _ _ (hmem (canonicalSingleton U)), hhi _ _ (hmem (canonicalSingleton U))⟩

/-- **`complement_pushforward_bounds`.**  `LEAN_PROVED`.

The complementary six coordinates push forward into the window `[Y^6, Z^6]`.  Combined with
`singleton_mem_window` this is the exact singleton Type-II *window* of the packet. -/
theorem complement_pushforward_bounds {C : SP2FixedCertificateData} {Y Z : ℕ}
    (U : Finset (Fin 7))
    (hlo : ∀ (i : Fin 7), ∀ p ∈ C.lam i, Y ≤ p) (hhi : ∀ (i : Fin 7), ∀ p ∈ C.lam i, p ≤ Z)
    {v : Fin 7 → ℕ} (hv : v ∈ cellVectors C) :
    Y ^ 6 ≤ ∏ i ∈ sixPrimeComplement U, v i ∧
      ∏ i ∈ sixPrimeComplement U, v i ≤ Z ^ 6 := by
  have hmem : ∀ i, v i ∈ C.lam i := fun i => (Fintype.mem_piFinset.1 hv) i
  have hcard : (sixPrimeComplement U).card = 6 := complementDepth_eq_six U
  constructor
  · have h1 : ∏ _i ∈ sixPrimeComplement U, Y ≤ ∏ i ∈ sixPrimeComplement U, v i :=
      Finset.prod_le_prod' (fun i _ => hlo i _ (hmem i))
    rwa [Finset.prod_const, hcard] at h1
  · have h2 : ∏ i ∈ sixPrimeComplement U, v i ≤ ∏ _i ∈ sixPrimeComplement U, Z :=
      Finset.prod_le_prod' (fun i _ => hhi i _ (hmem i))
    rwa [Finset.prod_const, hcard] at h2

/-- The full pushforward of a cell vector is confined to `[Y^7, Z^7]`. -/
theorem pushforward_bounds {C : SP2FixedCertificateData} {Y Z : ℕ}
    (hlo : ∀ (i : Fin 7), ∀ p ∈ C.lam i, Y ≤ p) (hhi : ∀ (i : Fin 7), ∀ p ∈ C.lam i, p ≤ Z)
    {v : Fin 7 → ℕ} (hv : v ∈ cellVectors C) :
    Y ^ 7 ≤ pushforward v ∧ pushforward v ≤ Z ^ 7 := by
  have hmem : ∀ i, v i ∈ C.lam i := fun i => (Fintype.mem_piFinset.1 hv) i
  constructor
  · have h1 : ∏ _i : Fin 7, Y ≤ ∏ i, v i := Finset.prod_le_prod' (fun i _ => hlo i _ (hmem i))
    simpa [pushforward] using h1
  · have h2 : ∏ i, v i ≤ ∏ _i : Fin 7, Z := Finset.prod_le_prod' (fun i _ => hhi i _ (hmem i))
    simpa [pushforward] using h2

/-! ## §15.  Counterguard: arbitrary weights are not product-separable -/

/-- The "diagonal" weight: `1` when the first two prime coordinates agree, `0` otherwise. -/
def diagonalWeight : (Fin 7 → ℕ) → ℤ := fun v => if v 0 = v 1 then 1 else 0

/-- The test vector with prescribed first two coordinates and `1` elsewhere. -/
def testVector (a b : ℕ) : Fin 7 → ℕ := fun i => if i = 0 then a else if i = 1 then b else 1

/-- The product of a slot family along a test vector. -/
theorem prod_testVector (f : Fin 7 → ℕ → ℤ) (a b : ℕ) :
    ∏ i, f i (testVector a b i)
      = f 0 a * f 1 b * (f 2 1 * f 3 1 * f 4 1 * f 5 1 * f 6 1) := by
  simp [Fin.prod_univ_seven, testVector]
  ring

/-- The diagonal weight of a test vector. -/
theorem diagonalWeight_testVector (a b : ℕ) :
    diagonalWeight (testVector a b) = if a = b then 1 else 0 := by
  simp [diagonalWeight, testVector]

/-- **`weight_not_product_separable`.**  `LEAN_PROVED`.

A counterguard: an arbitrary cell weight `Ω` need **not** be rank-one / product separable.
Consequently, no compiler may replace a general `C.Om` by `∏ i, f i (v i)`; the product form
is a *bridge field*, not a theorem. -/
theorem weight_not_product_separable :
    ¬ ∃ f : Fin 7 → ℕ → ℤ, ∀ v : Fin 7 → ℕ, diagonalWeight v = ∏ i, f i (v i) := by
  rintro ⟨f, hf⟩
  have h22 := hf (testVector 2 2)
  have h33 := hf (testVector 3 3)
  have h23 := hf (testVector 2 3)
  rw [prod_testVector, diagonalWeight_testVector, if_pos rfl] at h22
  rw [prod_testVector, diagonalWeight_testVector, if_pos rfl] at h33
  rw [prod_testVector, diagonalWeight_testVector, if_neg (by norm_num)] at h23
  set t : ℤ := f 2 1 * f 3 1 * f 4 1 * f 5 1 * f 6 1
  have key : (f 0 2 * f 1 2 * t) * (f 0 3 * f 1 3 * t)
      = (f 0 2 * f 1 3 * t) * (f 0 3 * f 1 2 * t) := by ring
  rw [← h22, ← h33, ← h23] at key
  norm_num at key

/-! ## §16.  Deterministic finite Cauchy / product-energy interfaces -/

/-- **`finite_cauchy_schwarz`.**  `LEAN_PROVED`.  The deterministic finite Cauchy–Schwarz
interface used by the packet: no asymptotics, no implicit constants. -/
theorem finite_cauchy_schwarz {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 :=
  Finset.sum_mul_sq_le_sq_mul_sq s f g

/-- **`productEnergy_factorises`.**  `LEAN_PROVED`.  The deterministic finite product-energy
interface: the `ℓ²` energy of a rank-one cell weight is the exact product of the slot
energies. -/
theorem productEnergy_factorises (C : SP2FixedCertificateData) (f : Fin 7 → ℕ → ℝ) :
    ∑ v ∈ cellVectors C, (∏ i, f i (v i)) ^ 2 = ∏ i, ∑ p ∈ C.lam i, (f i p) ^ 2 := by
  rw [cellVectors, Finset.prod_univ_sum C.lam (fun i p => (f i p) ^ 2)]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  exact (Finset.prod_pow Finset.univ 2 (fun i => f i (v i))).symm

/-- The Cauchy–Schwarz interface applied to the cell: the pairing of two rank-one weights is
controlled by the two exact product energies. -/
theorem cell_cauchy_productEnergy (C : SP2FixedCertificateData) (f g : Fin 7 → ℕ → ℝ) :
    (∑ v ∈ cellVectors C, (∏ i, f i (v i)) * (∏ i, g i (v i))) ^ 2
      ≤ (∏ i, ∑ p ∈ C.lam i, (f i p) ^ 2) * (∏ i, ∑ p ∈ C.lam i, (g i p) ^ 2) := by
  have h := finite_cauchy_schwarz (cellVectors C) (fun v => ∏ i, f i (v i))
    (fun v => ∏ i, g i (v i))
  rw [productEnergy_factorises C f, productEnergy_factorises C g] at h
  exact h

end StrictCellSingleton
end Erdos287
