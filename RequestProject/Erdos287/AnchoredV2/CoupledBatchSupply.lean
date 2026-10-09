import RequestProject.Erdos287.AnchoredV2.TrackedKernel
import RequestProject.Erdos287.AnchoredV2.CoupledCharge

/-!
# Anchored V2 — the finite coupled-batch supply record

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The large-cutoff research arguments rely on external prime-supply / Jacobsthal style estimates.
This file **separates the finite algebra from that supply**: a `CoupledBatchSupply` is a purely
finite record listing, for a tracked-prime kernel and one tracked odd prime `p` with retained
valuation exponent `e`,

* the optional repair sites and their physical positions (fresh, pairwise distinct);
* their left/right neighbours, with proofs that the neighbours are permanently selected and
  retained, and that no two sites are adjacent;
* proofs that the inherited high-power equations and the truncated prime-power equations only
  depend on the retained positions (so the repair denominators preserve them);
* the charge of each site modulo `2^e` and modulo `p`, both units;
* enough sites (`2^e p − 1`) to attain every required batch charge.

**No asymptotic existence statement occurs inside the record.**  The optional proposition
`FixedPowerCoupledSupply` is the place where an external (currently non-formal) supply theorem
would be plugged in; it is deliberately left uninhabited.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV2

open TrackedPrimeKernel

/-- A finite coupled-batch supply record for the tracked kernel `K`, tracked odd prime `p` and
retained valuation exponent `e`. -/
structure CoupledBatchSupply (K : TrackedPrimeKernel) (p e : ℕ) where
  /-- the tracked prime is prime -/
  p_prime : p.Prime
  /-- the tracked prime is odd -/
  p_odd : p ≠ 2
  /-- the retained valuation exponent is positive -/
  e_pos : 1 ≤ e
  /-- the number of optional repair sites -/
  n : ℕ
  /-- there are enough sites to attain every batch charge -/
  enough : 2 ^ e * p - 1 ≤ n
  /-- the physical position of each repair site -/
  pos : Fin n → ℕ
  /-- distinct sites occupy distinct physical positions -/
  pos_inj : Function.Injective pos
  /-- the repair sites are fresh: they are not retained kernel positions -/
  pos_fresh : ∀ i, pos i ∉ K.positions
  /-- the left neighbour of each repair site -/
  left : Fin n → ℕ
  /-- the right neighbour of each repair site -/
  right : Fin n → ℕ
  /-- the neighbours are permanently selected -/
  nbr_pinned : ∀ i, left i ∈ K.pins ∧ right i ∈ K.pins
  /-- the neighbours are retained kernel positions -/
  nbr_retained : ∀ i, left i ∈ K.positions ∧ right i ∈ K.positions
  /-- no two repair sites are adjacent -/
  sites_nonadjacent : ∀ i j, (pos i, pos j) ∉ K.adjacency
  /-- the inherited high-power equations only depend on the retained positions -/
  highPower_local : ∀ g ∈ K.highPower, ∀ w w' : ℕ → Bool,
    (∀ x ∈ K.positions, w x = w' x) → g w = g w'
  /-- the truncated prime-power equations only depend on the retained positions -/
  layerEq_local : ∀ q ∈ K.tracked, ∀ w w' : ℕ → Bool,
    (∀ x ∈ K.positions, w x = w' x) → K.layerEq q w = K.layerEq q w'
  /-- the `2^e`-charge of each site -/
  a : Fin n → ZMod (2 ^ e)
  /-- the `p`-charge of each site -/
  b : Fin n → ZMod p
  /-- the `2^e`-charges are units -/
  a_unit : ∀ i, IsUnit (a i)
  /-- the `p`-charges are units -/
  b_unit : ∀ i, IsUnit (b i)

/-- **The asymptotic supply firewall.**  `FixedPowerCoupledSupply M R p e` is the *optional*
proposition asserting that every localised tracked kernel inside the window `[0, M)` with at
least `R` free room admits a finite coupled-batch supply for the tracked prime `p` at exponent
`e`.  Establishing it requires external analytic prime-supply input (Jacobsthal / Bertrand type
bounds) which is **not** formalised here, so the proposition is deliberately left uninhabited:
no axiom, no `sorry`, no instance. -/
def FixedPowerCoupledSupply (M R p e : ℕ) : Prop :=
  ∀ K : TrackedPrimeKernel, K.Localised → K.positions ⊆ Finset.range M →
    R ≤ 2 ^ e * p → Nonempty (CoupledBatchSupply K p e)

/-- **`coupledBatchSupply_of_fixedPower`.**  `KERNEL-PROVED`.  The firewall implication: the
optional fixed-power supply proposition yields the finite coupled-batch supply record used by
the finite extension theorem.  (The hypothesis is an *owner*, not a theorem.) -/
theorem coupledBatchSupply_of_fixedPower {M R p e : ℕ} (h : FixedPowerCoupledSupply M R p e)
    (K : TrackedPrimeKernel) (hloc : K.Localised) (hwin : K.positions ⊆ Finset.range M)
    (hR : R ≤ 2 ^ e * p) : Nonempty (CoupledBatchSupply K p e) :=
  h K hloc hwin hR

end AnchoredV2
end Erdos287
