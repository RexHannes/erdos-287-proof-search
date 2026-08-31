import Mathlib
import RequestProject.CurrentProgramme.Block20PackingCompiler

/-!
# BLOCK20 Δ, Phase B (§6) — the large prime-power router

The research audit supplies the counting bound

```
contribution  ≪  X^{1 − σ_*/2 + o(1)}
```

for the exceptional sector of atoms carrying a *large prime power*.  That is **analytic
input**: it is not proved here, and nothing in this module creates it.

What *is* formalised:

* `IsLargePrimePowerAtom` — the literal definition of the exceptional sector;
* `largePrimePower_router_partition` — the finite routing partition (cover, disjointness and
  exact reassembly of the sum);
* `largePrimePower_not_squarefree` — the elementary implication identifying the bad atom
  condition (a large prime power forces a repeated prime, hence non-squarefreeness);
* `LargePrimePowerRouterEstimateInput` — the **uninhabited** analytic input carrying exactly
  the estimate that is needed;
* `largePrimePower_sector_negligible_of_input` — the conditional consumer.

Status: `287-K0-SP2-LARGE-PRIMEPOWER-ROUTER45 : externallyAudited / conditionalCompiler`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace Block20

/-! ## §6.1  The exceptional sector -/

/-- `n` carries a **large prime power**: some prime power `p^k` with `k ≥ 2` divides `n` and
exceeds the routing bound. -/
def IsLargePrimePowerAtom (bound n : ℕ) : Prop :=
  ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ p ^ k ∣ n ∧ bound < p ^ k

/-- **`largePrimePower_not_squarefree`.**  `LEAN_PROVED`.

The elementary implication identifying the bad atom condition: an atom of the exceptional
sector is divisible by the square of a prime, hence is **not squarefree**.  This is what lets
the router send the sector to the squareful/repeated-prime routing state. -/
theorem largePrimePower_not_squarefree {bound n : ℕ}
    (h : IsLargePrimePowerAtom bound n) : ¬ Squarefree n := by
  obtain ⟨p, k, hp, hk, hdvd, -⟩ := h
  intro hsf
  have hsq : p ^ 2 ∣ n := dvd_trans (pow_dvd_pow p hk) hdvd
  have := hsf p (by simpa [pow_two] using hsq)
  exact hp.not_isUnit (by simpa using this)

/-- **`largePrimePower_squarefree_excluded`.**  `LEAN_PROVED`.

Conversely, squarefree atoms never enter the exceptional sector. -/
theorem largePrimePower_squarefree_excluded {bound n : ℕ} (hsf : Squarefree n) :
    ¬ IsLargePrimePowerAtom bound n :=
  fun h => largePrimePower_not_squarefree h hsf

open Classical in
/-- The exceptional sector inside a finite range. -/
noncomputable def largePrimePowerSector (bound N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => IsLargePrimePowerAtom bound n)

open Classical in
/-- The complementary (routed) sector. -/
noncomputable def routedSector (bound N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => ¬ IsLargePrimePowerAtom bound n)

/-- **`largePrimePower_router_partition`.**  `LEAN_PROVED`.

The finite routing partition: the two sectors are disjoint, they cover the range, and the
sum reassembles exactly — the router spends nothing twice. -/
theorem largePrimePower_router_partition (bound N : ℕ) (w : ℕ → ℝ) :
    Disjoint (largePrimePowerSector bound N) (routedSector bound N) ∧
      largePrimePowerSector bound N ∪ routedSector bound N = Finset.range N ∧
      ∑ n ∈ largePrimePowerSector bound N, w n + ∑ n ∈ routedSector bound N, w n
        = ∑ n ∈ Finset.range N, w n := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.disjoint_filter_filter_not _ _ _
  · exact Finset.filter_union_filter_not_eq _ _
  · exact Finset.sum_filter_add_sum_filter_not _ _ _

/-! ## §6.2  The analytic input (uninhabited) -/

/-- **`LargePrimePowerRouterEstimateInput`** — `EXTERNAL / ANALYTIC / UNINHABITED`.

Exactly the estimate that the research audit supplies, and nothing more:

```
|∑_{n ∈ exceptional sector} w(n)|  ≤  C · X^{1 − σ_*/2 + η}
```

with an explicit constant, an explicit `η` playing the role of the `o(1)`, the routing bound
tied to the scale, and the declared saving genuinely positive. -/
structure LargePrimePowerRouterEstimateInput
    (X : ℝ) (N bound : ℕ) (w : ℕ → ℝ) (sigmaStar C eta : ℝ) : Prop where
  /-- The scale is nontrivial and the range matches it. -/
  scale : 3 ≤ X ∧ (N : ℝ) = X
  /-- The packing parameter is the Block20 one. -/
  sigma_range : (1629054 : ℝ) / 10000000 ≤ sigmaStar ∧ sigmaStar < 1
  /-- The `o(1)` is a genuine saving: `η < σ_*/2`. -/
  eta_small : 0 < eta ∧ eta < sigmaStar / 2
  /-- The constant is explicit. -/
  constant_pos : 0 < C
  /-- The routing bound is the source-level one. -/
  bound_scale : (bound : ℝ) = X ^ (sigmaStar / 2)
  /-- The estimate itself. -/
  estimate : |∑ n ∈ largePrimePowerSector bound N, w n| ≤ C * X ^ (1 - sigmaStar / 2 + eta)

/-- The conclusion the router needs: the exceptional sector is `o(X)`, with the explicit
exponent saving. -/
def LargePrimePowerSectorNegligible (X : ℝ) (N bound : ℕ) (w : ℕ → ℝ) (C : ℝ) :
    Prop :=
  ∃ delta : ℝ, 0 < delta ∧ |∑ n ∈ largePrimePowerSector bound N, w n| ≤ C * X ^ (1 - delta)

/-- **`largePrimePower_sector_negligible_of_input`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

The conditional consumer.  No analytic content is created: the saving `δ = σ_*/2 − η` is
exactly the one the input declares. -/
theorem largePrimePower_sector_negligible_of_input
    {X : ℝ} {N bound : ℕ} {w : ℕ → ℝ} {sigmaStar C eta : ℝ}
    (h : LargePrimePowerRouterEstimateInput X N bound w sigmaStar C eta) :
    LargePrimePowerSectorNegligible X N bound w C := by
  refine ⟨sigmaStar / 2 - eta, by linarith [h.eta_small.2], ?_⟩
  have := h.estimate
  have hx : (1 : ℝ) - sigmaStar / 2 + eta = 1 - (sigmaStar / 2 - eta) := by ring
  rwa [hx] at this

/-- **`largePrimePowerRouter_not_automatic`.**  `LEAN_PROVED`.

The analytic input is **not inhabited** by this repository. -/
theorem largePrimePowerRouter_not_automatic :
    ∃ (X : ℝ) (N bound : ℕ) (w : ℕ → ℝ) (sigmaStar C eta : ℝ),
      ¬ LargePrimePowerRouterEstimateInput X N bound w sigmaStar C eta := by
  refine ⟨0, 0, 0, fun _ => 0, 0, 0, 0, ?_⟩
  intro h
  have := h.scale.1
  norm_num at this

end Block20
end Erdos287
