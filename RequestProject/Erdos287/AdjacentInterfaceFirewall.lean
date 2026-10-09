import Mathlib
import RequestProject.Erdos287.CompensatedMeasure

/-!
# Erdős #287 effectivity — the adjacent-interface firewall for `Z_n = n·Ê(z/n)` (§53)

```
DENSITY TERMS CANCEL EXACTLY            : KERNEL-PROVED
ARITHMETIC PREFIX SURVIVES              : KERNEL-PROVED
EMPTY SHORT SHELL ⇏ ZERO DIFFERENCE     : KERNEL-PROVED (finite counterexample)
"ADJACENT SHELL ONLY" ROUTE             : RETIRED_NONCLOSING
```

Write, with a fixed local-coefficient range `D₀`,

    Ê*_M(z; n) = G_M(⌊z/n⌋) − (z/(2n))·Λ_M(D₀),   Λ_M(D₀) = ∑_{d ≤ D₀} η_M(d)/d,
    Z_n       = n · Ê*_M(z; n).

The density part of `Z_n` is `(z/2)·Λ_M(D₀)`, **independent of `n`**, so the adjacent
difference `Z_n − Z_{n+1}` cancels it exactly and leaves the purely arithmetic prefix

    Z_n − Z_{n+1} = n·G_M(⌊z/n⌋) − (n+1)·G_M(⌊z/(n+1)⌋).

`adjacent_emptyShell_not_zero` is the finite counterexample: when the short shell
`(z/(n+1), z/n]` contains no integer (i.e. `⌊z/n⌋ = ⌊z/(n+1)⌋`) the difference equals
`−G_M(⌊z/n⌋)`, which is nonzero already at `M = 1, z = 3, n = 2`.  Hence controlling the
short shell alone can never close the adjacent-interface difference, and the
"adjacent shell only" route is tagged `RETIRED_NONCLOSING`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §53.1  The interface object -/

/-- The fixed-range local density coefficient `Λ_M(D₀) = ∑_{d ≤ D₀} η_M(d)/d`. -/
def densityCoeff (M D₀ : ℕ) : ℚ := ∑ d ∈ Finset.Icc 1 D₀, etaM M d / d

/-- The interface-compensated remainder `Ê*_M(z;n) = G_M(⌊z/n⌋) − (z/(2n))Λ_M(D₀)`. -/
def EhatStar (M D₀ z n : ℕ) : ℚ :=
  GM M (z / n) - ((z : ℚ) / (2 * n)) * densityCoeff M D₀

/-- The adjacent-interface object `Z_n = n·Ê*_M(z;n)`. -/
def Zadj (M D₀ z n : ℕ) : ℚ := (n : ℚ) * EhatStar M D₀ z n

/-- **`Zadj_density_constant`.**  `KERNEL-PROVED`.  The density part of `Z_n` does not depend
on `n`: it equals `(z/2)Λ_M(D₀)` for every `n ≥ 1`. -/
theorem Zadj_density_constant (M D₀ z : ℕ) {n : ℕ} (hn : 0 < n) :
    (n : ℚ) * (((z : ℚ) / (2 * n)) * densityCoeff M D₀)
      = ((z : ℚ) / 2) * densityCoeff M D₀ := by
  have hn' : (n : ℚ) ≠ 0 := by positivity
  field_simp

/-- **`adjacent_interface_identity`.**  `KERNEL-PROVED`.  The exact adjacent-interface
identity: the density terms cancel and a purely arithmetic prefix survives. -/
theorem adjacent_interface_identity (M D₀ z : ℕ) {n : ℕ} (hn : 0 < n) :
    Zadj M D₀ z n - Zadj M D₀ z (n + 1)
      = (n : ℚ) * GM M (z / n) - ((n : ℚ) + 1) * GM M (z / (n + 1)) := by
  have h1 := Zadj_density_constant M D₀ z hn
  have h2 := Zadj_density_constant M D₀ z (Nat.succ_pos n)
  rw [Zadj, Zadj, EhatStar, EhatStar, mul_sub, mul_sub]
  push_cast at h2 ⊢
  rw [h1, h2]
  ring

/-! ## §53.2  The empty-short-shell counterexample -/

/-- The short shell between two adjacent interfaces: the integers `t` with
`z/(n+1) < t ≤ z/n`. -/
def shortShell (z n : ℕ) : Finset ℕ := Finset.Ioc (z / (n + 1)) (z / n)

lemma shortShell_empty_iff (z n : ℕ) : shortShell z n = ∅ ↔ z / n ≤ z / (n + 1) := by
  rw [shortShell, Finset.Ioc_eq_empty_iff]
  constructor
  · intro h; omega
  · intro h; omega

/-- **`adjacent_emptyShell_difference`.**  `KERNEL-PROVED`.  If the short shell is empty then
the adjacent-interface difference is `−G_M(⌊z/n⌋)` — *not* zero in general. -/
theorem adjacent_emptyShell_difference (M D₀ z : ℕ) {n : ℕ} (hn : 0 < n)
    (hshell : z / n = z / (n + 1)) :
    Zadj M D₀ z n - Zadj M D₀ z (n + 1) = - GM M (z / n) := by
  rw [adjacent_interface_identity M D₀ z hn, ← hshell]
  ring

/-- **`adjacent_emptyShell_not_zero`.**  `KERNEL-PROVED`.  An **empty short shell does not
imply a zero adjacent-interface difference**: at `M = 1`, `D₀ = 1`, `z = 3`, `n = 2` the
shell is empty while the difference equals `−1`.  This retires the "adjacent shell only"
route. -/
theorem adjacent_emptyShell_not_zero :
    shortShell 3 2 = ∅ ∧ Zadj 1 1 3 2 - Zadj 1 1 3 3 = -1 := by
  have hG : GM 1 1 = 1 := by
    simp [GM, gz]
  refine ⟨by decide, ?_⟩
  have h := adjacent_emptyShell_difference 1 1 3 (n := 2) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, hG]

/-- Status tag for the retired route. -/
inductive AdjacentRouteStatus
  | retiredNonclosing
  | live
  deriving DecidableEq, Repr

/-- The "adjacent shell only" route is recorded `RETIRED_NONCLOSING`. -/
def adjacentShellOnlyRoute : AdjacentRouteStatus := .retiredNonclosing

/-- **`adjacent_shell_only_retired`.**  `KERNEL-PROVED` (bookkeeping).  The route is tagged
retired, and the tag is justified by `adjacent_emptyShell_not_zero`. -/
theorem adjacent_shell_only_retired :
    adjacentShellOnlyRoute = AdjacentRouteStatus.retiredNonclosing ∧
      adjacentShellOnlyRoute ≠ AdjacentRouteStatus.live :=
  ⟨rfl, by decide⟩

end Effectivity
end Erdos287
