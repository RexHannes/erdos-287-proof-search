import Mathlib

/-!
# Erdős #287 effectivity — full density / compensation restoration (§17)

```
CANONICAL k = 1 SOURCE IDENTITY        : KERNEL-PROVED (exact algebraic identity)
SPLIT INTO OWNER BLOCKS                : KERNEL-PROVED
D_X REMOVABILITY FIREWALL              : KERNEL-PROVED (explicit finite witness)
SMALLNESS OF ANY BLOCK                 : NOT ASSERTED
```

This module records the exact *current source identity* for the `k = 1` core, in the shape

    T̃_{k=1}
      = P_boundary
        − 4 ∑_z ω(z) V*(z)
        + 4 ∑_z ω(z) W(z²/X)/z · [ Q_{≤5000}(z) + A_{>5000}(z) − D_X(z) ].

Everything here is *bookkeeping algebra*: the identity is true by definition of `Ttilde`,
and the point of the module is that the definition is pinned down exactly, that the
owner blocks (`Q`, `A`, `D_X`, `V*`, `P_boundary`) are separated with no double charge,
and that **no block is asserted to be small**.  The firewall theorem
`DX_term_not_removable` exhibits a finite instance in which dropping the `D_X` block
changes the value, so the density term may not be silently discarded.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-- The exact data of the `k = 1` density/compensation source at a given checkpoint.

* `Zset`      — the finite outer `z`-range actually summed over;
* `omegaW`    — the outer arithmetic weight `ω(z)`;
* `W`         — the smooth cutoff, evaluated at `z²/X`;
* `X`         — the scale;
* `Vstar`     — the `V*` compensation owner;
* `Qle5000`   — the bounded-conductor compiler owner `Q_{≤5000}`;
* `Agt5000`   — the truncated-source owner `A_{>5000}`;
* `DX`        — the density owner `D_X`;
* `Pboundary` — the `P8` boundary-replacement owner. -/
structure DensitySource where
  /-- finite outer `z`-range -/
  Zset : Finset ℕ
  /-- outer arithmetic weight -/
  omegaW : ℕ → ℝ
  /-- smooth cutoff -/
  W : ℝ → ℝ
  /-- scale -/
  X : ℝ
  /-- `V*` compensation owner -/
  Vstar : ℕ → ℝ
  /-- bounded-conductor compiler owner -/
  Qle5000 : ℕ → ℝ
  /-- truncated-source owner -/
  Agt5000 : ℕ → ℝ
  /-- density owner -/
  DX : ℕ → ℝ
  /-- boundary-replacement owner -/
  Pboundary : ℝ

namespace DensitySource

variable (S : DensitySource)

/-- The `V*` block `−4 ∑_z ω(z) V*(z)`. -/
noncomputable def vstarBlock : ℝ := -4 * ∑ z ∈ S.Zset, S.omegaW z * S.Vstar z

/-- The outer cutoff weight `ω(z) · W(z²/X) / z`. -/
noncomputable def outerWeight (z : ℕ) : ℝ := S.omegaW z * S.W ((z : ℝ) ^ 2 / S.X) / z

/-- The compensated bracket `Q_{≤5000}(z) + A_{>5000}(z) − D_X(z)`. -/
noncomputable def bracket (z : ℕ) : ℝ := S.Qle5000 z + S.Agt5000 z - S.DX z

/-- The compensated block `4 ∑_z ω(z) W(z²/X)/z · [ Q + A − D ]`. -/
noncomputable def compBlock : ℝ := 4 * ∑ z ∈ S.Zset, S.outerWeight z * S.bracket z

/-- **The canonical `k = 1` source functional.** -/
noncomputable def Ttilde : ℝ := S.Pboundary + S.vstarBlock + S.compBlock

end DensitySource

open DensitySource

/-- **`Ttilde_source_identity`.**  `KERNEL-PROVED`.  The exact current source identity, written
out in full. -/
theorem Ttilde_source_identity (S : DensitySource) :
    S.Ttilde
      = S.Pboundary
        - 4 * ∑ z ∈ S.Zset, S.omegaW z * S.Vstar z
        + 4 * ∑ z ∈ S.Zset,
            (S.omegaW z * S.W ((z : ℝ) ^ 2 / S.X) / z)
              * (S.Qle5000 z + S.Agt5000 z - S.DX z) := by
  simp only [DensitySource.Ttilde, DensitySource.vstarBlock, DensitySource.compBlock,
    DensitySource.outerWeight, DensitySource.bracket]
  ring

/-- **`Ttilde_split`.**  `KERNEL-PROVED`.  The compensated block splits into the three owner
sums with no cross terms: the `Q_{≤5000}`, `A_{>5000}` and `D_X` owners are charged exactly
once each. -/
theorem Ttilde_split (S : DensitySource) :
    S.Ttilde
      = S.Pboundary + S.vstarBlock
        + 4 * (∑ z ∈ S.Zset, S.outerWeight z * S.Qle5000 z)
        + 4 * (∑ z ∈ S.Zset, S.outerWeight z * S.Agt5000 z)
        - 4 * (∑ z ∈ S.Zset, S.outerWeight z * S.DX z) := by
  simp only [DensitySource.Ttilde, DensitySource.compBlock, DensitySource.bracket, mul_add,
    mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- The same source with the density owner `D_X` deleted. -/
noncomputable def dropDX (S : DensitySource) : DensitySource :=
  { S with DX := fun _ => 0 }

/-- The finite witness: a one-point outer range on which the density owner carries the whole
value of the functional. -/
noncomputable def witnessSource : DensitySource where
  Zset := {1}
  omegaW := fun _ => 1
  W := fun _ => 1
  X := 1
  Vstar := fun _ => 0
  Qle5000 := fun _ => 0
  Agt5000 := fun _ => 0
  DX := fun _ => 1
  Pboundary := 0

/-- **`DX_term_not_removable`.**  `KERNEL-PROVED` firewall.  Deleting the density owner `D_X`
changes the value of the source functional: there is a finite instance with
`T̃ = −4` while the `D_X`-free functional is `0`.  Hence the density term is a genuine owner
and may never be dropped as "negligible" without a proof. -/
theorem DX_term_not_removable :
    witnessSource.Ttilde ≠ (dropDX witnessSource).Ttilde := by
  have h1 : witnessSource.Ttilde = -4 := by
    simp [DensitySource.Ttilde, DensitySource.vstarBlock, DensitySource.compBlock,
      DensitySource.outerWeight, DensitySource.bracket, witnessSource]
  have h2 : (dropDX witnessSource).Ttilde = 0 := by
    simp [DensitySource.Ttilde, DensitySource.vstarBlock, DensitySource.compBlock,
      DensitySource.outerWeight, DensitySource.bracket, witnessSource, dropDX]
  rw [h1, h2]
  norm_num

/-- **`Ttilde_zero_of_all_owners_zero`.**  `KERNEL-PROVED` sanity check: with every owner
vanishing the functional vanishes.  (No smallness of any individual owner is asserted
anywhere in this module.) -/
theorem Ttilde_zero_of_all_owners_zero (S : DensitySource)
    (hP : S.Pboundary = 0) (hV : ∀ z ∈ S.Zset, S.Vstar z = 0)
    (hQ : ∀ z ∈ S.Zset, S.Qle5000 z = 0) (hA : ∀ z ∈ S.Zset, S.Agt5000 z = 0)
    (hD : ∀ z ∈ S.Zset, S.DX z = 0) : S.Ttilde = 0 := by
  have hv : S.vstarBlock = 0 := by
    simp only [DensitySource.vstarBlock]
    rw [Finset.sum_eq_zero (fun z hz => by rw [hV z hz, mul_zero])]
    ring
  have hc : S.compBlock = 0 := by
    simp only [DensitySource.compBlock]
    rw [Finset.sum_eq_zero (fun z hz => by
      have : S.bracket z = 0 := by
        simp only [DensitySource.bracket, hQ z hz, hA z hz, hD z hz]; ring
      rw [this, mul_zero])]
    ring
  rw [DensitySource.Ttilde, hP, hv, hc]
  ring

end Effectivity
end Erdos287
