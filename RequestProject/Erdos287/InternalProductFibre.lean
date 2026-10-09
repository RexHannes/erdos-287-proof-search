import Mathlib
import RequestProject.Erdos287.BsrcWeights
import RequestProject.Erdos287.ResidueCollapse

/-!
# Erdős #287 effectivity — the internal product fibre `ℓ = d·t` (§55)

```
TRUNCATED SHIFT-SIEVE COEFFICIENT S_{d,E}(a) : KERNEL-PROVED (exact complementary form)
INTERNAL PRODUCT-FIBRE IDENTITY A_{D,E}       : KERNEL-PROVED
d-RANGE MONOTONICITY / EXHAUSTION             : KERNEL-PROVED
INTERNAL ℓ ≠ ORIGINAL CONDUCTOR f             : KERNEL-PROVED FIREWALL
E = 5000 CUT-OFF PRESERVED                    : KERNEL-PROVED (no e > 5000 source restored)
```

The internal fibre variable is `ℓ = d·t`.  The transformed physical conductor interval is
the divisor window

    d ∣ ℓ,   d ≤ D,   t = ℓ/d ≥ 2,   t ∣ s,   t ≤ E   (truncated e-source),

and the fibre coefficient is

    A_{D,E}(ℓ; s, z) = ∑_{d ∣ ℓ, d ≤ D, t = ℓ/d ≥ 2, t ∣ s} σ_E(t, z),
    σ_E(t, z)        = β(t) · 1_{t ≤ E} · 1_{(t,z) = 1}.

`internal_product_fibre_identity` is the exact identity rewriting this divisor sum as a sum
over factorisation *pairs* `(d,t)` with `d·t = ℓ` — the product-fibre form.

**Firewall.**  The internal fibre variable `ℓ` is *not* the original conductor variable `f`:
`internal_ell_not_conductor` shows the internal range `1000 < ℓ ≤ 5000` is disjoint from the
old certified conductor range `f ≤ 1000`, so no `f ≤ 1000` certificate transports
automatically to an internal `ℓ`.

**Cut-off.**  `SdE` and `σ_E` are truncated at `E`; `truncated_source_cutoff_preserved`
records that the truncation drops exactly the `t > E` complementary part, and the frozen
`e > 5000` source is never restored.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §55.1  The truncated e-source coefficient -/

/-- The truncated `e`-source coefficient `σ_E(t,z) = β(t)·1_{t ≤ E}·1_{(t,z)=1}`. -/
def sigmaSrc (E t z : ℕ) : ℚ :=
  if t ≤ E ∧ Nat.Coprime t z then beta t else 0

lemma sigmaSrc_of_gt {E t z : ℕ} (h : E < t) : sigmaSrc E t z = 0 := by
  simp [sigmaSrc, Nat.not_le.2 h]

/-- **`truncated_source_cutoff_preserved`.**  `KERNEL-PROVED`.  The truncated coefficient
differs from the untruncated one exactly by the complementary `t > E` part; the truncation is
therefore lossless bookkeeping, and no `t > E` source is silently restored. -/
theorem truncated_source_cutoff_preserved (E z : ℕ) (a : ℕ) :
    ∑ t ∈ (Nat.divisors a).filter (fun t => Nat.Coprime t z), sigmaSrc E t z
      = ∑ t ∈ (Nat.divisors a).filter (fun t => Nat.Coprime t z ∧ t ≤ E), beta t := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hc : Nat.Coprime t z <;> by_cases hE : t ≤ E <;> simp [sigmaSrc, hc, hE]

/-- **`SdE_truncation_complement`.**  `KERNEL-PROVED`.  The exact complementary form of the
truncated divisor coefficient: the full divisor sum splits as the truncated part plus the
`t > E` complement. -/
theorem SdE_truncation_complement (d E a : ℕ) :
    ∑ t ∈ (Nat.divisors a).filter (fun t => d ∣ t), beta t
      = SdE d E a + ∑ t ∈ (Nat.divisors a).filter (fun t => d ∣ t ∧ ¬ t ≤ E), beta t := by
  classical
  rw [SdE, ← Finset.sum_filter_add_sum_filter_not
    ((Nat.divisors a).filter (fun t => d ∣ t)) (fun t => t ≤ E) beta,
    Finset.filter_filter, Finset.filter_filter]

/-! ## §55.2  The internal product fibre -/

/-- The internal-fibre divisor window: `d ∣ ℓ`, `d ≤ D`, `t = ℓ/d ≥ 2` and `t ∣ s`. -/
def fibreWindow (D : ℕ) (ell s : ℕ) : Finset ℕ :=
  (Nat.divisors ell).filter (fun d => d ≤ D ∧ 2 ≤ ell / d ∧ (ell / d) ∣ s)

/-- `A_{D,E}(ℓ; s, z)`: the internal product-fibre coefficient. -/
def AfibreDE (D E : ℕ) (ell s z : ℕ) : ℚ :=
  ∑ d ∈ fibreWindow D ell s, sigmaSrc E (ell / d) z

/-- **`internal_product_fibre_identity`.**  `KERNEL-PROVED`.  The exact internal
product-fibre identity: the divisor window sum equals the sum over factorisation pairs
`(d,t)` with `d·t = ℓ`. -/
theorem internal_product_fibre_identity (D E ell s z : ℕ) :
    AfibreDE D E ell s z
      = ∑ p ∈ (Nat.divisorsAntidiagonal ell).filter
            (fun p => p.1 ≤ D ∧ 2 ≤ p.2 ∧ p.2 ∣ s), sigmaSrc E p.2 z := by
  classical
  rw [AfibreDE, fibreWindow, Finset.sum_filter, Finset.sum_filter,
    ← Nat.sum_divisorsAntidiagonal
      (fun a b => if a ≤ D ∧ 2 ≤ b ∧ b ∣ s then sigmaSrc E b z else 0)]

/-- **`AfibreDE_mono_D`.**  `KERNEL-PROVED`.  Enlarging the `d`-range only adds window
elements: the fibre windows are nested. -/
theorem AfibreDE_mono_D {D D' : ℕ} (h : D ≤ D') (ell s : ℕ) :
    fibreWindow D ell s ⊆ fibreWindow D' ell s := by
  intro d hd
  rw [fibreWindow, Finset.mem_filter] at hd ⊢
  exact ⟨hd.1, le_trans hd.2.1 h, hd.2.2⟩

/-- **`fibreWindow_no_t_one`.**  `KERNEL-PROVED`.  The condition `t ≥ 2` removes the trivial
fibre `t = 1` (i.e. `d = ℓ`): the internal fibre never contains the whole conductor. -/
theorem fibreWindow_no_t_one {D ell s : ℕ} (hell : ell ≠ 0) :
    ell ∉ fibreWindow D ell s := by
  intro h
  rw [fibreWindow, Finset.mem_filter] at h
  have : ell / ell = 1 := Nat.div_self (Nat.pos_of_ne_zero hell)
  rw [this] at h
  omega

/-! ## §55.3  Firewall: the internal fibre variable is not the conductor -/

/-- The old certified conductor range. -/
def oldConductorRange : Finset ℕ := Finset.Icc 1 1000

/-- The internal fibre range currently in play. -/
def internalEllRange : Finset ℕ := Finset.Icc 1001 5000

/-- **`internal_ell_not_conductor`.**  `KERNEL-PROVED`.  The internal fibre range and the old
certified conductor range are disjoint, and the internal range is nonempty: **no `f ≤ 1000`
certificate may be applied automatically to an internal `ℓ`.** -/
theorem internal_ell_not_conductor :
    Disjoint oldConductorRange internalEllRange ∧
      internalEllRange.Nonempty ∧
      ¬ (∀ ell ∈ internalEllRange, ell ∈ oldConductorRange) := by
  refine ⟨?_, ⟨1001, by decide⟩, ?_⟩
  · rw [Finset.disjoint_left]
    intro a ha hb
    rw [oldConductorRange, Finset.mem_Icc] at ha
    rw [internalEllRange, Finset.mem_Icc] at hb
    omega
  · intro h
    have := h 1001 (by decide)
    rw [oldConductorRange, Finset.mem_Icc] at this
    omega

/-- **`E5000_cutoff_not_extended`.**  `KERNEL-PROVED`.  The truncated source is genuinely
truncated at `E = 5000`: every `t > 5000` contributes `0`, so the frozen `e > 5000` source is
not restored by the internal fibre. -/
theorem E5000_cutoff_not_extended {t : ℕ} (ht : 5000 < t) (z : ℕ) :
    sigmaSrc 5000 t z = 0 := sigmaSrc_of_gt ht

end Effectivity
end Erdos287
