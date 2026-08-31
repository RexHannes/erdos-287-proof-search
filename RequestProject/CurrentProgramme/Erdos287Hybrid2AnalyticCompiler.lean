import Mathlib
import RequestProject.CurrentProgramme.Erdos287Hybrid2Arithmetic
import RequestProject.Erdos287.Universal

/-!
# HYBRID-2 analytic compiler — explicit-hypothesis style

**Nothing in this file is unconditional analysis.**  The separated-frequency large sieve and
the Archimedean nuclear (packet) decomposition needed for Hybrid 2 are *not* theorems of this
repository, and none is fabricated here.  They enter as **explicit theorem hypotheses**
(`hArch`, `hPacket`, `hLS`), never as axioms.  Everything the compiler itself does is
elementary real algebra, and that part *is* kernel-checked.

Contents.

* §7  `fixedEll_bound` — the fixed-`ℓ` estimate, reproduced exactly from the three analytic
  inputs.
* §8  `ell_sum_harmonic`, `ell_sum_harmonic_two_min` — the deterministic harmonic `ℓ`-summation
  `B_ℓ ≤ C/ℓ  ⟹  ∑_ℓ B_ℓ ≤ C(1 + log …)`.  An *exact* harmonic bound is used
  (`harmonic_le_one_add_log`); no asymptotic `O(log)` statement occurs.

The names of the analytic hypotheses are the ones used in the audit, so that the report can
list them verbatim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace Erdos287
namespace Hybrid2

/-! ## §7  The fixed-`ℓ` bound -/

/-- **`fixedEll_bound`.**  `LEAN_PROVED` **conditionally** on `hArch`, `hPacket`, `hLS`.

Fix `ℓ` and abstract the three analytic quantities:

* `Pell`  — the packet `L²` mass `∑_u |c_ℓ(u)|²`;
* `Sell`  — the separated-frequency sum `∑_v |∑_u c_ℓ(u) e(θ_u v)|²`;
* `Bell`  — the fixed-`ℓ` contribution to the bilinear form.

The three hypotheses are exactly:

```
hArch    :  Bell ≤ Carch * sqrt Sell
            (Archimedean reciprocal factor admits a separated packet expansion with
             total coefficient mass ≤ Carch, followed by Cauchy–Schwarz);

hPacket  :  Pell ≤ L1^2 / (ℓ * M1);

hLS      :  Sell ≤ (D/ℓ + Q) * (1 + M1/(ℓ*Q)) * Pell
            (separated reciprocal frequencies with spacing 1/Q).
```

Conclusion — the fixed-`ℓ` estimate, verbatim:

```
Bell ≤ Carch * sqrt ( (D/ℓ + Q) (1 + M1/(ℓQ)) L1²/(ℓ M1) ).
```

This theorem is **not** unconditional. -/
theorem fixedEll_bound {ell D Q M1 L1 Carch Pell Sell Bell : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hQ : 0 < Q) (hM1 : 0 < M1) (hCarch : 0 ≤ Carch)
    (hArch : Bell ≤ Carch * Real.sqrt Sell)
    (hPacket : Pell ≤ L1 ^ 2 / (ell * M1))
    (hLS : Sell ≤ (D / ell + Q) * (1 + M1 / (ell * Q)) * Pell) :
    Bell ≤ Carch * Real.sqrt ((D / ell + Q) * (1 + M1 / (ell * Q)) * (L1 ^ 2 / (ell * M1))) := by
  have hfac : (0 : ℝ) ≤ (D / ell + Q) * (1 + M1 / (ell * Q)) := by positivity
  have hstep : Sell ≤ (D / ell + Q) * (1 + M1 / (ell * Q)) * (L1 ^ 2 / (ell * M1)) :=
    hLS.trans (mul_le_mul_of_nonneg_left hPacket hfac)
  exact hArch.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstep) hCarch)

/-! ## §8  The harmonic `ℓ`-sum compiler -/

/-- `∑_{1 ≤ k ≤ n} 1/k ≤ 1 + log n`, in the `Finset.Icc` form used by the bank.
This is Mathlib's exact harmonic bound, not an asymptotic statement. -/
theorem sum_inv_Icc_le_one_add_log (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log (n : ℝ) := by
  have h := harmonic_le_one_add_log n
  have hcast : ((harmonic n : ℚ) : ℝ) = ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) := by
    rw [Erdos287.harmonic_eq_sum_Icc]
    push_cast
    exact Finset.sum_congr rfl fun k _ => by rw [one_div]
  rw [hcast] at h
  exact h

/-- **`ell_sum_harmonic`.**  `LEAN_PROVED` (unconditional, deterministic).

From the fixed-`ℓ` bounds `B_ℓ ≤ C/ℓ` valid for `1 ≤ ℓ ≤ n`,

```
∑_{ℓ = 1}^{n} B_ℓ ≤ C (1 + log n).
```

The floor / `Nat` coercion is explicit: the range is the natural-number interval
`Finset.Icc 1 n` and `log n` is the real logarithm of the cast. -/
theorem ell_sum_harmonic {n : ℕ} {C : ℝ} (hC : 0 ≤ C) (B : ℕ → ℝ)
    (hB : ∀ ell ∈ Finset.Icc 1 n, B ell ≤ C / (ell : ℝ)) :
    ∑ ell ∈ Finset.Icc 1 n, B ell ≤ C * (1 + Real.log (n : ℝ)) := by
  have h1 : ∑ ell ∈ Finset.Icc 1 n, B ell ≤ ∑ ell ∈ Finset.Icc 1 n, C / (ell : ℝ) :=
    Finset.sum_le_sum hB
  have h2 : ∑ ell ∈ Finset.Icc 1 n, C / (ell : ℝ)
      = C * ∑ ell ∈ Finset.Icc 1 n, (1 : ℝ) / (ell : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_one_div]
  have h3 : C * ∑ ell ∈ Finset.Icc 1 n, (1 : ℝ) / (ell : ℝ) ≤ C * (1 + Real.log (n : ℝ)) :=
    mul_le_mul_of_nonneg_left (sum_inv_Icc_le_one_add_log n) hC
  calc ∑ ell ∈ Finset.Icc 1 n, B ell ≤ ∑ ell ∈ Finset.Icc 1 n, C / (ell : ℝ) := h1
    _ = C * ∑ ell ∈ Finset.Icc 1 n, (1 : ℝ) / (ell : ℝ) := h2
    _ ≤ C * (1 + Real.log (n : ℝ)) := h3

/-- **`ell_sum_harmonic_two_min`.**  `LEAN_PROVED` (unconditional).

The form in which the compiler is used: the `ℓ`-range is `1 ≤ ℓ ≤ min(D, M1)` and the bound is
stated with the `2·min(D,M1)` argument of the source,

```
∑_{ℓ ≤ min(D,M1)} B_ℓ ≤ C (1 + log (2 min(D,M1))).
```

`D` and `M1` are natural numbers here (already floored); the coercions are explicit. -/
theorem ell_sum_harmonic_two_min {D M1 : ℕ} {C : ℝ} (hC : 0 ≤ C) (B : ℕ → ℝ)
    (hB : ∀ ell ∈ Finset.Icc 1 (min D M1), B ell ≤ C / (ell : ℝ)) :
    ∑ ell ∈ Finset.Icc 1 (min D M1), B ell
      ≤ C * (1 + Real.log (((2 * min D M1 : ℕ) : ℝ))) := by
  set n : ℕ := min D M1 with hn
  have hbase := ell_sum_harmonic hC B hB
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0] at hbase ⊢
    simpa using hbase
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
    have hlog : Real.log (n : ℝ) ≤ Real.log (2 * (n : ℝ)) :=
      Real.log_le_log hn0 (by linarith)
    have : C * (1 + Real.log (n : ℝ)) ≤ C * (1 + Real.log (2 * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left (by linarith) hC
    have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
    calc ∑ ell ∈ Finset.Icc 1 n, B ell ≤ C * (1 + Real.log (n : ℝ)) := hbase
      _ ≤ C * (1 + Real.log (2 * (n : ℝ))) := this
      _ = C * (1 + Real.log ((2 * n : ℕ) : ℝ)) := by rw [hcast]

end Hybrid2
end Erdos287
