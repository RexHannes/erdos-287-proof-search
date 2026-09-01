import RequestProject.CurrentProgramme.Erdos287RegularPerronParent

/-!
# Template reassembly of the regular Perron parent

`TEMPLATE REASSEMBLY : KERNEL-PROVED (finite identity)`

This module is **append-only**.

A **template family** is a finite index set `Π` of *`X`-independent* cardinality
together with coefficients `F_{z,π}` whose pointwise sum is the regular parent:

```
∑_{π ∈ Π} F_{z,π}(n) = F_z^{reg}(n).
```

`template_correlation_reassembly` upgrades this to the finite correlation level,
**for every finite row set simultaneously** — in particular at every scale `X`,
with the same index family.  This is the identity that must be used *before* any
triangle inequality.

**Firewall.**  `abs_sum_lt_sum_abs_counterexample` records the concrete failure
of replacing `|∑_π C_{s,π}|` by `∑_π |C_{s,π}|`: two templates with values
`+1` and `−1` have `|∑| = 0 < 2 = ∑|·|`.  `Cfrag = 0` is banked purely as
finite, `X`-independent metadata.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace TemplateReassembly

/-! ## §1.  The finite, `X`-independent template family -/

/-- **`TemplateFamily`** — a finite template index `Π = Fin card` (no dependence on the
scale `X`) together with the pointwise reassembly identity onto the regular parent. -/
structure TemplateFamily where
  /-- The `X`-independent number of templates. -/
  card : ℕ
  /-- The template coefficients. -/
  Fpi : Fin card → ℕ → ℂ → ℂ
  /-- The regular parent coefficient. -/
  Freg : ℕ → ℂ → ℂ
  /-- **The pointwise reassembly identity.** -/
  reassembly : ∀ n z, ∑ pi : Fin card, Fpi pi n z = Freg n z

namespace TemplateFamily

variable (T : TemplateFamily)

/-- The finite correlation carried by one template. -/
noncomputable def templateCorrelation (pi : Fin T.card) (S : Finset ℕ) (w : ℕ → ℂ)
    (z : ℂ) : ℂ :=
  ∑ n ∈ S, w n * T.Fpi pi n z

/-- The finite correlation carried by the regular parent. -/
noncomputable def parentCorrelation (S : Finset ℕ) (w : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ n ∈ S, w n * T.Freg n z

/-- **`template_correlation_reassembly`.**  `KERNEL-PROVED`.

`∑_{π ∈ Π} C_{s,π} = C_s^{reg}` — the exact finite reassembly identity, valid for every
finite row set (hence at every scale, with the same `X`-independent index family). -/
theorem template_correlation_reassembly (S : Finset ℕ) (w : ℕ → ℂ) (z : ℂ) :
    ∑ pi : Fin T.card, T.templateCorrelation pi S w z = T.parentCorrelation S w z := by
  unfold templateCorrelation parentCorrelation
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.mul_sum, T.reassembly n z]

/-- The same identity for the two-sign source: summing the sign as well. -/
theorem template_correlation_reassembly_two_sign (S : Finset ℕ) (w : Bool → ℕ → ℂ)
    (z : ℂ) :
    ∑ s : Bool, ∑ pi : Fin T.card, T.templateCorrelation pi S (w s) z
      = ∑ s : Bool, T.parentCorrelation S (w s) z :=
  Finset.sum_congr rfl fun s _ => T.template_correlation_reassembly S (w s) z

end TemplateFamily

/-! ## §2.  The triangle-inequality firewall -/

/-- **`abs_sum_lt_sum_abs_counterexample`.**  `KERNEL-PROVED`.

`∑_π ‖C_{s,π}‖` must **not** replace `‖∑_π C_{s,π}‖`: an explicit two-template family
has `‖∑‖ = 0` while `∑ ‖·‖ = 2`.  The parent identity must be applied first. -/
theorem abs_sum_lt_sum_abs_counterexample :
    ∃ C : Fin 2 → ℂ, ‖∑ i, C i‖ < ∑ i, ‖C i‖ := by
  refine ⟨![1, -1], ?_⟩
  norm_num [Fin.sum_univ_two]

/-- **`triangle_only_after_parent`.**  `KERNEL-PROVED`.

The only inequality the reassembly supports: after the parent identity, the parent
correlation is bounded by the sum of the template moduli — never the other way round. -/
theorem triangle_only_after_parent (T : TemplateFamily) (S : Finset ℕ) (w : ℕ → ℂ)
    (z : ℂ) :
    ‖T.parentCorrelation S w z‖ ≤ ∑ pi : Fin T.card, ‖T.templateCorrelation pi S w z‖ := by
  rw [← T.template_correlation_reassembly S w z]
  exact norm_sum_le _ _

/-! ## §3.  `C_frag` as finite metadata -/

/-- **`Cfrag`** — banked as finite, `X`-independent **metadata** only.

It is a numeral in this repository.  It is *not* an asymptotic theorem, and no analytic
statement is derived from it. -/
def Cfrag : ℚ := 0

@[simp] theorem Cfrag_eq_zero : Cfrag = 0 := rfl

end TemplateReassembly
end Erdos287
