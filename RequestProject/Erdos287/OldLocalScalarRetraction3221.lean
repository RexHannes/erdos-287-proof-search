import Mathlib

/-!
# V23, §1 — retraction of the old pointwise local-scalar dictionary

`BALANCED7-OLD-POINTWISE-LOCAL-SCALAR45 : RETRACTED / WRONG GEOMETRY`

## What the old dictionary said

An earlier reading of the Balanced7 comparison attached to each modulus `q` the *pointwise*
local scalar

```
    2q / φ(q)
```

and used it as the local mass of the `q`-cell of the aggregate `μ/φ`-sum.

## Why it is the wrong geometry

The aggregate object that the comparison has to reproduce is

```
    J_P(z) = ∑_{q ≤ z, (q,2P)=1} μ(q)/φ(q) · log(z/q)  →  2B(P),
```

whose limit `2B(P)` depends only on the physical seven-prime datum `P`, **not** on the
modulus `q`.  A dictionary that assigns to the `q`-cell a scalar depending on `q` therefore
cannot be the local shape of that aggregate constant: this file proves the obstruction in
exact form.

* `oldPointwiseLocalScalar_three` : `2·3/φ(3) = 3`;
* `oldPointwiseLocalScalar_five`  : `2·5/φ(5) = 5/2`;
* `old_pointwise_local_scalar_not_constant` : `q ↦ 2q/φ(q)` is not constant;
* `oldPointwiseLocalScalarDictionary_refuted` : the historical dictionary statement — that
  the pointwise scalar equals the `q`-independent aggregate value `2B(P)` for every odd
  prime modulus — is **false**, for every value of `2B(P)` whatsoever.

## Firewall

This is a *repository-internal* algebraic refutation of the pointwise dictionary.  The
independent audit of the corrected (aggregate) geometry is a separate matter and is
recorded, per the audit verdict `CASE F — SOURCE-MISSING`, as still open; see
`RequestProject/Status/Erdos287V23Status.lean`.  No historical source file is deleted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace V23OldScalar

/-! ## §1.1  The historical scalar -/

/-- **The old pointwise local scalar** `2q/φ(q)` (historical; retracted). -/
noncomputable def oldPointwiseLocalScalar (q : ℕ) : ℝ :=
  2 * (q : ℝ) / (Nat.totient q : ℝ)

@[simp] theorem oldPointwiseLocalScalar_three : oldPointwiseLocalScalar 3 = 3 := by
  have h : Nat.totient 3 = 2 := by decide
  rw [oldPointwiseLocalScalar, h]
  norm_num

@[simp] theorem oldPointwiseLocalScalar_five : oldPointwiseLocalScalar 5 = 5 / 2 := by
  have h : Nat.totient 5 = 4 := by decide
  rw [oldPointwiseLocalScalar, h]
  norm_num

/-- **`old_pointwise_local_scalar_not_constant`.**  `LEAN_PROVED`.

The map `q ↦ 2q/φ(q)` is not constant: it takes the value `3` at `q = 3` and `5/2` at
`q = 5`. -/
theorem old_pointwise_local_scalar_not_constant :
    ¬ ∃ c : ℝ, ∀ q : ℕ, 3 ≤ q → oldPointwiseLocalScalar q = c := by
  rintro ⟨c, hc⟩
  have h3 := hc 3 (by norm_num)
  have h5 := hc 5 (by norm_num)
  rw [oldPointwiseLocalScalar_three] at h3
  rw [oldPointwiseLocalScalar_five] at h5
  rw [← h3] at h5
  norm_num at h5

/-! ## §1.2  The historical dictionary, and its refutation -/

/-- **`OldPointwiseLocalScalarDictionary`** — the *historical* claim, preserved verbatim as
a `Prop` so that its retraction is a theorem and not an edit.

It says: the aggregate limit constant `twoB` (a datum of the physical seven-prime family
`P` alone) is realised cell-by-cell as the pointwise scalar `2q/φ(q)`. -/
def OldPointwiseLocalScalarDictionary (twoB : ℝ) : Prop :=
  ∀ q : ℕ, 3 ≤ q → oldPointwiseLocalScalar q = twoB

/-- **`oldPointwiseLocalScalarDictionary_refuted`.**  `LEAN_PROVED`.

For **no** value of the aggregate constant does the old pointwise dictionary hold.  This is
the exact sense in which `2q/φ(q)` is the wrong geometry: the left side varies with `q`,
the right side does not. -/
theorem oldPointwiseLocalScalarDictionary_refuted (twoB : ℝ) :
    ¬ OldPointwiseLocalScalarDictionary twoB := by
  intro h
  exact old_pointwise_local_scalar_not_constant ⟨twoB, h⟩

/-- **`old_dictionary_has_no_inhabitant`.**  `LEAN_PROVED`.

Restated existentially: there is no aggregate constant for which the retracted dictionary
is inhabited. -/
theorem old_dictionary_has_no_inhabitant :
    ¬ ∃ twoB : ℝ, OldPointwiseLocalScalarDictionary twoB := by
  rintro ⟨twoB, h⟩
  exact oldPointwiseLocalScalarDictionary_refuted twoB h

/-! ## §1.3  What survives

The *shape* `q/φ(q)` is still the correct local density of a sieve-type count in a single
progression — that use (in `ShortShiftSieve3221` and `ShiuDivisorAverage3221`) is untouched.
What is retracted is only its use as the local shape of the aggregate `μ/φ` comparison
constant.  The following records the distinction in a machine-checkable way: the surviving
use is a *bound* attached to one fixed modulus, and a fixed modulus does of course have a
well-defined scalar. -/
theorem oldScalar_fixed_modulus_is_fine (q : ℕ) (hq : 0 < Nat.totient q) :
    oldPointwiseLocalScalar q * (Nat.totient q : ℝ) = 2 * (q : ℝ) := by
  have h : (Nat.totient q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  rw [oldPointwiseLocalScalar, div_mul_cancel₀ _ h]

end V23OldScalar
end Erdos287
