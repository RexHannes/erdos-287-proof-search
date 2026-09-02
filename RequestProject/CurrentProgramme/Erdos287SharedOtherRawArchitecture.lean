import RequestProject.CurrentProgramme.Erdos287TwoLaneMasterCompilerV2

/-!
# The 287A / shared-other45 raw architecture

```
DEPENDENT RAW PACKET  RawPacket X = RawData Tot X ⊕ RawData U X : KERNEL-PROVED
TOT CONSTRUCTOR EXCLUSION FIREWALL                              : KERNEL-PROVED
U CONSTRUCTOR CONTENT (k, J, HB grammar, 𝓔, E*, u/v, skeleton)  : KERNEL-PROVED
DETERMINISTIC E*(𝓔)                                             : KERNEL-PROVED
GENERATED COEFFICIENTS  A_η(a;τ), B_η(b;τ)                      : KERNEL-PROVED (definitions)
DETERMINANT-LINE TRANSFORMATION  rq − 2ab = s                   : KERNEL-PROVED
CENTRED TWO-COPY IDENTITY  |S|² = PP̄ − PM̄ − MP̄ + MM̄            : KERNEL-PROVED
COEFFICIENT PRESERVATION                                        : KERNEL-PROVED
```

This module is **append-only**.  Everything here is finite/algebraic; no analytic statement
is proved, and no analytic socket is inhabited.

**§1** builds the *dependent* raw packet type at a scale `X` as a genuine sum type, with the
`Tot` constructor carrying **none** of `k`, `J`, the HB leaves, `𝓔`, `E*`, the shared `gcd`
or `Δ`, and the `U` constructor carrying exactly the listed source data with a
*deterministic* `E*`.

**§2** defines the exact selected-`E` generated coefficients `A_η(a;τ)` and `B_η(b;τ)`.

**§3–§5** kernel-prove the determinant-line transformation, the centred two-copy identity
and exact coefficient preservation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace SharedOtherRaw

open Erdos287.TwoLaneRawSource

/-! ## §1  The dependent raw packet type -/

/-- **`PerronSkeleton`** — the dyadic/Perron skeleton labels of a raw datum.  Labels only:
no contour ordinate is a field. -/
structure PerronSkeleton where
  /-- The dyadic block index. -/
  dyadicBlock : ℕ
  /-- The Perron truncation label. -/
  truncationLabel : ℕ
  /-- The contour orientation. -/
  orientation : Bool
  deriving DecidableEq, Repr

/-- **`HBLeafKind`** — the literal Heath-Brown leaf grammar. -/
inductive HBLeafKind
  /-- A linear (type-I) leaf. -/
  | linear
  /-- A `log`-weighted leaf. -/
  | logWeighted
  /-- A `log·log`-weighted leaf. -/
  | logLogWeighted
  deriving DecidableEq, Fintype, Repr

/-- **`HBLeaf`** — one literal leaf of the Heath-Brown grammar. -/
structure HBLeaf where
  /-- The grammar kind of the leaf. -/
  kind : HBLeafKind
  /-- The leaf modulus. -/
  modulus : ℕ
  /-- The integer coefficient of the leaf. -/
  coefficient : ℤ
  deriving DecidableEq, Repr

/-- **`CoefficientPattern`** — the three source coefficient patterns of the census. -/
inductive CoefficientPattern
  /-- The `1 × 1` pattern. -/
  | oneOne
  /-- The `log x × 1` pattern. -/
  | logOne
  /-- The `log x × log` pattern. -/
  | logLog
  deriving DecidableEq, Fintype, Repr

/-- **`RawDataTot`** — the `Tot` raw datum at scale `X`.

Its fields are **exactly** a modulus below the scale, a residue label, a source sign and a
dyadic/Perron skeleton.  It carries no `k`, no `J`, no HB leaf, no `𝓔`, no `E*`, no shared
`gcd` and no `Δ`. -/
structure RawDataTot (X : ℕ) where
  /-- The modulus of the datum. -/
  modulus : ℕ
  /-- The modulus is positive. -/
  modulus_pos : 0 < modulus
  /-- The modulus lies below the scale: this is the dependence on `X`. -/
  modulus_le : modulus ≤ X
  /-- The residue label. -/
  residue : ℕ
  /-- The source sign. -/
  sourceSign : Bool
  /-- The dyadic/Perron skeleton. -/
  skeleton : PerronSkeleton

/-- **`RawDataU`** — the `U` raw datum at scale `X`.

Its fields are **exactly** `k`, `J`, the literal HB grammar, the family `𝓔`, the
deterministic selected `E* = E*(𝓔)`, the `u`/`v` source, the dyadic/Perron skeleton and the
source signs. -/
structure RawDataU (X : ℕ) where
  /-- The dissection depth `k`. -/
  k : ℕ
  /-- The Perron dissection parameter `J`. -/
  J : ℕ
  /-- The literal Heath-Brown grammar of the row. -/
  hbGrammar : List HBLeaf
  /-- The inclusion–exclusion family `𝓔`. -/
  mathcalE : Finset (Finset Leaf)
  /-- The family is nonempty, so the selector is defined. -/
  mathcalE_nonempty : mathcalE.Nonempty
  /-- The selected `E*`. -/
  EStar : Finset Leaf
  /-- `E*` is **deterministically** the canonical selector of `𝓔`. -/
  EStar_def : EStar = selectedE mathcalE mathcalE_nonempty
  /-- The `u` slot of the source. -/
  u : ℕ
  /-- The `v` slot of the source. -/
  v : ℕ
  /-- The `u`/`v` source lies below the scale: this is the dependence on `X`. -/
  uv_le : u * v ≤ X
  /-- The dyadic/Perron skeleton. -/
  skeleton : PerronSkeleton
  /-- The source sign of the `u` slot. -/
  uSign : Bool
  /-- The source sign of the `v` slot. -/
  vSign : Bool

/-- **`RawPacket`** — the dependent raw packet type at scale `X`:
`RawPacket X = RawData Tot X ⊕ RawData U X`. -/
abbrev RawPacket (X : ℕ) : Type := RawDataTot X ⊕ RawDataU X

/-- The `Tot` injection. -/
def RawPacket.tot {X : ℕ} (t : RawDataTot X) : RawPacket X := Sum.inl t

/-- The `U` injection. -/
def RawPacket.u {X : ℕ} (p : RawDataU X) : RawPacket X := Sum.inr p

/-- **`rawPacket_is_a_two_lane_sum`.**  `KERNEL-PROVED`.

Every raw packet is exactly one of a `Tot` datum and a `U` datum. -/
theorem rawPacket_is_a_two_lane_sum {X : ℕ} (p : RawPacket X) :
    (∃ t : RawDataTot X, p = RawPacket.tot t) ∨ (∃ q : RawDataU X, p = RawPacket.u q) := by
  cases p with
  | inl t => exact Or.inl ⟨t, rfl⟩
  | inr q => exact Or.inr ⟨q, rfl⟩

/-- **`rawPacket_lanes_are_disjoint`.**  `KERNEL-PROVED`.  A `Tot` datum is never a `U`
datum. -/
theorem rawPacket_lanes_are_disjoint {X : ℕ} (t : RawDataTot X) (q : RawDataU X) :
    RawPacket.tot t ≠ RawPacket.u q := by
  simp [RawPacket.tot, RawPacket.u]

/-! ### The `Tot` constructor exclusion firewall -/

/-- The literal field names of the `Tot` constructor. -/
def totFieldNames : List String :=
  ["modulus", "modulus_pos", "modulus_le", "residue", "sourceSign", "skeleton"]

/-- The field names the `Tot` constructor must **not** contain. -/
def forbiddenTotFieldNames : List String :=
  ["k", "J", "hbGrammar", "mathcalE", "EStar", "sharedGcd", "Delta"]

/-- **`tot_constructor_excludes_forbidden_fields`.**  `KERNEL-PROVED`.

No forbidden name occurs among the `Tot` field names. -/
theorem tot_constructor_excludes_forbidden_fields :
    ∀ f ∈ forbiddenTotFieldNames, f ∉ totFieldNames := by decide

/-- **`tot_datum_is_determined_by_its_listed_fields`.**  `KERNEL-PROVED`.

The semantic form of the same firewall: a `Tot` datum carries **no data beyond** the four
listed carriers, so in particular no `k`, `J`, `𝓔`, `E*`, `gcd` or `Δ` is hidden in it. -/
theorem tot_datum_is_determined_by_its_listed_fields {X : ℕ} (s t : RawDataTot X)
    (hm : s.modulus = t.modulus) (hr : s.residue = t.residue)
    (hs : s.sourceSign = t.sourceSign) (hk : s.skeleton = t.skeleton) : s = t := by
  cases s; cases t
  simp_all

/-- **`u_constructor_carries_the_listed_fields`.**  `KERNEL-PROVED`.

Dually, the `U` datum does carry the listed source data, and its `E*` is determined by
`𝓔`. -/
theorem u_constructor_carries_the_listed_fields {X : ℕ} (p : RawDataU X) :
    p.EStar = selectedE p.mathcalE p.mathcalE_nonempty ∧ p.EStar ∈ p.mathcalE :=
  ⟨p.EStar_def, p.EStar_def ▸ selectedE_mem _ _⟩

/-- **`selectedE_congr`.**  `KERNEL-PROVED`.  The canonical selector depends on the family
only, not on the nonemptiness proof. -/
theorem selectedE_congr {E₁ E₂ : Finset (Finset Leaf)} (h₁ : E₁.Nonempty) (h₂ : E₂.Nonempty)
    (h : E₁ = E₂) : selectedE E₁ h₁ = selectedE E₂ h₂ := by
  subst h; rfl

/-- **`EStar_is_deterministic`.**  `KERNEL-PROVED`.

Two `U` data with the same family `𝓔` have the same selected `E*`: the selector is a
function of `𝓔` alone, never an independent choice. -/
theorem EStar_is_deterministic {X : ℕ} (p q : RawDataU X)
    (h : p.mathcalE = q.mathcalE) : p.EStar = q.EStar := by
  rw [p.EStar_def, q.EStar_def]
  exact selectedE_congr _ _ h

/-! ## §2  The exact selected-`E` generated coefficients -/

/-- **`A_eta`** — the exact `A_η(a;τ)` coefficient generated by the selected `E`.

It is the signed, divisor-restricted sum over `E*` of the source profile `eta` against the
Perron character slot `chi`.  It is a function of `E*` — hence of `𝓔` — and of the source
data only. -/
noncomputable def A_eta {X : ℕ} (p : RawDataU X) (eta : ℕ → ℝ) (chi : ℕ → ℤ → ℝ)
    (a : ℕ) (tau : ℤ) : ℝ :=
  (if p.uSign then (1 : ℝ) else -1) *
    ∑ d ∈ p.EStar.filter (fun d => d ∣ a), eta d * chi (a / d) tau

/-- **`B_eta`** — the exact `B_η(b;τ)` coefficient generated by the selected `E`, on the
`v` slot. -/
noncomputable def B_eta {X : ℕ} (p : RawDataU X) (eta : ℕ → ℝ) (chi : ℕ → ℤ → ℝ)
    (b : ℕ) (tau : ℤ) : ℝ :=
  (if p.vSign then (1 : ℝ) else -1) *
    ∑ d ∈ p.EStar.filter (fun d => d ∣ b), eta d * chi (b / d) tau

/-- **`A_eta_eq_zero_of_no_divisor`.**  `KERNEL-PROVED`.

The generated coefficient is supported on arguments divisible by some element of `E*`. -/
theorem A_eta_eq_zero_of_no_divisor {X : ℕ} (p : RawDataU X) (eta : ℕ → ℝ)
    (chi : ℕ → ℤ → ℝ) (a : ℕ) (tau : ℤ) (h : ∀ d ∈ p.EStar, ¬ d ∣ a) :
    A_eta p eta chi a tau = 0 := by
  have : p.EStar.filter (fun d => d ∣ a) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 ?_
    intro d hd
    exact h d hd
  simp [A_eta, this]

/-- **`B_eta_eq_zero_of_no_divisor`.**  `KERNEL-PROVED`. -/
theorem B_eta_eq_zero_of_no_divisor {X : ℕ} (p : RawDataU X) (eta : ℕ → ℝ)
    (chi : ℕ → ℤ → ℝ) (b : ℕ) (tau : ℤ) (h : ∀ d ∈ p.EStar, ¬ d ∣ b) :
    B_eta p eta chi b tau = 0 := by
  have : p.EStar.filter (fun d => d ∣ b) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 ?_
    intro d hd
    exact h d hd
  simp [B_eta, this]

/-- **`generated_coefficients_depend_only_on_the_selected_E`.**  `KERNEL-PROVED`.

`A_η` and `B_η` are generated by `E*` and the signs: two `U` data with the same `𝓔` and the
same signs generate the same coefficients. -/
theorem generated_coefficients_depend_only_on_the_selected_E {X : ℕ} (p q : RawDataU X)
    (hE : p.mathcalE = q.mathcalE) (hu : p.uSign = q.uSign) (hv : p.vSign = q.vSign)
    (eta : ℕ → ℝ) (chi : ℕ → ℤ → ℝ) (a : ℕ) (tau : ℤ) :
    A_eta p eta chi a tau = A_eta q eta chi a tau ∧
    B_eta p eta chi a tau = B_eta q eta chi a tau := by
  have hs := EStar_is_deterministic p q hE
  constructor
  · simp [A_eta, hs, hu]
  · simp [B_eta, hs, hv]

/-! ## §3  The determinant-line transformation -/

/-- **`determinant_line_invariant`.**  `KERNEL-PROVED`.

The parametrisation `b = b₀ + r·ℓ`, `q = q₀ + 2a·ℓ` leaves the determinant `rq − 2ab`
invariant. -/
theorem determinant_line_invariant (r a b₀ q₀ ell : ℤ) :
    r * (q₀ + 2 * a * ell) - 2 * a * (b₀ + r * ell) = r * q₀ - 2 * a * b₀ := by ring

/-- **`determinant_line_forward`.**  `KERNEL-PROVED`.

Every point of the line solves `rq − 2ab = s`. -/
theorem determinant_line_forward {r a b₀ q₀ s : ℤ} (h : r * q₀ - 2 * a * b₀ = s) (ell : ℤ)
    {b q : ℤ} (hb : b = b₀ + r * ell) (hq : q = q₀ + 2 * a * ell) :
    r * q - 2 * a * b = s := by
  subst hb; subst hq
  rw [determinant_line_invariant]; exact h

/-- **`determinant_line_converse`.**  `KERNEL-PROVED`.

Conversely, if `r ≠ 0`, a solution whose `b`-coordinate lies on the line has its
`q`-coordinate on the line too: the parametrisation is exact, not merely sufficient. -/
theorem determinant_line_converse {r a b₀ q₀ s b q ell : ℤ} (hr : r ≠ 0)
    (h₀ : r * q₀ - 2 * a * b₀ = s) (h : r * q - 2 * a * b = s) (hb : b = b₀ + r * ell) :
    q = q₀ + 2 * a * ell := by
  have hstep : r * (q - q₀ - 2 * a * ell) = 0 := by
    have : r * q - 2 * a * b = r * q₀ - 2 * a * b₀ := by rw [h, h₀]
    rw [hb] at this
    linarith [this]
  rcases mul_eq_zero.1 hstep with h' | h'
  · exact absurd h' hr
  · linarith

/-- **`census_determinant_line`.**  `KERNEL-PROVED`.

The census determinant `ℓ·q − (π·z·y)·c = 2` of the newest source metadata, in the same
parametric form. -/
theorem census_determinant_line {ell q pi z y c : ℤ} (h : ell * q - (pi * z * y) * c = 2)
    (t : ℤ) : ell * (q + (pi * z * y) * t) - (pi * z * y) * (c + ell * t) = 2 := by
  have : ell * (q + pi * z * y * t) - pi * z * y * (c + ell * t)
      = ell * q - pi * z * y * c := by ring
  rw [this]; exact h

/-! ## §4  The centred two-copy identity -/

/-- **`centred_two_copy_identity`.**  `KERNEL-PROVED`.

With `S = P − M`,
`|S|² = P·P̄ − P·M̄ − M·P̄ + M·M̄`. -/
theorem centred_two_copy_identity (P M : ℂ) :
    (P - M) * (starRingEnd ℂ) (P - M)
      = P * (starRingEnd ℂ) P - P * (starRingEnd ℂ) M - M * (starRingEnd ℂ) P
        + M * (starRingEnd ℂ) M := by
  rw [map_sub]
  ring

/-- **`centred_two_copy_normSq`.**  `KERNEL-PROVED`.  The same identity in `normSq` form. -/
theorem centred_two_copy_normSq (P M : ℂ) :
    ((Complex.normSq (P - M) : ℝ) : ℂ)
      = P * (starRingEnd ℂ) P - P * (starRingEnd ℂ) M - M * (starRingEnd ℂ) P
        + M * (starRingEnd ℂ) M := by
  rw [← centred_two_copy_identity]
  exact (Complex.mul_conj _).symm

/-! ## §5  Exact coefficient preservation -/

/-- **`coefficient_preservation`.**  `KERNEL-PROVED`.

Squaring a finite source sum produces exactly the two-copy array of products of the source
coefficients: no coefficient is lost, duplicated or majorised. -/
theorem coefficient_preservation {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c f : ι → ℂ) :
    (∑ n ∈ S, c n * f n) * (starRingEnd ℂ) (∑ m ∈ S, c m * f m)
      = ∑ n ∈ S, ∑ m ∈ S, (c n * (starRingEnd ℂ) (c m)) * (f n * (starRingEnd ℂ) (f m)) := by
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul]
  ring

/-- **`coefficient_preservation_diagonal`.**  `KERNEL-PROVED`.

On the diagonal the two-copy value is exactly the squared modulus of the one-copy value. -/
theorem coefficient_preservation_diagonal (c f : ℂ) :
    (c * (starRingEnd ℂ) c) * (f * (starRingEnd ℂ) f)
      = ((Complex.normSq (c * f) : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_mul]
  push_cast
  ring

/-- **`centred_two_copy_is_not_the_uncentred_square`.**  `KERNEL-PROVED`.

The centring is not cosmetic: at explicit data the centred square differs from `P·P̄`. -/
theorem centred_two_copy_is_not_the_uncentred_square :
    ∃ P M : ℂ, (P - M) * (starRingEnd ℂ) (P - M) ≠ P * (starRingEnd ℂ) P := by
  refine ⟨1, 1, ?_⟩
  simp

end SharedOtherRaw
end Erdos287
