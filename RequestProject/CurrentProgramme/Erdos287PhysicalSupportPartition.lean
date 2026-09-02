import Mathlib

/-!
# The physical support partition, the physical weights and the four error channels

```
SUPPORT PARTITION  I_X = P_X ⊎ N1_X ⊎ N2_X ⊎ U_X : KERNEL-PROVED
PHYSICAL WEIGHTS a_X, b_X, w_X, H_X              : TYPED (source pins explicit)
FOUR ERROR CHANNELS E_T, E_L, E_2, E_M, Bmass    : DEFINED over the literal classes
```

This module is **append-only**.

**§1 — the support partition.**  Each index of the finite audited range `I_X` carries
exactly one of the four literal support classes `P`, `N1`, `N2`, `U`.  The regions
`P_X, N1_X, N2_X, U_X` are the corresponding fibres, and the finite set identity

```
    I_X = P_X ⊎ N1_X ⊎ N2_X ⊎ U_X
```

is kernel-proved, together with pairwise disjointness, the cardinality identity and the
region-wise sum decomposition used by the transference algebra.

**§2 — the physical weights.**  The literal source data

```
    a_X(n) = W(n/X)·[Λ(2n−1) + Λ(2n+1)],
    b_X(n) = 4·W(n/X)·Bsrc(n),
    w_X    = a_X − b_X,
    H_X    = H_ε
```

are *typed*, with `W`, `Λ`, `Bsrc`, `H_ε` carried as explicit source fields.  `Bsrc` is
never replaced by an unrelated `B`: `bX_determines_Bsrc` shows the comparison weight pins
the source function wherever the window is nonzero.

**§3 — the four error channels.**  `E_T`, `E_L`, `E_2`, `E_M` and `Bmass` are defined by
the literal support classes only.  **No analytic theorem is attached to any of them.**
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace PhysicalSupport

/-! ## §1  The literal support classes and the partition -/

/-- **`SupportClass`** — the four literal support classes of the fixed certificate. -/
inductive SupportClass
  /-- The certificate-positive (prime) class `P`. -/
  | P
  /-- The first negative class `N1`. -/
  | N1
  /-- The second negative class `N2`. -/
  | N2
  /-- The uncontrolled / leakage class `U`. -/
  | U
  deriving DecidableEq, Fintype, Repr

/-- **`PhysicalSupportData`** — the audited finite index set `I_X` together with the
literal classification of each index. -/
structure PhysicalSupportData where
  /-- The audited finite index set `I_X`. -/
  I : Finset ℕ
  /-- The literal support class of each index. -/
  cls : ℕ → SupportClass

namespace PhysicalSupportData

variable (d : PhysicalSupportData)

/-- The fibre of a support class inside `I_X`. -/
def region (c : SupportClass) : Finset ℕ := d.I.filter (fun n => d.cls n = c)

/-- `P_X`. -/
def PX : Finset ℕ := d.region SupportClass.P

/-- `N1_X`. -/
def N1X : Finset ℕ := d.region SupportClass.N1

/-- `N2_X`. -/
def N2X : Finset ℕ := d.region SupportClass.N2

/-- `U_X`. -/
def UX : Finset ℕ := d.region SupportClass.U

/-- `N_X = N1_X ∪ N2_X`. -/
def NX : Finset ℕ := d.N1X ∪ d.N2X

@[simp] theorem mem_region {n : ℕ} {c : SupportClass} :
    n ∈ d.region c ↔ n ∈ d.I ∧ d.cls n = c := by
  simp [region]

/-- **`support_partition_union`.**  `KERNEL-PROVED`.  The four regions exhaust `I_X`. -/
theorem support_partition_union : d.PX ∪ d.N1X ∪ d.N2X ∪ d.UX = d.I := by
  ext n
  simp only [Finset.mem_union, PX, N1X, N2X, UX, mem_region]
  constructor
  · intro h
    rcases h with h | h
    · rcases h with h | h
      · rcases h with h | h
        · exact h.1
        · exact h.1
      · exact h.1
    · exact h.1
  · intro h
    cases hc : d.cls n <;> simp [h]

/-- **`regions_disjoint`.**  `KERNEL-PROVED`.  Distinct classes give disjoint regions. -/
theorem regions_disjoint {c c' : SupportClass} (h : c ≠ c') :
    Disjoint (d.region c) (d.region c') := by
  refine Finset.disjoint_left.2 ?_
  intro n hn hn'
  rw [mem_region] at hn hn'
  exact h (hn.2 ▸ hn'.2 ▸ rfl)

/-- **`support_partition_disjoint`.**  `KERNEL-PROVED`.  The six pairwise disjointness
statements of the literal four-class partition. -/
theorem support_partition_disjoint :
    Disjoint d.PX d.N1X ∧ Disjoint d.PX d.N2X ∧ Disjoint d.PX d.UX ∧
    Disjoint d.N1X d.N2X ∧ Disjoint d.N1X d.UX ∧ Disjoint d.N2X d.UX :=
  ⟨d.regions_disjoint (by decide), d.regions_disjoint (by decide),
    d.regions_disjoint (by decide), d.regions_disjoint (by decide),
    d.regions_disjoint (by decide), d.regions_disjoint (by decide)⟩

/-- **`support_partition_card`.**  `KERNEL-PROVED`.  The disjoint-union identity in
cardinality form. -/
theorem support_partition_card :
    d.PX.card + d.N1X.card + d.N2X.card + d.UX.card = d.I.card := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := d.support_partition_disjoint
  have hu : (d.PX ∪ d.N1X ∪ d.N2X ∪ d.UX).card = d.I.card := by
    rw [d.support_partition_union]
  rw [Finset.card_union_of_disjoint (by
        refine Finset.disjoint_union_left.2 ⟨?_, ?_⟩
        · exact Finset.disjoint_union_left.2 ⟨h3, h5⟩
        · exact h6),
      Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨h2, h4⟩),
      Finset.card_union_of_disjoint h1] at hu
  exact hu

/-- **`sum_partition`.**  `KERNEL-PROVED`.  The region-wise decomposition of any finite
sum over `I_X`.  This is the only fact the transference algebra consumes. -/
theorem sum_partition (f : ℕ → ℝ) :
    ∑ n ∈ d.I, f n =
      (∑ n ∈ d.PX, f n) + (∑ n ∈ d.N1X, f n) + (∑ n ∈ d.N2X, f n) + (∑ n ∈ d.UX, f n) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := d.support_partition_disjoint
  have hu := d.support_partition_union
  rw [← hu]
  rw [Finset.sum_union (by
        refine Finset.disjoint_union_left.2 ⟨?_, ?_⟩
        · exact Finset.disjoint_union_left.2 ⟨h3, h5⟩
        · exact h6),
      Finset.sum_union (Finset.disjoint_union_left.2 ⟨h2, h4⟩),
      Finset.sum_union h1]

/-- **`NX_partition`.**  `KERNEL-PROVED`.  The combined negative class splits exactly. -/
theorem NX_partition (f : ℕ → ℝ) :
    ∑ n ∈ d.NX, f n = (∑ n ∈ d.N1X, f n) + (∑ n ∈ d.N2X, f n) := by
  obtain ⟨-, -, -, h4, -, -⟩ := d.support_partition_disjoint
  exact Finset.sum_union h4

end PhysicalSupportData

/-! ## §2  The physical weights -/

/-- **`PhysicalWeightData`** — the literal physical source data of the fixed certificate:
the scale `X`, the smooth window `W`, the von Mangoldt weight `Λ`, the *source* comparison
function `Bsrc`, and the perturbed certificate kernel `H_ε`. -/
structure PhysicalWeightData where
  /-- The scale `X`. -/
  X : ℝ
  /-- The smooth window `W`. -/
  W : ℝ → ℝ
  /-- The von Mangoldt weight `Λ`. -/
  Lam : ℕ → ℝ
  /-- The **source** comparison function `Bsrc` (never an unrelated `B`). -/
  Bsrc : ℕ → ℝ
  /-- The perturbed certificate kernel `H_ε`. -/
  Heps : ℕ → ℝ

namespace PhysicalWeightData

variable (w : PhysicalWeightData)

/-- `a_X(n) = W(n/X)·[Λ(2n−1) + Λ(2n+1)]`. -/
noncomputable def aX (n : ℕ) : ℝ := w.W ((n : ℝ) / w.X) * (w.Lam (2 * n - 1) + w.Lam (2 * n + 1))

/-- `b_X(n) = 4·W(n/X)·Bsrc(n)`. -/
noncomputable def bX (n : ℕ) : ℝ := 4 * w.W ((n : ℝ) / w.X) * w.Bsrc n

/-- `w_X = a_X − b_X`. -/
noncomputable def wX (n : ℕ) : ℝ := w.aX n - w.bX n

/-- `H_X = H_ε`. -/
def HX (n : ℕ) : ℝ := w.Heps n

/-- **`wX_def`.**  `KERNEL-PROVED`.  The difference weight is literally `a_X − b_X`. -/
theorem wX_def (n : ℕ) : w.wX n = w.aX n - w.bX n := rfl

/-- **`aX_add_wX`.**  `KERNEL-PROVED`.  `a_X = b_X + w_X`, the form the transference
algebra uses. -/
theorem aX_eq_bX_add_wX (n : ℕ) : w.aX n = w.bX n + w.wX n := by
  simp [wX, aX, bX]

/-- **`weights_vanish_off_window`.**  `KERNEL-PROVED`.  Both physical weights vanish where
the smooth window vanishes. -/
theorem weights_vanish_off_window {n : ℕ} (h : w.W ((n : ℝ) / w.X) = 0) :
    w.aX n = 0 ∧ w.bX n = 0 ∧ w.wX n = 0 := by
  refine ⟨by simp [aX, h], by simp [bX, h], ?_⟩
  simp [wX, aX, bX, h]

/-- **`bX_determines_Bsrc`.**  `KERNEL-PROVED`.

The comparison weight pins the *source* function: wherever the window is nonzero, two
weight data with the same window and the same `b_X` have the same `Bsrc`.  Consequently
`Bsrc` may not be silently replaced by an unrelated `B`. -/
theorem bX_determines_Bsrc {w₁ w₂ : PhysicalWeightData} {n : ℕ}
    (hW : w₁.W ((n : ℝ) / w₁.X) = w₂.W ((n : ℝ) / w₂.X))
    (hne : w₁.W ((n : ℝ) / w₁.X) ≠ 0)
    (hb : w₁.bX n = w₂.bX n) : w₁.Bsrc n = w₂.Bsrc n := by
  simp only [bX, ← hW] at hb
  have h4 : (4 : ℝ) * w₁.W ((n : ℝ) / w₁.X) ≠ 0 := by
    simpa using hne
  exact mul_left_cancel₀ h4 hb

/-- **`BsrcPinned`** — `SOURCE PIN : OPEN / UNINHABITED`.

The predicate "`Bsrc` is the literal source comparison function of the run".  Only its
structural consequences are recorded; **no inhabitant is constructed**, and in particular
no unrelated `B` is substituted for it. -/
structure BsrcPinned (w : PhysicalWeightData) : Prop where
  /-- The source comparison function is nonnegative. -/
  nonneg : ∀ n, 0 ≤ w.Bsrc n
  /-- It is not identically zero on the audited scale. -/
  nontrivial : ∃ n, w.Bsrc n ≠ 0

/-- **`bsrcPin_not_automatic`.**  `KERNEL-PROVED`.  The source pin is a genuine obligation:
explicit data refute it. -/
theorem bsrcPin_not_automatic : ∃ w : PhysicalWeightData, ¬ BsrcPinned w := by
  refine ⟨⟨1, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩, ?_⟩
  rintro ⟨-, ⟨n, hn⟩⟩
  exact hn rfl

end PhysicalWeightData

/-! ## §3  The four error channels over the literal support classes -/

variable (d : PhysicalSupportData) (w : PhysicalWeightData)

/-- The `H_ε`-correlation of the difference weight over a region. -/
noncomputable def corrOn (R : Finset ℕ) : ℝ := ∑ n ∈ R, w.wX n * w.HX n

/-- **`Bmass`** — the comparison mass carried by the certificate-positive class `P_X`. -/
noncomputable def Bmass : ℝ := ∑ n ∈ d.PX, w.bX n

/-- **`primeMass`** — the prime mass carried by `P_X`. -/
noncomputable def primeMass : ℝ := ∑ n ∈ d.PX, w.aX n

/-- The total physical correlation over the audited range. -/
noncomputable def totalCorr : ℝ := corrOn w d.I

/-- **`E_M_exact`** — the exact `N1` (main/Möbius comparison) channel value. -/
noncomputable def E_M_exact : ℝ := corrOn w d.N1X

/-- **`E_2_exact`** — the exact `N2` (λ-collar) channel value. -/
noncomputable def E_2_exact : ℝ := corrOn w d.N2X

/-- **`E_L_exact`** — the exact `U` (leakage) channel value. -/
noncomputable def E_L_exact : ℝ := corrOn w d.UX

/-- **`E_T_deficit Cc`** — the exact transverse/total channel deficit
`Cc·Bmass − totalCorr`; the channel `E_T` is whatever dominates it. -/
noncomputable def E_T_deficit (Cc : ℝ) : ℝ := Cc * Bmass d w - totalCorr d w

/-- **`channels_decompose_totalCorr`.**  `KERNEL-PROVED`.

The only unconditional identity relating the channels: the total correlation is the sum of
the `P`-part and the three literal error-class parts.  **No analytic theorem is attached.**
-/
theorem channels_decompose_totalCorr :
    totalCorr d w = corrOn w d.PX + E_M_exact d w + E_2_exact d w + E_L_exact d w := by
  simpa [totalCorr, corrOn, E_M_exact, E_2_exact, E_L_exact] using
    d.sum_partition (fun n => w.wX n * w.HX n)

/-- **`P_correlation_eq_mass_difference`.**  `KERNEL-PROVED`.

If the certificate kernel equals `1` on the class `P_X` — the literal defining property of
that class — then the `P`-correlation is exactly `primeMass − Bmass`. -/
theorem P_correlation_eq_mass_difference (hH : ∀ n ∈ d.PX, w.HX n = 1) :
    corrOn w d.PX = primeMass d w - Bmass d w := by
  have h : ∀ n ∈ d.PX, w.wX n * w.HX n = w.aX n - w.bX n := by
    intro n hn
    rw [hH n hn, mul_one, w.wX_def]
  rw [corrOn, Finset.sum_congr rfl h, Finset.sum_sub_distrib]
  rfl

end PhysicalSupport
end Erdos287
