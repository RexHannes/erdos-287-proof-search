import RequestProject.CurrentProgramme.Erdos287FourErrorTransference
import RequestProject.CurrentProgramme.Erdos287MasterSourceTypedPerronPackets

/-!
# The endgame source sockets: master source, `N2` λ-collar, global `Bsrc` comparison,
Ford-83 explicit constants

```
MASTER SOURCE SOCKET            : OPEN / UNINHABITED
N2 LAMBDA-COLLAR SOCKET         : OPEN / UNINHABITED
GLOBAL Bsrc COMPARISON SOCKET   : OPEN / UNINHABITED
FORD-83 EXPLICIT CONSTANTS      : OPEN / UNINHABITED
```

This module is **append-only**.  It defines the four typed research sockets of the
fixed-certificate endgame.  **None of them is inhabited**, no constant is guessed and no
external analytic theorem is proved.  For each socket a counterguard shows that it is a
genuine constraint (explicit data refute it), so nothing is vacuous.

**§1 — the Ford source index and the owner type.**  The index carries every field the
reconstruction needs: `k`, `J`, `T`, the large-prime leaves, the `u/v` factors, the selected
`E`, the Perron/Mellin labels, the orientation, the source sign, and the owner.  The owner
type is *reused* (never re-declared): it is the banked six-constructor
`Erdos287.MasterSourcePackets.PacketOwner`.

**§2 — `MasterSourceToTypedPerronPacketsInput`.**  Its content is exactly the reconstruction
statement: the physical `H_ε` correlation equals the sum of typed owner packets over the
**complete** Ford source index, plus boundary, plus truncation.

**§3 — `FixedCertificateN2LambdaCollarInput`.**  Its conclusion is exactly
`E_2 ≤ δ₂ · Bmass`, with the `o(Bmass)` form recorded separately.  It is explicitly recorded
that the Ford bounded-sequence `N2` theorem is **not** a literal inhabitant for the physical
`Λ` weight, and a counterguard proves the two are not interchangeable.

**§4 — `GlobalBsrcComparisonMarginInput`.**  The global `B = Bsrc` equality, the `N1`
comparison formula, the `E_M` bound and the positive `Bmass` lower bound, in one uninhabited
socket.

**§5 — `Ford83ExplicitOEpsilonCollarConstants`.**  `K_pert`, `K_collar`, `ε₀`, `X₀` with the
two literal inequalities and the large-`X` threshold.  No constant is supplied.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace EndgameSockets

open Erdos287.PhysicalSupport
open Erdos287.FourErrorTransference

/-! ## §1  The Ford source index and the owner enumeration -/

/-- **`Owner`** — the owner enumeration of the endgame, *reused* from the banked
six-constructor packet-owner type:

```
    lowQ | Pascadi | C0 | transverse | bDiagonal | local
```
-/
abbrev Owner := Erdos287.MasterSourcePackets.PacketOwner

/-- **`owner_is_exactly_six`.**  `KERNEL-PROVED`.  The reused owner type has exactly the six
mandated constructors. -/
theorem owner_is_exactly_six : Fintype.card Owner = 6 :=
  Erdos287.MasterSourcePackets.owner_type_is_exactly_six

/-- **`FordSourceIndex`** — the complete index of the Ford source decomposition.  Every
field required by the reconstruction is present. -/
structure FordSourceIndex where
  /-- The dissection depth `k`. -/
  k : ℕ
  /-- The Perron dissection parameter `J`. -/
  J : ℕ
  /-- The Perron truncation height `T`. -/
  T : ℝ
  /-- The large-prime leaves of the row. -/
  largePrimeLeaves : List ℕ
  /-- The `u` factor. -/
  u : ℕ
  /-- The `v` factor. -/
  v : ℕ
  /-- The selected `E` set label. -/
  selectedE : ℕ
  /-- The Perron label. -/
  perronLabel : ℕ
  /-- The Mellin label. -/
  mellinLabel : ℕ
  /-- The orientation of the contour. -/
  orientation : Bool
  /-- The source sign (`true = +`, `false = −`). -/
  sourceSign : Bool
  /-- The owner of the packet carried by this index. -/
  owner : Owner

/-- **`fordSourceIndex_carries_owner`.**  `KERNEL-PROVED`.  The owner really is a field of
the index: it is recoverable from the index, and no separate owner map is needed. -/
theorem fordSourceIndex_carries_owner (i : FordSourceIndex) : ∃ o : Owner, i.owner = o :=
  ⟨i.owner, rfl⟩

/-! ## §2  The master-source socket -/

/-- **`MasterSourceToTypedPerronPacketsInput`** — `OPEN / UNINHABITED`.

The exact reconstruction theorem of the master source:

```
    physical H_ε correlation
      = Σ over the COMPLETE Ford source index of typed owner packets
        + boundary
        + truncation ,
```

together with owner accounting against a supplied account function `acct`, the pinned
boundary and truncation terms, and completeness of the index against the supplied
admissibility predicate.

**Nothing in this repository inhabits this structure at the physical data.** -/
structure MasterSourceToTypedPerronPacketsInput
    (d : PhysicalSupportData) (w : PhysicalWeightData)
    (admissible : FordSourceIndex → Prop) (acct : Owner → ℝ)
    (boundaryTerm truncationTerm : ℝ) where
  /-- The index type of the emitted packets. -/
  carrier : Type
  /-- Decidable equality on the carrier. -/
  carrierDec : DecidableEq carrier
  /-- The finite set of emitted packets. -/
  cells : Finset carrier
  /-- The Ford source label of each emitted packet. -/
  label : carrier → FordSourceIndex
  /-- The value of each emitted packet. -/
  packet : carrier → ℝ
  /-- **Completeness**: every admissible Ford source index is realised by an emitted
  packet. -/
  complete : ∀ f : FordSourceIndex, admissible f → ∃ i ∈ cells, label i = f
  /-- **Owner accounting**: the emitted packets sum to the supplied owner accounts. -/
  owner_accounting : ∑ i ∈ cells, packet i = ∑ o : Owner, acct o
  /-- **Reconstruction**: the physical correlation is packets + boundary + truncation. -/
  reconstruction :
    totalCorr d w = (∑ i ∈ cells, packet i) + boundaryTerm + truncationTerm

/-- **`masterSource_socket_is_a_genuine_constraint`.**  `KERNEL-PROVED`.

The master-source socket is not vacuous data-shuffling: for explicit parameters it is
**uninhabitable**, because the reconstruction and the owner accounting together pin the
physical correlation. -/
theorem masterSource_socket_is_a_genuine_constraint :
    ∃ (d : PhysicalSupportData) (w : PhysicalWeightData)
      (admissible : FordSourceIndex → Prop) (acct : Owner → ℝ) (bT tT : ℝ),
      IsEmpty (MasterSourceToTypedPerronPacketsInput d w admissible acct bT tT) := by
  refine ⟨⟨∅, fun _ => SupportClass.P⟩, ⟨1, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun _ => False, fun _ => 0, 1, 0, ?_⟩
  constructor
  intro h
  have hrec := h.reconstruction
  have hacct := h.owner_accounting
  have hzero : totalCorr (⟨∅, fun _ => SupportClass.P⟩ : PhysicalSupportData)
      (⟨1, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩ : PhysicalWeightData) = 0 := by
    simp [totalCorr, corrOn]
  rw [hzero, hacct] at hrec
  simp at hrec

/-- **`masterSource_socket_not_inhabited_here`.**  `KERNEL-PROVED`.

Nothing in this module produces the socket: the statement that *some* parameter tuple makes
it uninhabited is precisely the previous theorem, and no constructor application for the
physical data occurs anywhere. -/
theorem masterSource_socket_not_inhabited_here :
    ∃ (d : PhysicalSupportData) (w : PhysicalWeightData)
      (admissible : FordSourceIndex → Prop) (acct : Owner → ℝ) (bT tT : ℝ),
      IsEmpty (MasterSourceToTypedPerronPacketsInput d w admissible acct bT tT) :=
  masterSource_socket_is_a_genuine_constraint

/-! ## §3  The physical `N2` λ-collar socket -/

/-- **`FixedCertificateN2LambdaCollarInput`** — `OPEN / UNINHABITED`.

Its conclusion is exactly

```
    E_2 ≤ δ₂ · Bmass .
```

The physical `Λ` weight is the one carried by `w`; nothing here proves the inequality. -/
structure FixedCertificateN2LambdaCollarInput
    (d : PhysicalSupportData) (w : PhysicalWeightData) (delta2 : ℝ) : Prop where
  /-- The collar constant is positive. -/
  delta2_pos : 0 < delta2
  /-- The literal collar conclusion. -/
  collar : E_2_exact d w ≤ delta2 * Bmass d w

/-- **`N2CollarVanishing`** — the stronger `E_2 = o(Bmass)` representation, along a scale
family.  Also **not** proved here. -/
def N2CollarVanishing (E2 B : ℝ → ℝ) : Prop :=
  ∀ delta : ℝ, 0 < delta → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → E2 X ≤ delta * B X

/-- **`vanishing_gives_collar_at_each_scale`.**  `KERNEL-PROVED`.

The `o(Bmass)` form is genuinely stronger: it yields the fixed-`δ₂` collar at every
sufficiently large scale. -/
theorem vanishing_gives_collar_at_each_scale {E2 B : ℝ → ℝ} (h : N2CollarVanishing E2 B)
    {delta : ℝ} (hd : 0 < delta) : ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → E2 X ≤ delta * B X :=
  h delta hd

/-- **`BoundedSequenceWeight`** — the hypothesis of the Ford bounded-sequence `N2` theorem:
the arithmetic weight is bounded by `1`.  The physical `Λ` weight does **not** satisfy it. -/
def BoundedSequenceWeight (w : PhysicalWeightData) : Prop := ∀ n : ℕ, |w.aX n| ≤ 1

/-- **`LambdaGrowth`** — the physical situation: the `Λ`-weighted sequence is unbounded. -/
def LambdaGrowth (w : PhysicalWeightData) : Prop := ∀ C : ℝ, ∃ n : ℕ, C < |w.aX n|

/-- **`boundedSequence_excludes_lambda_growth`.**  `KERNEL-PROVED`.

The Ford bounded-sequence hypothesis and the physical `Λ` growth are incompatible, so the
bounded-sequence `N2` theorem is **not a literal inhabitant** of the collar socket for the
physical `Λ` weight. -/
theorem boundedSequence_excludes_lambda_growth (w : PhysicalWeightData)
    (hb : BoundedSequenceWeight w) : ¬ LambdaGrowth w := by
  intro hg
  obtain ⟨n, hn⟩ := hg 1
  exact absurd (hb n) (not_le.2 hn)

/-- **`boundedSequence_does_not_give_the_collar`.**  `KERNEL-PROVED` counterguard.

Even where the bounded-sequence hypothesis *does* hold, it does not imply the collar
conclusion: explicit data satisfy `BoundedSequenceWeight` while violating
`E_2 ≤ δ₂ · Bmass` for every positive `δ₂`.  Hence no monotonicity or transfer argument
may replace the missing physical input. -/
theorem boundedSequence_does_not_give_the_collar (delta2 : ℝ) :
    ∃ (d : PhysicalSupportData) (w : PhysicalWeightData),
      BoundedSequenceWeight w ∧ ¬ (E_2_exact d w ≤ delta2 * Bmass d w) := by
  refine ⟨⟨{1}, fun _ => SupportClass.N2⟩, ⟨1, fun _ => 1, fun _ => 0, fun _ => -1,
    fun _ => 1⟩, ?_, ?_⟩
  · intro n
    simp [PhysicalWeightData.aX]
  · have hB : Bmass (⟨{1}, fun _ => SupportClass.N2⟩ : PhysicalSupportData)
        (⟨1, fun _ => 1, fun _ => 0, fun _ => -1, fun _ => 1⟩ : PhysicalWeightData) = 0 := by
      simp [Bmass, PhysicalSupportData.PX, PhysicalSupportData.region]
    have hE : E_2_exact (⟨{1}, fun _ => SupportClass.N2⟩ : PhysicalSupportData)
        (⟨1, fun _ => 1, fun _ => 0, fun _ => -1, fun _ => 1⟩ : PhysicalWeightData) = 4 := by
      simp [E_2_exact, corrOn, PhysicalSupportData.N2X, PhysicalSupportData.region,
        PhysicalWeightData.wX, PhysicalWeightData.aX, PhysicalWeightData.bX,
        PhysicalWeightData.HX]
    rw [hE, hB]
    norm_num

/-- **`n2Collar_socket_is_a_genuine_constraint`.**  `KERNEL-PROVED`.

The collar socket is refutable at explicit data, hence a genuine open obligation. -/
theorem n2Collar_socket_is_a_genuine_constraint :
    ∃ (d : PhysicalSupportData) (w : PhysicalWeightData) (delta2 : ℝ),
      ¬ FixedCertificateN2LambdaCollarInput d w delta2 := by
  obtain ⟨d, w, -, hfail⟩ := boundedSequence_does_not_give_the_collar 1
  exact ⟨d, w, 1, fun h => hfail h.collar⟩

/-! ## §4  The global `Bsrc` / `N1` comparison socket -/

/-- **`GlobalBsrcComparisonMarginInput`** — `OPEN / UNINHABITED`.

The four literal source items of the comparison pin:

* the global equality between the physical `B` and the source `Bsrc`;
* the `N1` comparison formula;
* the `E_M` bound;
* the positive lower bound for `Bmass`.

**No inhabitant is constructed.** -/
structure GlobalBsrcComparisonMarginInput
    (d : PhysicalSupportData) (w : PhysicalWeightData)
    (physicalB : ℕ → ℝ) (deltaM bLower : ℝ) : Prop where
  /-- Global equality of the physical `B` with the source `Bsrc` on the audited range. -/
  global_equality : ∀ n ∈ d.I, physicalB n = w.Bsrc n
  /-- The `N1` comparison formula: the `N1` correlation is comparable to the mass built
  from the physical `B`. -/
  N1_comparison : E_M_exact d w ≤ deltaM * ∑ n ∈ d.PX, physicalB n
  /-- The `E_M` bound in `Bmass` form. -/
  E_M_bound : E_M_exact d w ≤ deltaM * Bmass d w
  /-- A positive lower bound for the comparison mass. -/
  Bmass_lower : 0 < bLower ∧ bLower ≤ Bmass d w

/-- **`bsrcComparison_socket_is_a_genuine_constraint`.**  `KERNEL-PROVED`.

Refutable at explicit data (the zero configuration has `Bmass = 0`), hence a genuine open
obligation. -/
theorem bsrcComparison_socket_is_a_genuine_constraint :
    ∃ (d : PhysicalSupportData) (w : PhysicalWeightData) (physicalB : ℕ → ℝ)
      (deltaM bLower : ℝ),
      ¬ GlobalBsrcComparisonMarginInput d w physicalB deltaM bLower := by
  refine ⟨⟨∅, fun _ => SupportClass.P⟩, ⟨1, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun _ => 0, 1, 1, ?_⟩
  intro h
  obtain ⟨hpos, hle⟩ := h.Bmass_lower
  have hB : Bmass (⟨∅, fun _ => SupportClass.P⟩ : PhysicalSupportData)
      (⟨1, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩ : PhysicalWeightData) = 0 := by
    simp [Bmass, PhysicalSupportData.PX, PhysicalSupportData.region]
  rw [hB] at hle
  linarith

/-- **`bsrc_is_not_replaced_by_an_arbitrary_B`.**  `KERNEL-PROVED CONDITIONAL`.

Conditionally on the comparison socket, the physical `B` *is* the source `Bsrc` on the whole
audited range: the socket forbids substituting an unrelated comparison function. -/
theorem bsrc_is_not_replaced_by_an_arbitrary_B
    {d : PhysicalSupportData} {w : PhysicalWeightData} {physicalB : ℕ → ℝ} {deltaM bLower : ℝ}
    (h : GlobalBsrcComparisonMarginInput d w physicalB deltaM bLower) :
    ∀ n ∈ d.I, physicalB n = w.Bsrc n :=
  h.global_equality

/-! ## §5  The Ford-83 explicit `O(ε)` collar constants -/

/-- **`Ford83ExplicitOEpsilonCollarConstants`** — `OPEN / UNINHABITED`.

The explicit-constant socket:

```
    m_ε  ≥  6·10⁻⁶ − K_pert·ε          (for 0 < ε ≤ ε₀),
    E_2  ≤  K_collar·ε·Bmass           (for X ≥ X₀),
```

carrying `K_pert`, `K_collar`, `ε₀`, `X₀`.  **No constant is guessed**: the structure is
parametrised by the supplied margin function and collar family and is never inhabited. -/
structure Ford83ExplicitOEpsilonCollarConstants
    (margin : ℝ → ℝ) (E2 Bm : ℝ → ℝ) where
  /-- The perturbation constant. -/
  K_pert : ℝ
  /-- The collar constant. -/
  K_collar : ℝ
  /-- The perturbation threshold. -/
  eps0 : ℝ
  /-- The scale threshold. -/
  X0 : ℝ
  /-- The constants are positive. -/
  K_pert_pos : 0 < K_pert
  /-- The collar constant is positive. -/
  K_collar_pos : 0 < K_collar
  /-- The perturbation threshold is positive. -/
  eps0_pos : 0 < eps0
  /-- The scale threshold is positive. -/
  X0_pos : 0 < X0
  /-- The explicit margin inequality. -/
  margin_bound : ∀ eps : ℝ, 0 < eps → eps ≤ eps0 → (6 / 1000000 : ℝ) - K_pert * eps ≤ margin eps
  /-- The explicit collar inequality, for every admissible `ε` above the scale threshold. -/
  collar_bound : ∀ eps : ℝ, 0 < eps → eps ≤ eps0 → ∀ X : ℝ, X0 ≤ X →
    E2 X ≤ K_collar * eps * Bm X

/-- **`ford83_constants_give_positive_margin_below_threshold`.**  `KERNEL-PROVED
CONDITIONAL`.

*If* the explicit constants are ever supplied, the margin is positive for every
`0 < ε < min(ε₀, 6·10⁻⁶/K_pert)`.  The threshold is computed **from the supplied
constants**; none is manufactured here. -/
theorem ford83_constants_give_positive_margin_below_threshold
    {margin E2 Bm : ℝ → ℝ} (c : Ford83ExplicitOEpsilonCollarConstants margin E2 Bm)
    {eps : ℝ} (hpos : 0 < eps) (hle : eps ≤ c.eps0)
    (hsmall : eps < (6 / 1000000 : ℝ) / c.K_pert) : 0 < margin eps := by
  have hK := c.K_pert_pos
  have hb := c.margin_bound eps hpos hle
  have : c.K_pert * eps < 6 / 1000000 := by
    rw [lt_div_iff₀ hK] at hsmall
    linarith [hsmall]
  linarith

/-- **`ford83_constants_socket_uninhabited_here`.**  `KERNEL-PROVED`.

The constants socket is a genuine obligation: for an explicit margin family it is
uninhabitable, so no constant may be read off from this repository. -/
theorem ford83_constants_socket_uninhabited_here :
    ∃ (margin E2 Bm : ℝ → ℝ),
      IsEmpty (Ford83ExplicitOEpsilonCollarConstants margin E2 Bm) := by
  refine ⟨fun _ => -1, fun _ => 0, fun _ => 0, ?_⟩
  constructor
  intro c
  have hK := c.K_pert_pos
  have he := c.eps0_pos
  set e : ℝ := min c.eps0 ((6 / 1000000 : ℝ) / (2 * c.K_pert)) with he'
  have hepos : 0 < e := lt_min he (by positivity)
  have hb := c.margin_bound e hepos (min_le_left _ _)
  have h2 : e ≤ (6 / 1000000 : ℝ) / (2 * c.K_pert) := min_le_right _ _
  have h3 : c.K_pert * e ≤ 6 / 2000000 := by
    rw [le_div_iff₀ (by positivity)] at h2
    linarith
  simp only at hb
  linarith

end EndgameSockets
end Erdos287
