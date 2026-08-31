import Mathlib
import RequestProject.CurrentProgramme.Erdos287TransverseCarrierInterface

/-!
# Transverse source factorisation and reduced conductors — Erdős #287 (append-only)

This module is **append-only**.  It edits nothing, weakens nothing and reproves nothing; it adds
the *exact arithmetic* of the transverse source factorisation now banked by the research notes.

For one transverse packet `P` the source records

```
R_P = z² q_C q_m,      q_C = 2 (e/a₁) (r₂/c₂) b₁Flat,      q_m = m₂Flat.
```

We name

```
E  := e/a₁,   R := r₂/c₂,   B₀ := b₁Flat,   M₀ := m₂Flat,
```

and after the row-gcd reduction by `Δ`

```
δ₂ := gcd(Δ,2),  δ_E := gcd(Δ,E),  δ_B := gcd(Δ,B₀),
2°  := 2/δ₂,     E°  := E/δ_E,     B°  := B₀/δ_B,
q̄   := 2° E° R B°,        R̂_P := z² q̄ M₀.
```

Conservatism.

* Every division that occurs is *justified*: `a₁ ∣ e` and `c₂ ∣ r₂` are explicit fields of the
  source structure, and each `δ` divides its partner by `Nat.gcd_dvd_*`.  For every quotient the
  exactness lemma `(quotient) * (divisor) = (dividend)` is proved.
* No analytic length statement occurs here.  `E°`, `R`, `B°`, `M₀`, `z`, `2°` are natural
  numbers with no assumed size.
* The carrier classification of §5 is **metadata**: it records the signless / signed / fixed
  bookkeeping of the source and asserts nothing about lengths or cancellation.

Contents.

* §1  the source packet and its exact quotients;
* §2  the reduced `q_C` factor `q̄` and the reduced packet conductor `R̂_P`;
* §3  the primed packet (the *same* structure, no copy-paste duplication);
* §4  the cross-packet reduced conductor `Q_*`, `d_*`, `Q_*^red`;
* §5  carrier metadata;
* §6  an elementary finite harmonic-square bound for the `R`-carrier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace TransverseReducedConductor

open Finset

/-! ## §1  The transverse source packet -/

/-- Source data of one transverse packet, in the literal shape used by the research notes.

The two divisibility fields are what makes `E = e/a₁` and `R = r₂/c₂` *exact* quotients; no
division is performed without them.  No size (length) assumption is made on any field. -/
structure TransversePacket where
  /-- The square carrier `z` (contributes `z²`). -/
  z : ℕ
  /-- Numerator of the `E`-carrier. -/
  e : ℕ
  /-- Denominator of the `E`-carrier. -/
  a1 : ℕ
  /-- Numerator of the `R`-carrier. -/
  r2 : ℕ
  /-- Denominator of the `R`-carrier. -/
  c2 : ℕ
  /-- The flat `b₁` factor `B₀`. -/
  b1Flat : ℕ
  /-- The flat `m₂` factor `M₀ = q_m`. -/
  m2Flat : ℕ
  /-- The row-gcd parameter `Δ`. -/
  Delta : ℕ
  /-- `z` is positive. -/
  z_pos : 0 < z
  /-- `a₁` is positive. -/
  a1_pos : 0 < a1
  /-- `c₂` is positive. -/
  c2_pos : 0 < c2
  /-- `e` is positive. -/
  e_pos : 0 < e
  /-- `r₂` is positive. -/
  r2_pos : 0 < r2
  /-- `B₀` is positive. -/
  b1Flat_pos : 0 < b1Flat
  /-- `M₀` is positive. -/
  m2Flat_pos : 0 < m2Flat
  /-- `Δ` is positive. -/
  Delta_pos : 0 < Delta
  /-- The `E`-carrier quotient is exact. -/
  a1_dvd_e : a1 ∣ e
  /-- The `R`-carrier quotient is exact. -/
  c2_dvd_r2 : c2 ∣ r2

namespace TransversePacket

variable (P : TransversePacket)

/-- `E := e/a₁`. -/
def E : ℕ := P.e / P.a1

/-- `R := r₂/c₂`. -/
def R : ℕ := P.r2 / P.c2

/-- `B₀ := b₁Flat`. -/
def B0 : ℕ := P.b1Flat

/-- `M₀ := m₂Flat = q_m`. -/
def M0 : ℕ := P.m2Flat

/-- **`E_mul_a1`.**  `LEAN_PROVED`.  The `E`-quotient is exact. -/
theorem E_mul_a1 : P.E * P.a1 = P.e := Nat.div_mul_cancel P.a1_dvd_e

/-- **`R_mul_c2`.**  `LEAN_PROVED`.  The `R`-quotient is exact. -/
theorem R_mul_c2 : P.R * P.c2 = P.r2 := Nat.div_mul_cancel P.c2_dvd_r2

/-- **`E_pos`.**  `LEAN_PROVED`. -/
theorem E_pos : 0 < P.E := Nat.div_pos (Nat.le_of_dvd P.e_pos P.a1_dvd_e) P.a1_pos

/-- **`R_pos`.**  `LEAN_PROVED`. -/
theorem R_pos : 0 < P.R := Nat.div_pos (Nat.le_of_dvd P.r2_pos P.c2_dvd_r2) P.c2_pos

/-- **`B0_pos`.**  `LEAN_PROVED`. -/
theorem B0_pos : 0 < P.B0 := P.b1Flat_pos

/-- **`M0_pos`.**  `LEAN_PROVED`. -/
theorem M0_pos : 0 < P.M0 := P.m2Flat_pos

/-- The unreduced source factor `q_C = 2 E R B₀`. -/
def qC : ℕ := 2 * P.E * P.R * P.B0

/-- The unreduced packet conductor `R_P = z² q_C q_m`. -/
def RSource : ℕ := P.z ^ 2 * P.qC * P.M0

/-- `δ₂ := gcd(Δ,2)`. -/
def delta2 : ℕ := Nat.gcd P.Delta 2

/-- `δ_E := gcd(Δ,E)`. -/
def deltaE : ℕ := Nat.gcd P.Delta P.E

/-- `δ_B := gcd(Δ,B₀)`. -/
def deltaB : ℕ := Nat.gcd P.Delta P.B0

/-- `2° := 2/δ₂`. -/
def twoCirc : ℕ := 2 / P.delta2

/-- `E° := E/δ_E`. -/
def ECirc : ℕ := P.E / P.deltaE

/-- `B° := B₀/δ_B`. -/
def BCirc : ℕ := P.B0 / P.deltaB

/-- **`delta2_dvd_two`.**  `LEAN_PROVED`. -/
theorem delta2_dvd_two : P.delta2 ∣ 2 := Nat.gcd_dvd_right _ _

/-- **`deltaE_dvd_E`.**  `LEAN_PROVED`. -/
theorem deltaE_dvd_E : P.deltaE ∣ P.E := Nat.gcd_dvd_right _ _

/-- **`deltaB_dvd_B0`.**  `LEAN_PROVED`. -/
theorem deltaB_dvd_B0 : P.deltaB ∣ P.B0 := Nat.gcd_dvd_right _ _

/-- **`twoCirc_mul_delta2`.**  `LEAN_PROVED`.  The `2°` quotient is exact. -/
theorem twoCirc_mul_delta2 : P.twoCirc * P.delta2 = 2 :=
  Nat.div_mul_cancel P.delta2_dvd_two

/-- **`ECirc_mul_deltaE`.**  `LEAN_PROVED`.  The `E°` quotient is exact. -/
theorem ECirc_mul_deltaE : P.ECirc * P.deltaE = P.E :=
  Nat.div_mul_cancel P.deltaE_dvd_E

/-- **`BCirc_mul_deltaB`.**  `LEAN_PROVED`.  The `B°` quotient is exact. -/
theorem BCirc_mul_deltaB : P.BCirc * P.deltaB = P.B0 :=
  Nat.div_mul_cancel P.deltaB_dvd_B0

/-- **`twoCirc_pos`.**  `LEAN_PROVED`. -/
theorem twoCirc_pos : 0 < P.twoCirc :=
  Nat.div_pos (Nat.le_of_dvd (by norm_num) P.delta2_dvd_two)
    (Nat.gcd_pos_of_pos_left 2 P.Delta_pos)

/-- **`ECirc_pos`.**  `LEAN_PROVED`. -/
theorem ECirc_pos : 0 < P.ECirc :=
  Nat.div_pos (Nat.le_of_dvd P.E_pos P.deltaE_dvd_E) (Nat.gcd_pos_of_pos_left _ P.Delta_pos)

/-- **`BCirc_pos`.**  `LEAN_PROVED`. -/
theorem BCirc_pos : 0 < P.BCirc :=
  Nat.div_pos (Nat.le_of_dvd P.B0_pos P.deltaB_dvd_B0) (Nat.gcd_pos_of_pos_left _ P.Delta_pos)

/-! ## §2  The reduced `q_C` factor and the reduced packet conductor -/

/-- The reduced `q_C` factor `q̄ = 2° E° R B°`. -/
def qBar : ℕ := P.twoCirc * P.ECirc * P.R * P.BCirc

/-- The `q_m` factor of the packet, `q_m = M₀`. -/
def qm : ℕ := P.M0

/-- The reduced packet conductor `R̂_P = z² q̄ M₀`. -/
def RHat : ℕ := P.z ^ 2 * P.qBar * P.M0

/-- **`qBar_pos`.**  `LEAN_PROVED`. -/
theorem qBar_pos : 0 < P.qBar :=
  Nat.mul_pos (Nat.mul_pos (Nat.mul_pos P.twoCirc_pos P.ECirc_pos) P.R_pos) P.BCirc_pos

/-- **`RHat_pos`.**  `LEAN_PROVED`. -/
theorem RHat_pos : 0 < P.RHat :=
  Nat.mul_pos (Nat.mul_pos (pow_pos P.z_pos 2) P.qBar_pos) P.M0_pos

/-- **`RHat_eq`.**  `LEAN_PROVED`.  The reduced packet conductor in the source's own shape,
`R̂_P = z² q̄ q_m`. -/
theorem RHat_eq : P.RHat = P.z ^ 2 * P.qBar * P.qm := rfl

/-- **`qBar_mul_deltas`.**  `LEAN_PROVED`.  The exact relation between the reduced factor `q̄` and
the unreduced source factor `q_C`: multiplying `q̄` back by the three row gcds returns `q_C`.
No cancellation is asserted beyond the proved divisibilities. -/
theorem qBar_mul_deltas : P.qBar * (P.delta2 * P.deltaE * P.deltaB) = P.qC := by
  have h2 := P.twoCirc_mul_delta2
  have hE := P.ECirc_mul_deltaE
  have hB := P.BCirc_mul_deltaB
  calc P.qBar * (P.delta2 * P.deltaE * P.deltaB)
      = (P.twoCirc * P.delta2) * ((P.ECirc * P.deltaE) * P.R * (P.BCirc * P.deltaB)) := by
        simp only [qBar]; ring
    _ = 2 * P.E * P.R * P.B0 := by rw [h2, hE, hB]; ring
    _ = P.qC := rfl

/-- **`qBar_dvd_qC`.**  `LEAN_PROVED`.  In particular `q̄ ∣ q_C`. -/
theorem qBar_dvd_qC : P.qBar ∣ P.qC :=
  ⟨P.delta2 * P.deltaE * P.deltaB, P.qBar_mul_deltas.symm⟩

end TransversePacket

/-! ## §3  The primed packet

No new structure is introduced: the primed packet `P'` is an inhabitant of the *same* structure
`TransversePacket`, so `z'`, `q̄'`, `M₀'`, `R̂_{P'}` are `P'.z`, `P'.qBar`, `P'.M0`, `P'.RHat`.
The following theorem records that the symmetric data is available with no duplication. -/

/-- **`primed_packet_symmetric`.**  `LEAN_PROVED`.  For an arbitrary primed packet the same exact
factorisation holds; the structure is reused, not copied. -/
theorem primed_packet_symmetric (P' : TransversePacket) :
    P'.RHat = P'.z ^ 2 * P'.qBar * P'.M0 ∧ 0 < P'.RHat ∧
      P'.qBar * (P'.delta2 * P'.deltaE * P'.deltaB) = P'.qC :=
  ⟨rfl, P'.RHat_pos, P'.qBar_mul_deltas⟩

/-! ## §4  The cross-packet reduced conductor -/

/-- **`lcm_eq_mul_div_gcd`.**  `LEAN_PROVED`.  The elementary identity
`lcm(a,b) = a b / gcd(a,b)` for a positive first argument (Mathlib's `Nat.gcd_mul_lcm` reused;
positivity of `a` alone already makes `gcd(a,b)` positive, so no hypothesis on `b` is needed). -/
theorem lcm_eq_mul_div_gcd {a b : ℕ} (ha : 0 < a) :
    Nat.lcm a b = a * b / Nat.gcd a b := by
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have h := Nat.gcd_mul_lcm a b
  exact (Nat.div_eq_of_eq_mul_left hg (by rw [← h]; ring)).symm

/-- The cross-packet conductor `Q_* = lcm(R̂_P, R̂_{P'})`. -/
def QStar (P P' : TransversePacket) : ℕ := Nat.lcm P.RHat P'.RHat

/-- The reduction parameter `d_* = gcd(B_*, Q_*)`, for a source numerator parameter `B_*`. -/
def dStar (P P' : TransversePacket) (BStar : ℕ) : ℕ := Nat.gcd BStar (QStar P P')

/-- The reduced cross-packet conductor `Q_*^red = Q_*/d_*`. -/
def QStarRed (P P' : TransversePacket) (BStar : ℕ) : ℕ := QStar P P' / dStar P P' BStar

/-- **`QStar_pos`.**  `LEAN_PROVED`. -/
theorem QStar_pos (P P' : TransversePacket) : 0 < QStar P P' :=
  Nat.pos_of_ne_zero (Nat.lcm_ne_zero P.RHat_pos.ne' P'.RHat_pos.ne')

/-- **`dStar_dvd_QStar`.**  `LEAN_PROVED`. -/
theorem dStar_dvd_QStar (P P' : TransversePacket) (BStar : ℕ) :
    dStar P P' BStar ∣ QStar P P' := Nat.gcd_dvd_right _ _

/-- **`QStarRed_mul_dStar`.**  `LEAN_PROVED`.  The `Q_*^red` quotient is exact. -/
theorem QStarRed_mul_dStar (P P' : TransversePacket) (BStar : ℕ) :
    QStarRed P P' BStar * dStar P P' BStar = QStar P P' :=
  Nat.div_mul_cancel (dStar_dvd_QStar P P' BStar)

/-- **`QStarRed_exact_normal_form`.**  `LEAN_PROVED`.  The exact (division-free) normal form

`Q_*^red · (gcd(R̂_P, R̂_{P'}) · d_*) = R̂_P · R̂_{P'}`. -/
theorem QStarRed_exact_normal_form (P P' : TransversePacket) (BStar : ℕ) :
    QStarRed P P' BStar * (Nat.gcd P.RHat P'.RHat * dStar P P' BStar) = P.RHat * P'.RHat := by
  have h1 : QStarRed P P' BStar * dStar P P' BStar = QStar P P' :=
    QStarRed_mul_dStar P P' BStar
  have h2 : Nat.gcd P.RHat P'.RHat * Nat.lcm P.RHat P'.RHat = P.RHat * P'.RHat :=
    Nat.gcd_mul_lcm _ _
  calc QStarRed P P' BStar * (Nat.gcd P.RHat P'.RHat * dStar P P' BStar)
      = (QStarRed P P' BStar * dStar P P' BStar) * Nat.gcd P.RHat P'.RHat := by ring
    _ = Nat.gcd P.RHat P'.RHat * Nat.lcm P.RHat P'.RHat := by
        rw [h1]; simp [QStar, Nat.mul_comm]
    _ = P.RHat * P'.RHat := h2

/-- **`QStarRed_eq_div`.**  `LEAN_PROVED`.  The requested divided form

`Q_*^red = R̂_P R̂_{P'} / (gcd(R̂_P, R̂_{P'}) d_*)`,

valid whenever `B_*` is positive (so that `d_* > 0`).  No analytic length claim is attached. -/
theorem QStarRed_eq_div (P P' : TransversePacket) {BStar : ℕ} (hB : 0 < BStar) :
    QStarRed P P' BStar =
      P.RHat * P'.RHat / (Nat.gcd P.RHat P'.RHat * dStar P P' BStar) := by
  have hg : 0 < Nat.gcd P.RHat P'.RHat := Nat.gcd_pos_of_pos_left _ P.RHat_pos
  have hd : 0 < dStar P P' BStar := Nat.gcd_pos_of_pos_left _ hB
  exact (Nat.div_eq_of_eq_mul_left (Nat.mul_pos hg hd)
    (QStarRed_exact_normal_form P P' BStar).symm).symm

/-! ## §5  Carrier metadata

Classification of the atomic factors of a packet.  This is **metadata only**: no length, no
cancellation and no analytic property is encoded, and nothing here feeds any inequality. -/

/-- The atomic factors of a reduced packet. -/
inductive PacketFactor
  /-- `z²`. -/
  | zSquare
  /-- `2°`. -/
  | twoCirc
  /-- `E°`. -/
  | ECirc
  /-- `R`. -/
  | Rcarrier
  /-- `B°`. -/
  | BCirc
  /-- `M₀`. -/
  | M0
  deriving DecidableEq, Fintype, Repr

/-- Bookkeeping classes of the atomic factors. -/
inductive CarrierClass
  /-- Signless. -/
  | signless
  /-- Signed / Möbius-bearing. -/
  | signed
  /-- Fixed / structural. -/
  | fixed
  deriving DecidableEq, Fintype, Repr

open PacketFactor CarrierClass

/-- The carrier classification of the atomic factors, for a packet and, identically, for the
primed packet (the structure is shared, so one table serves both). -/
def carrierClass : PacketFactor → CarrierClass
  | zSquare => fixed
  | PacketFactor.twoCirc => fixed
  | PacketFactor.ECirc => signless
  | Rcarrier => signless
  | PacketFactor.BCirc => signed
  | PacketFactor.M0 => signed

/-- **`carrierClass_table`.**  `LEAN_PROVED`.  The requested classification, verbatim. -/
theorem carrierClass_table :
    carrierClass PacketFactor.ECirc = signless ∧
    carrierClass Rcarrier = signless ∧
    carrierClass PacketFactor.BCirc = signed ∧
    carrierClass PacketFactor.M0 = signed ∧
    carrierClass zSquare = fixed ∧
    carrierClass PacketFactor.twoCirc = fixed := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`carrierClass_is_metadata`.**  `LEAN_PROVED`.  The classification is a bare function into a
three-element label type: the classes are pairwise distinct and no factor of any packet is
asserted to be long, short, or to satisfy any inequality. -/
theorem carrierClass_is_metadata :
    signless ≠ signed ∧ signless ≠ fixed ∧ signed ≠ fixed := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-! ## §6  `R`-carrier harmonic energy (elementary, unconditional) -/

/-- **`Rcarrier_harmonic_square_bound`.**  `LEAN_PROVED`.  The elementary finite harmonic-square
bound for the `R`-carrier, with the explicit constant `C = 1`:

`∑_{R ∈ [L, 2L)} |1/(c₂ R)|² ≤ 1/(c₂² L)`.

Purely finite and unconditional; no analytic input. -/
theorem Rcarrier_harmonic_square_bound (c2 L : ℕ) (hc : 0 < c2) (hL : 0 < L) :
    ∑ r ∈ Finset.Ico L (2 * L), (1 / ((c2 : ℝ) * (r : ℝ))) ^ 2
      ≤ 1 / ((c2 : ℝ) ^ 2 * (L : ℝ)) := by
  have hc0 : (0 : ℝ) < (c2 : ℝ) := by exact_mod_cast hc
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hterm : ∀ r ∈ Finset.Ico L (2 * L),
      (1 / ((c2 : ℝ) * (r : ℝ))) ^ 2 ≤ 1 / ((c2 : ℝ) ^ 2 * (L : ℝ) ^ 2) := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    have hrL : (L : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.1
    have hr0 : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le hL0 hrL
    rw [div_pow, one_pow, mul_pow]
    apply one_div_le_one_div_of_le (by positivity)
    have : (L : ℝ) ^ 2 ≤ (r : ℝ) ^ 2 := by nlinarith
    nlinarith [sq_nonneg ((c2 : ℝ))]
  have hcard : (Finset.Ico L (2 * L)).card = L := by
    rw [Nat.card_Ico]; omega
  calc ∑ r ∈ Finset.Ico L (2 * L), (1 / ((c2 : ℝ) * (r : ℝ))) ^ 2
      ≤ ∑ _r ∈ Finset.Ico L (2 * L), 1 / ((c2 : ℝ) ^ 2 * (L : ℝ) ^ 2) :=
        Finset.sum_le_sum hterm
    _ = (L : ℝ) * (1 / ((c2 : ℝ) ^ 2 * (L : ℝ) ^ 2)) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ = 1 / ((c2 : ℝ) ^ 2 * (L : ℝ)) := by
        field_simp

end TransverseReducedConductor
end Erdos287
