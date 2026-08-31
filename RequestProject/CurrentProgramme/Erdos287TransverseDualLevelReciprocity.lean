import Mathlib
import RequestProject.CurrentProgramme.Erdos287TransverseBezoutThreeAxisFourier

/-!
# Dual-level CRT split and additive reciprocity — Erdős #287 (append-only)

This module is **append-only**.  It formalises the exact coordinate switch of the dual level:

* an explicit additive phase `e_n(a) = exp(2π i a / n)` with its three structural lemmas
  (norm one, additivity, invariance under `a ≡ a' (mod n)`) and the exact coprime splitting
  `e_{mn}(b n + c m) = e_m(b) · e_n(c)`;
* the **dual CRT split** of `e_{m r₀}(Δ γ_g q⁻¹)` into
  `e_m(Δ c_m (q r₀)⁻¹) · e_{r₀}(Δ d_ℓ (m q)⁻¹)`, first as an exact integer congruence and then
  as an exact identity of complex phases;
* the **additive reciprocity** identity `z n + y r₀ ≡ 1 (mod n r₀)` for coprime `n, r₀` and its
  phase form, which is the arithmetic content of
  `1/(r₀ · (m q)) ↔ -inverse(r₀)/(m q) + inverse(m q)/r₀`;
* the dual normal form `C_{m q g}` and the affine coordinate `Ξ(ℓ)`.

Every modular inverse is a **supplied** quantity carrying its defining congruence: no inverse is
introduced from an unproved coprimality.  The Archimedean factor is a *parameter* of
`DualReciprocityData`; no smooth analysis is performed and no Archimedean bound is claimed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace TransverseDualLevel

/-! ## §1  Elementary integer CRT tools -/

/-- **`int_modEq_combine_coprime`.**  `LEAN_PROVED`.  Exact CRT combination: congruences modulo
two coprime natural moduli give the congruence modulo their product. -/
theorem int_modEq_combine_coprime {m n : ℕ} (h : Nat.Coprime m n) {a b : ℤ}
    (h1 : a ≡ b [ZMOD (m : ℤ)]) (h2 : a ≡ b [ZMOD (n : ℤ)]) :
    a ≡ b [ZMOD ((m * n : ℕ) : ℤ)] := by
  have d1 : (m : ℤ) ∣ b - a := Int.ModEq.dvd h1
  have d2 : (n : ℤ) ∣ b - a := Int.ModEq.dvd h2
  have hco : IsCoprime (m : ℤ) (n : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd_natCast_natCast] using h
  have : ((m : ℤ) * (n : ℤ)) ∣ b - a := hco.mul_dvd d1 d2
  exact Int.modEq_iff_dvd.mpr (by simpa using this)

/-- **`int_inverse_unique`.**  `LEAN_PROVED`.  Two inverses of the same element modulo `n` are
congruent modulo `n`.  (Used to identify `q⁻¹` computed in different moduli.) -/
theorem int_inverse_unique {n q A B : ℤ} (hA : q * A ≡ 1 [ZMOD n]) (hB : q * B ≡ 1 [ZMOD n]) :
    A ≡ B [ZMOD n] := by
  calc A = A * 1 := by ring
    _ ≡ A * (q * B) [ZMOD n] := (hB.symm).mul_left A
    _ = B * (q * A) := by ring
    _ ≡ B * 1 [ZMOD n] := hA.mul_left B
    _ = B := by ring

/-! ## §2  The explicit additive phase -/

/-- The additive phase `e_n(a) = exp(2π i a/n)`.  For `n = 0` it is the constant `1`. -/
noncomputable def addPhase (n : ℕ) (a : ℤ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((a : ℝ) / (n : ℝ)) : ℝ) : ℂ) * Complex.I)

/-- **`addPhase_norm`.**  `LEAN_PROVED`.  Every additive phase has modulus one. -/
theorem addPhase_norm (n : ℕ) (a : ℤ) : ‖addPhase n a‖ = 1 := by
  rw [addPhase]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **`addPhase_add`.**  `LEAN_PROVED`.  Additivity in the numerator. -/
theorem addPhase_add (n : ℕ) (a b : ℤ) :
    addPhase n (a + b) = addPhase n a * addPhase n b := by
  rw [addPhase, addPhase, addPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **`addPhase_period`.**  `LEAN_PROVED`.  The phase is trivial on multiples of the modulus. -/
theorem addPhase_period {n : ℕ} (hn : n ≠ 0) (k : ℤ) : addPhase n ((n : ℤ) * k) = 1 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hrw : ((2 * Real.pi * ((((n : ℤ) * k : ℤ) : ℝ) / (n : ℝ)) : ℝ) : ℂ) * Complex.I
      = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    have : (((((n : ℤ) * k : ℤ)) : ℝ) / (n : ℝ)) = (k : ℝ) := by
      push_cast
      field_simp
    rw [this]
    push_cast
    ring
  rw [addPhase, hrw]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-- **`addPhase_congr`.**  `LEAN_PROVED`.  The phase depends on the numerator only modulo `n`. -/
theorem addPhase_congr (n : ℕ) {a b : ℤ} (h : a ≡ b [ZMOD (n : ℤ)]) :
    addPhase n a = addPhase n b := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : a = b := by simpa [Int.ModEq] using h
    rw [this]
  · obtain ⟨k, hk⟩ : (n : ℤ) ∣ a - b := (Int.ModEq.dvd h.symm)
    have ha : a = b + (n : ℤ) * k := by omega
    rw [ha, addPhase_add, addPhase_period hn.ne' k, mul_one]

/-- **`addPhase_split`.**  `LEAN_PROVED`.  Exact coprime-modulus splitting of the phase:
`e_{m n}(b n + c m) = e_m(b) · e_n(c)`.  (No coprimality is needed for this identity itself;
coprimality is what makes the *decomposition of a given numerator* possible.) -/
theorem addPhase_split {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (b c : ℤ) :
    addPhase (m * n) (b * (n : ℤ) + c * (m : ℤ)) = addPhase m b * addPhase n c := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [addPhase, addPhase, addPhase, ← Complex.exp_add]
  congr 1
  have hreal : ((b * (n : ℤ) + c * (m : ℤ) : ℤ) : ℝ) / ((m * n : ℕ) : ℝ)
      = (b : ℝ) / (m : ℝ) + (c : ℝ) / (n : ℝ) := by
    push_cast
    field_simp
  rw [show ((2 * Real.pi * (((b * (n : ℤ) + c * (m : ℤ) : ℤ) : ℝ) / ((m * n : ℕ) : ℝ)) : ℝ) : ℂ)
      = ((2 * Real.pi * ((b : ℝ) / (m : ℝ) + (c : ℝ) / (n : ℝ)) : ℝ) : ℂ) by rw [hreal]]
  push_cast
  ring

/-! ## §3  The dual CRT split -/

/-- **`transverseDualCRT_split_int`.**  `LEAN_PROVED`.  The exact integer form of the dual CRT
split.  With `m`, `r₀` coprime, `γ ≡ c_m (mod m)`, `γ ≡ d_ℓ (mod r₀)` and supplied inverses

* `q · qinv ≡ 1 (mod m r₀)`,
* `(q r₀) · w ≡ 1 (mod m)`,
* `(m q) · z ≡ 1 (mod r₀)`,

one has `Δ γ qinv ≡ (Δ c_m w) r₀ + (Δ d_ℓ z) m  (mod m r₀)`. -/
theorem transverseDualCRT_split_int {m r0 : ℕ} (hco : Nat.Coprime m r0)
    {gamma cM dEll Delta q qinv w z : ℤ}
    (hgm : gamma ≡ cM [ZMOD (m : ℤ)]) (hgr : gamma ≡ dEll [ZMOD (r0 : ℤ)])
    (hqinv : q * qinv ≡ 1 [ZMOD ((m * r0 : ℕ) : ℤ)])
    (hw : (q * (r0 : ℤ)) * w ≡ 1 [ZMOD (m : ℤ)])
    (hz : ((m : ℤ) * q) * z ≡ 1 [ZMOD (r0 : ℤ)]) :
    Delta * gamma * qinv
      ≡ (Delta * cM * w) * (r0 : ℤ) + (Delta * dEll * z) * (m : ℤ) [ZMOD ((m * r0 : ℕ) : ℤ)] := by
  have hdm : (m : ℤ) ∣ ((m * r0 : ℕ) : ℤ) := ⟨(r0 : ℤ), by push_cast; ring⟩
  have hdr : (r0 : ℤ) ∣ ((m * r0 : ℕ) : ℤ) := ⟨(m : ℤ), by push_cast; ring⟩
  refine int_modEq_combine_coprime hco ?_ ?_
  · -- modulo `m`
    have hqm : q * qinv ≡ 1 [ZMOD (m : ℤ)] := Int.ModEq.of_dvd hdm hqinv
    have hqw : q * ((r0 : ℤ) * w) ≡ 1 [ZMOD (m : ℤ)] := by
      have : q * ((r0 : ℤ) * w) = (q * (r0 : ℤ)) * w := by ring
      rw [this]; exact hw
    have hinv : qinv ≡ (r0 : ℤ) * w [ZMOD (m : ℤ)] := int_inverse_unique hqm hqw
    have h1 : Delta * gamma * qinv ≡ Delta * cM * ((r0 : ℤ) * w) [ZMOD (m : ℤ)] := by
      calc Delta * gamma * qinv ≡ Delta * cM * qinv [ZMOD (m : ℤ)] :=
            (hgm.mul_left Delta).mul_right qinv
        _ ≡ Delta * cM * ((r0 : ℤ) * w) [ZMOD (m : ℤ)] := hinv.mul_left _
    have h2 : (Delta * dEll * z) * (m : ℤ) ≡ 0 [ZMOD (m : ℤ)] :=
      Int.modEq_zero_iff_dvd.mpr ⟨Delta * dEll * z, by ring⟩
    calc Delta * gamma * qinv ≡ Delta * cM * ((r0 : ℤ) * w) [ZMOD (m : ℤ)] := h1
      _ = (Delta * cM * w) * (r0 : ℤ) + 0 := by ring
      _ ≡ (Delta * cM * w) * (r0 : ℤ) + (Delta * dEll * z) * (m : ℤ) [ZMOD (m : ℤ)] :=
          (Int.ModEq.refl _).add h2.symm
  · -- modulo `r₀`
    have hqr : q * qinv ≡ 1 [ZMOD (r0 : ℤ)] := Int.ModEq.of_dvd hdr hqinv
    have hqz : q * ((m : ℤ) * z) ≡ 1 [ZMOD (r0 : ℤ)] := by
      have : q * ((m : ℤ) * z) = ((m : ℤ) * q) * z := by ring
      rw [this]; exact hz
    have hinv : qinv ≡ (m : ℤ) * z [ZMOD (r0 : ℤ)] := int_inverse_unique hqr hqz
    have h1 : Delta * gamma * qinv ≡ Delta * dEll * ((m : ℤ) * z) [ZMOD (r0 : ℤ)] := by
      calc Delta * gamma * qinv ≡ Delta * dEll * qinv [ZMOD (r0 : ℤ)] :=
            (hgr.mul_left Delta).mul_right qinv
        _ ≡ Delta * dEll * ((m : ℤ) * z) [ZMOD (r0 : ℤ)] := hinv.mul_left _
    have h2 : (Delta * cM * w) * (r0 : ℤ) ≡ 0 [ZMOD (r0 : ℤ)] :=
      Int.modEq_zero_iff_dvd.mpr ⟨Delta * cM * w, by ring⟩
    calc Delta * gamma * qinv ≡ Delta * dEll * ((m : ℤ) * z) [ZMOD (r0 : ℤ)] := h1
      _ = 0 + (Delta * dEll * z) * (m : ℤ) := by ring
      _ ≡ (Delta * cM * w) * (r0 : ℤ) + (Delta * dEll * z) * (m : ℤ) [ZMOD (r0 : ℤ)] :=
          h2.symm.add (Int.ModEq.refl _)

/-- **`transverseDualCRT_split`.**  `LEAN_PROVED`.  The dual CRT split at the level of phases:

`e_{m r₀}(Δ γ q⁻¹) = e_m(Δ c_m (q r₀)⁻¹) · e_{r₀}(Δ d_ℓ (m q)⁻¹)`,

with all inverses supplied as integers carrying their defining congruences. -/
theorem transverseDualCRT_split {m r0 : ℕ} (hm : m ≠ 0) (hr0 : r0 ≠ 0) (hco : Nat.Coprime m r0)
    {gamma cM dEll Delta q qinv w z : ℤ}
    (hgm : gamma ≡ cM [ZMOD (m : ℤ)]) (hgr : gamma ≡ dEll [ZMOD (r0 : ℤ)])
    (hqinv : q * qinv ≡ 1 [ZMOD ((m * r0 : ℕ) : ℤ)])
    (hw : (q * (r0 : ℤ)) * w ≡ 1 [ZMOD (m : ℤ)])
    (hz : ((m : ℤ) * q) * z ≡ 1 [ZMOD (r0 : ℤ)]) :
    addPhase (m * r0) (Delta * gamma * qinv)
      = addPhase m (Delta * cM * w) * addPhase r0 (Delta * dEll * z) := by
  rw [addPhase_congr (m * r0)
    (transverseDualCRT_split_int hco hgm hgr hqinv hw hz)]
  exact addPhase_split hm hr0 _ _

/-! ## §4  Additive reciprocity -/

/-- **`additiveReciprocity_coprime`.**  `LEAN_PROVED`.  The exact integer reciprocity identity:
for coprime `n`, `r₀` with supplied inverses `n z ≡ 1 (mod r₀)` and `r₀ y ≡ 1 (mod n)`,

`z n + y r₀ ≡ 1  (mod n r₀)`,

which is the integer form of `z/r₀ + y/n ≡ 1/(n r₀)  (mod 1)`. -/
theorem additiveReciprocity_coprime {n r0 : ℕ} (hco : Nat.Coprime n r0) {y z : ℤ}
    (hz : (n : ℤ) * z ≡ 1 [ZMOD (r0 : ℤ)]) (hy : (r0 : ℤ) * y ≡ 1 [ZMOD (n : ℤ)]) :
    z * (n : ℤ) + y * (r0 : ℤ) ≡ 1 [ZMOD ((n * r0 : ℕ) : ℤ)] := by
  refine int_modEq_combine_coprime hco ?_ ?_
  · have h0 : z * (n : ℤ) ≡ 0 [ZMOD (n : ℤ)] := Int.modEq_zero_iff_dvd.mpr ⟨z, by ring⟩
    calc z * (n : ℤ) + y * (r0 : ℤ) ≡ 0 + y * (r0 : ℤ) [ZMOD (n : ℤ)] :=
          h0.add (Int.ModEq.refl _)
      _ = (r0 : ℤ) * y := by ring
      _ ≡ 1 [ZMOD (n : ℤ)] := hy
  · have h0 : y * (r0 : ℤ) ≡ 0 [ZMOD (r0 : ℤ)] := Int.modEq_zero_iff_dvd.mpr ⟨y, by ring⟩
    calc z * (n : ℤ) + y * (r0 : ℤ) ≡ z * (n : ℤ) + 0 [ZMOD (r0 : ℤ)] :=
          (Int.ModEq.refl _).add h0
      _ = (n : ℤ) * z := by ring
      _ ≡ 1 [ZMOD (r0 : ℤ)] := hz

/-- **`additiveReciprocity_phase`.**  `LEAN_PROVED`.  Phase form of reciprocity: for every
integer amplitude `a`,

`e_{r₀}(a z) · e_n(a y) = e_{n r₀}(a)`.

The right-hand factor `e_{n r₀}(a)` is the *explicit* residual small phase; it is never called
harmless and never discarded. -/
theorem additiveReciprocity_phase {n r0 : ℕ} (hn : n ≠ 0) (hr0 : r0 ≠ 0)
    (hco : Nat.Coprime n r0) {y z : ℤ}
    (hz : (n : ℤ) * z ≡ 1 [ZMOD (r0 : ℤ)]) (hy : (r0 : ℤ) * y ≡ 1 [ZMOD (n : ℤ)]) (a : ℤ) :
    addPhase r0 (a * z) * addPhase n (a * y) = addPhase (n * r0) a := by
  have hcong : a * z * (n : ℤ) + a * y * (r0 : ℤ) ≡ a [ZMOD ((n * r0 : ℕ) : ℤ)] := by
    have := (additiveReciprocity_coprime hco hz hy).mul_left a
    calc a * z * (n : ℤ) + a * y * (r0 : ℤ)
        = a * (z * (n : ℤ) + y * (r0 : ℤ)) := by ring
      _ ≡ a * 1 [ZMOD ((n * r0 : ℕ) : ℤ)] := this
      _ = a := by ring
  calc addPhase r0 (a * z) * addPhase n (a * y)
      = addPhase n (a * y) * addPhase r0 (a * z) := by ring
    _ = addPhase (n * r0) ((a * y) * (r0 : ℤ) + (a * z) * (n : ℤ)) :=
        (addPhase_split hn hr0 _ _).symm
    _ = addPhase (n * r0) (a * z * (n : ℤ) + a * y * (r0 : ℤ)) := by ring_nf
    _ = addPhase (n * r0) a := addPhase_congr _ hcong

/-! ## §5  The dual normal form `C_{m q g}` and the affine coordinate `Ξ` -/

/-- The dual constant `C_{m q g} = q · (q⁻¹ mod m) · c_m`, an integer representative. -/
def Cmqg (q qInvM cM : ℤ) : ℤ := q * qInvM * cM

/-- **`Cmqg_mod_m`.**  `LEAN_PROVED`.  `C_{m q g} ≡ c_m (mod m)`. -/
theorem Cmqg_mod_m {m : ℕ} {q qInvM cM : ℤ} (h : q * qInvM ≡ 1 [ZMOD (m : ℤ)]) :
    Cmqg q qInvM cM ≡ cM [ZMOD (m : ℤ)] := by
  calc Cmqg q qInvM cM = cM * (q * qInvM) := by unfold Cmqg; ring
    _ ≡ cM * 1 [ZMOD (m : ℤ)] := h.mul_left cM
    _ = cM := by ring

/-- **`Cmqg_mod_q`.**  `LEAN_PROVED`.  `C_{m q g} ≡ 0 (mod q)`. -/
theorem Cmqg_mod_q (q qInvM cM : ℤ) : Cmqg q qInvM cM ≡ 0 [ZMOD q] :=
  Int.modEq_zero_iff_dvd.mpr ⟨qInvM * cM, by unfold Cmqg; ring⟩

/-- The dual affine coordinate `Ξ(ℓ) = C_{m q g} - k_g - A_m ℓ`, as an integer representative
(its class modulo `m q` is what the dual level uses). -/
def Xi (C kg Am : ℤ) (ell : ℤ) : ℤ := C - kg - Am * ell

/-- **`Xi_affine_slope`.**  `LEAN_PROVED`.  The exact affine slope of `Ξ`:
`Ξ(ℓ+1) - Ξ(ℓ) = -A_m`, as an integer identity, hence a fortiori modulo `m q`. -/
theorem Xi_affine_slope (C kg Am ell : ℤ) : Xi C kg Am (ell + 1) - Xi C kg Am ell = -Am := by
  unfold Xi; ring

/-- **`Xi_affine_slope_mod`.**  `LEAN_PROVED`.  The congruence form recorded in the research
note: `Ξ(ℓ+1) - Ξ(ℓ) ≡ -A_m (mod m q)`. -/
theorem Xi_affine_slope_mod (mq : ℕ) (C kg Am ell : ℤ) :
    Xi C kg Am (ell + 1) - Xi C kg Am ell ≡ -Am [ZMOD (mq : ℤ)] := by
  rw [Xi_affine_slope]

/-! ## §6  `DualReciprocityData` -/

/-- The dual-level reciprocity package.  The Archimedean factor `archDual` is an **explicit
parameter** with the single property that it has modulus one; no smooth analysis, no derivative
scale and no mass estimate is formalised, and none is claimed. -/
structure DualReciprocityData where
  /-- The `m`-component of the dual modulus. -/
  m : ℕ
  /-- The `q`-component of the dual modulus. -/
  q : ℕ
  /-- `0 < m`. -/
  m_pos : 0 < m
  /-- `0 < q`. -/
  q_pos : 0 < q
  /-- Supplied inverse of `q` modulo `m`. -/
  qInvM : ℤ
  /-- Its defining congruence. -/
  qInvM_spec : (q : ℤ) * qInvM ≡ 1 [ZMOD (m : ℤ)]
  /-- The `m`-component `c_m`. -/
  cM : ℤ
  /-- The constant of the `r₀`-component. -/
  kg : ℤ
  /-- The affine slope. -/
  Am : ℤ
  /-- The Archimedean dual factor: an explicit parameter. -/
  archDual : ℂ
  /-- Its only recorded property. -/
  archDual_norm : ‖archDual‖ = 1

namespace DualReciprocityData

variable (P : DualReciprocityData)

/-- The dual modulus `m q`. -/
def modulus : ℕ := P.m * P.q

/-- **`modulus_pos`.**  `LEAN_PROVED`. -/
theorem modulus_pos : 0 < P.modulus := Nat.mul_pos P.m_pos P.q_pos

/-- The dual constant of the packet. -/
def C : ℤ := Cmqg (P.q : ℤ) P.qInvM P.cM

/-- The dual affine coordinate of the packet. -/
def XiOf (ell : ℤ) : ℤ := Xi P.C P.kg P.Am ell

/-- **`C_mod_m`.**  `LEAN_PROVED`.  `C_{m q g} ≡ c_m (mod m)`. -/
theorem C_mod_m : P.C ≡ P.cM [ZMOD (P.m : ℤ)] := Cmqg_mod_m P.qInvM_spec

/-- **`C_mod_q`.**  `LEAN_PROVED`.  `C_{m q g} ≡ 0 (mod q)`. -/
theorem C_mod_q : P.C ≡ 0 [ZMOD (P.q : ℤ)] := Cmqg_mod_q _ _ _

/-- **`XiOf_affine_slope`.**  `LEAN_PROVED`.  The exact affine slope of the packet's `Ξ`. -/
theorem XiOf_affine_slope (ell : ℤ) : P.XiOf (ell + 1) - P.XiOf ell = -P.Am :=
  Xi_affine_slope _ _ _ _

end DualReciprocityData

/-- **`transverseDualLevelReciprocity`.**  `LEAN_PROVED`.  The dual-level reciprocity statement
in its safe form: the *arithmetic* character of the `r₀`-component equals the dual arithmetic
character times the explicit residual phase `e_{n r₀}(a)`, and the Archimedean parameter of the
packet contributes a factor of modulus one which is **not** analysed.

Concretely: `e_{r₀}(a z) · e_n(a y) = e_{n r₀}(a)`, and multiplying by `archDual` preserves
modulus. -/
theorem transverseDualLevelReciprocity (P : DualReciprocityData) {n r0 : ℕ} (hn : n ≠ 0)
    (hr0 : r0 ≠ 0) (hco : Nat.Coprime n r0) {y z : ℤ}
    (hz : (n : ℤ) * z ≡ 1 [ZMOD (r0 : ℤ)]) (hy : (r0 : ℤ) * y ≡ 1 [ZMOD (n : ℤ)]) (a : ℤ) :
    P.archDual * (addPhase r0 (a * z) * addPhase n (a * y))
        = P.archDual * addPhase (n * r0) a ∧
      ‖P.archDual * addPhase (n * r0) a‖ = 1 := by
  refine ⟨by rw [additiveReciprocity_phase hn hr0 hco hz hy a], ?_⟩
  rw [norm_mul, P.archDual_norm, addPhase_norm, one_mul]

/-- **`archDual_is_a_free_parameter`.**  `LEAN_PROVED`.  The Archimedean dual factor is genuinely
a parameter: for every modulus-one complex number there is a packet carrying it.  Hence no
theorem of this module can be read as determining, bounding or discharging it. -/
theorem archDual_is_a_free_parameter (w : ℂ) (hw : ‖w‖ = 1) :
    ∃ P : DualReciprocityData, P.archDual = w :=
  ⟨{ m := 1, q := 1, m_pos := one_pos, q_pos := one_pos, qInvM := 1
     qInvM_spec := by decide +kernel
     cM := 0, kg := 0, Am := 0, archDual := w, archDual_norm := hw }, rfl⟩

end TransverseDualLevel
end Erdos287
