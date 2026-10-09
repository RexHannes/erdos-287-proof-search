import Mathlib

/-!
# Erdős #287 — V100R4 source chain: general affine phase (exact CRT / phase algebra)

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

§7 of the request (message-level source; the V100R4 text was not supplied).  The physical
conditions are preserved literally:

  `n₁ ρ ≡ c (mod f)`,   `A n₁ ρ ≡ B (mod l)`,   `A n₂ ρ ≡ B (mod l)`.

`A` is **never cancelled modulo `f`** and `(A, f) = 1` is **never assumed**: the `f`-colour is
computed from `n₁ ρ ≡ c (f)` alone (unit hypothesis on `n₁` modulo `f`), and only the
`l`-condition uses an inverse of `A n₁` (modulo `l`).

* `IntDiff x y` — `x - y ∈ ℤ` (equality of phases modulo 1), over `ℚ`.
* `crt2_phase`, `crt3_phase` — partial fractions modulo 1 for pairwise coprime moduli with
  explicit inverses.
* `affine_phase_decomposition` — for pairwise coprime `f, l, w` (`w = uv`):
  `hρ/(flw) ≡ h c n̄₁ a_f / f  +  h B t a_l / l  +  hρ a_w / w   (mod 1)`
  (tiny-base colour, reciprocal factor, Archimedean/smooth factor), where
  `n₁ n̄₁ ≡ 1 (f)`, `(A n₁) t ≡ 1 (l)`, `lw·a_f ≡ 1 (f)`, `fw·a_l ≡ 1 (l)`, `fl·a_w ≡ 1 (w)`.
* `reciprocal_factor_n2` — the `n₂` condition gives the same reciprocal factor.
* `fixedLocal_split_phase` — `f = f₀ f₁` with `(f₀,f₁) = 1` splits the colour.
* `ePhase` / `ePhase_decomposition` — the multiplicative form
  `e_{flw}(hρ) = e_f(colour) · e_l(reciprocal) · e_w(Archimedean)`.
* `ph1_phase` / `ph1_ePhase` — **the supplied identity PH.1, verbatim**:
  `e_{fluv}(hρ) = e(Bh/(A n₁ fluv)) · e_{n₁v}(Bh(n₁-n₂)\overline{A f n₂ l u}) ·
  e_{Af}(h(Ac-B)\overline{l u n₁ v})` under `n₁ρ ≡ c (f)`, `A n₁ ρ ≡ B (lu)`, `A n₂ ρ ≡ B (v)`
  (no `(A,f) = 1`).  **No source mismatch.**
-/

open scoped BigOperators

namespace Erdos287.SourceChain

/-! ### Phases modulo 1 -/

/-- `x ≡ y (mod 1)`. -/
def IntDiff (x y : ℚ) : Prop := ∃ k : ℤ, x = y + k

theorem IntDiff.refl (x : ℚ) : IntDiff x x := ⟨0, by simp⟩

theorem IntDiff.symm {x y : ℚ} (h : IntDiff x y) : IntDiff y x := by
  obtain ⟨k, hk⟩ := h; exact ⟨-k, by push_cast; linarith⟩

theorem IntDiff.trans {x y z : ℚ} (h1 : IntDiff x y) (h2 : IntDiff y z) : IntDiff x z := by
  obtain ⟨k, hk⟩ := h1; obtain ⟨j, hj⟩ := h2; exact ⟨j + k, by push_cast; linarith⟩

theorem IntDiff.add {x y x' y' : ℚ} (h1 : IntDiff x y) (h2 : IntDiff x' y') :
    IntDiff (x + x') (y + y') := by
  obtain ⟨k, hk⟩ := h1; obtain ⟨j, hj⟩ := h2; exact ⟨k + j, by push_cast; linarith⟩

theorem intDiff_of_dvd {q : ℤ} (hq : q ≠ 0) {a b : ℤ} (h : q ∣ a - b) :
    IntDiff ((a : ℚ) / q) ((b : ℚ) / q) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have : (a : ℚ) = b + q * k := by
    have := congrArg (fun z : ℤ => (z : ℚ)) hk; push_cast at this; linarith
  rw [this]; field_simp

theorem intDiff_of_modEq {q : ℤ} (hq : q ≠ 0) {a b : ℤ} (h : a ≡ b [ZMOD q]) :
    IntDiff ((a : ℚ) / q) ((b : ℚ) / q) :=
  intDiff_of_dvd hq (Int.ModEq.dvd h.symm)

/-! ### CRT partial fractions modulo 1 -/

/-- Two coprime moduli. -/
theorem crt2_phase {q1 q2 : ℤ} (h1 : q1 ≠ 0) (h2 : q2 ≠ 0) (hc : IsCoprime q1 q2)
    {b1 b2 : ℤ} (hb1 : q2 * b1 ≡ 1 [ZMOD q1]) (hb2 : q1 * b2 ≡ 1 [ZMOD q2]) (x : ℤ) :
    IntDiff ((x : ℚ) / (q1 * q2)) (((x * b1 : ℤ) : ℚ) / q1 + ((x * b2 : ℤ) : ℚ) / q2) := by
  set N := x * b1 * q2 + x * b2 * q1
  have d1 : q1 ∣ x - N := by
    obtain ⟨k, hk⟩ := hb1.symm.dvd
    exact ⟨-(x * k) - x * b2, by simp only [N]; linear_combination (-x) * hk⟩
  have d2 : q2 ∣ x - N := by
    obtain ⟨k, hk⟩ := hb2.symm.dvd
    exact ⟨-(x * k) - x * b1, by simp only [N]; linear_combination (-x) * hk⟩
  have := intDiff_of_dvd (mul_ne_zero h1 h2) (IsCoprime.mul_dvd hc d1 d2)
  push_cast at this ⊢
  refine this.trans ⟨0, ?_⟩
  simp only [N]; push_cast
  field_simp
  ring

/-- Three pairwise coprime moduli. -/
theorem crt3_phase {f l w : ℤ} (hf : f ≠ 0) (hl : l ≠ 0) (hw : w ≠ 0)
    (hfl : IsCoprime f l) (hfw : IsCoprime f w) (hlw : IsCoprime l w)
    {af al aw : ℤ} (haf : l * w * af ≡ 1 [ZMOD f]) (hal : f * w * al ≡ 1 [ZMOD l])
    (haw : f * l * aw ≡ 1 [ZMOD w]) (x : ℤ) :
    IntDiff ((x : ℚ) / (f * l * w))
      (((x * af : ℤ) : ℚ) / f + ((x * al : ℤ) : ℚ) / l + ((x * aw : ℤ) : ℚ) / w) := by
  set N := x * af * (l * w) + x * al * (f * w) + x * aw * (f * l)
  have h1 : f ∣ x - N := by
    obtain ⟨k, hk⟩ := haf.symm.dvd
    exact ⟨-(x * k) - x * al * w - x * aw * l, by simp only [N]; linear_combination (-x) * hk⟩
  have h2 : l ∣ x - N := by
    obtain ⟨k, hk⟩ := hal.symm.dvd
    exact ⟨-(x * k) - x * af * w - x * aw * f, by simp only [N]; linear_combination (-x) * hk⟩
  have h3 : w ∣ x - N := by
    obtain ⟨k, hk⟩ := haw.symm.dvd
    exact ⟨-(x * k) - x * af * l - x * al * f, by simp only [N]; linear_combination (-x) * hk⟩
  have hall : f * l * w ∣ x - N :=
    IsCoprime.mul_dvd (IsCoprime.mul_left hfw hlw) (IsCoprime.mul_dvd hfl h1 h2) h3
  have := intDiff_of_dvd (mul_ne_zero (mul_ne_zero hf hl) hw) hall
  push_cast at this ⊢
  refine this.trans ⟨0, ?_⟩
  simp only [N]; push_cast
  field_simp
  ring

/-! ### Substituting the physical conditions -/

/-- Tiny-base colour from `n₁ ρ ≡ c (mod f)` and `n₁ n̄₁ ≡ 1 (mod f)` (no `A` involved). -/
theorem colour_subst {f n1 n1inv ρ c h a : ℤ} (hf : f ≠ 0) (hρ : n1 * ρ ≡ c [ZMOD f])
    (hinv : n1 * n1inv ≡ 1 [ZMOD f]) :
    IntDiff (((h * ρ * a : ℤ) : ℚ) / f) (((h * c * n1inv * a : ℤ) : ℚ) / f) := by
  refine intDiff_of_modEq hf ?_
  have hd : f ∣ c * n1inv - ρ := by
    obtain ⟨k1, hk1⟩ := hρ.dvd
    obtain ⟨k2, hk2⟩ := hinv.dvd
    exact ⟨n1inv * k1 - ρ * k2, by linear_combination n1inv * hk1 - ρ * hk2⟩
  have : ρ ≡ c * n1inv [ZMOD f] := Int.modEq_of_dvd hd
  calc h * ρ * a = h * a * ρ := by ring
    _ ≡ h * a * (c * n1inv) [ZMOD f] := this.mul_left _
    _ = h * c * n1inv * a := by ring

/-- Reciprocal factor from `A n₁ ρ ≡ B (mod l)` and `(A n₁) t ≡ 1 (mod l)`. -/
theorem reciprocal_subst {l A n1 t ρ B h a : ℤ} (hl : l ≠ 0) (hρ : A * n1 * ρ ≡ B [ZMOD l])
    (hinv : (A * n1) * t ≡ 1 [ZMOD l]) :
    IntDiff (((h * ρ * a : ℤ) : ℚ) / l) (((h * B * t * a : ℤ) : ℚ) / l) :=
  colour_subst (n1 := A * n1) (c := B) hl (by simpa [mul_assoc] using hρ) hinv

/-- **General affine phase decomposition.**  For pairwise coprime `f, l, w`:
`hρ/(flw) ≡ h c n̄₁ a_f/f + h B t a_l/l + hρ a_w/w (mod 1)`. -/
theorem affine_phase_decomposition {f l w : ℤ} (hf : f ≠ 0) (hl : l ≠ 0) (hw : w ≠ 0)
    (hfl : IsCoprime f l) (hfw : IsCoprime f w) (hlw : IsCoprime l w)
    {af al aw : ℤ} (haf : l * w * af ≡ 1 [ZMOD f]) (hal : f * w * al ≡ 1 [ZMOD l])
    (haw : f * l * aw ≡ 1 [ZMOD w])
    {A B c n1 n1inv t ρ h : ℤ}
    (hcol : n1 * ρ ≡ c [ZMOD f]) (hn1 : n1 * n1inv ≡ 1 [ZMOD f])
    (hrec : A * n1 * ρ ≡ B [ZMOD l]) (ht : (A * n1) * t ≡ 1 [ZMOD l]) :
    IntDiff (((h * ρ : ℤ) : ℚ) / (f * l * w))
      (((h * c * n1inv * af : ℤ) : ℚ) / f + ((h * B * t * al : ℤ) : ℚ) / l +
        ((h * ρ * aw : ℤ) : ℚ) / w) := by
  refine (crt3_phase hf hl hw hfl hfw hlw haf hal haw (h * ρ)).trans ?_
  exact ((colour_subst hf hcol hn1).add (reciprocal_subst hl hrec ht)).add (IntDiff.refl _)

/-- The second physical condition `A n₂ ρ ≡ B (mod l)` produces the same reciprocal factor. -/
theorem reciprocal_factor_n2 {l A n2 t2 ρ B h a : ℤ} (hl : l ≠ 0)
    (hρ2 : A * n2 * ρ ≡ B [ZMOD l]) (ht2 : (A * n2) * t2 ≡ 1 [ZMOD l]) :
    IntDiff (((h * ρ * a : ℤ) : ℚ) / l) (((h * B * t2 * a : ℤ) : ℚ) / l) :=
  reciprocal_subst hl hρ2 ht2

/-- **Fixed-local split** `f = f₀ f₁`, `(f₀, f₁) = 1`, of the tiny-base colour. -/
theorem fixedLocal_split_phase {f0 f1 : ℤ} (h0 : f0 ≠ 0) (h1 : f1 ≠ 0) (hc : IsCoprime f0 f1)
    {b0 b1 : ℤ} (hb0 : f1 * b0 ≡ 1 [ZMOD f0]) (hb1 : f0 * b1 ≡ 1 [ZMOD f1]) (y : ℤ) :
    IntDiff ((y : ℚ) / (f0 * f1)) (((y * b0 : ℤ) : ℚ) / f0 + ((y * b1 : ℤ) : ℚ) / f1) :=
  crt2_phase h0 h1 hc hb0 hb1 y

/-! ### Multiplicative form -/

/-- `e(x) = exp(2πi x)`. -/
noncomputable def ePhase (x : ℚ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

theorem ePhase_add (x y : ℚ) : ePhase (x + y) = ePhase x * ePhase y := by
  unfold ePhase; rw [← Complex.exp_add]; push_cast; ring_nf

theorem ePhase_intDiff {x y : ℚ} (h : IntDiff x y) : ePhase x = ePhase y := by
  obtain ⟨k, rfl⟩ := h
  rw [ePhase_add]
  have : ePhase (k : ℚ) = 1 := by
    unfold ePhase
    rw [show (2 * Real.pi * Complex.I * (((k : ℚ) : ℂ)) : ℂ) = k * (2 * Real.pi * Complex.I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I k
  rw [this, mul_one]

/-- **`e_{flw}(hρ)` = colour · reciprocal · Archimedean.** -/
theorem ePhase_decomposition {f l w : ℤ} (hf : f ≠ 0) (hl : l ≠ 0) (hw : w ≠ 0)
    (hfl : IsCoprime f l) (hfw : IsCoprime f w) (hlw : IsCoprime l w)
    {af al aw : ℤ} (haf : l * w * af ≡ 1 [ZMOD f]) (hal : f * w * al ≡ 1 [ZMOD l])
    (haw : f * l * aw ≡ 1 [ZMOD w])
    {A B c n1 n1inv t ρ h : ℤ}
    (hcol : n1 * ρ ≡ c [ZMOD f]) (hn1 : n1 * n1inv ≡ 1 [ZMOD f])
    (hrec : A * n1 * ρ ≡ B [ZMOD l]) (ht : (A * n1) * t ≡ 1 [ZMOD l]) :
    ePhase (((h * ρ : ℤ) : ℚ) / (f * l * w)) =
      ePhase (((h * c * n1inv * af : ℤ) : ℚ) / f) * ePhase (((h * B * t * al : ℤ) : ℚ) / l) *
        ePhase (((h * ρ * aw : ℤ) : ℚ) / w) := by
  rw [ePhase_intDiff (affine_phase_decomposition hf hl hw hfl hfw hlw haf hal haw hcol hn1
    hrec ht), ePhase_add, ePhase_add]

/-! ### The supplied phase identity (PH.1) — exact reciprocity form -/

/-- **PH.1 (message-level source pack, §16), kernel-proved.**  Under the clean CRT conditions
`n₁ρ ≡ c (f)`, `A n₁ ρ ≡ B (lu)`, `A n₂ ρ ≡ B (v)` and the explicit inverses
`s · (A f n₂ l u) ≡ 1 (mod n₁ v)`, `t · (l u n₁ v) ≡ 1 (mod A f)`:

`hρ/(fluv) ≡ Bh/(A n₁ fluv) + Bh(n₁-n₂) s/(n₁ v) + h(Ac-B) t/(Af)   (mod 1)`,

i.e. `e_{fluv}(hρ) = e(Bh/(A n₁ fluv)) · e_{n₁v}(Bh(n₁-n₂)\overline{A f n₂ l u}) ·
e_{Af}(h(Ac-B)\overline{l u n₁ v})`.  `(A, f) = 1` is **not** assumed and `A` is not cancelled
modulo `f` (the colour lives modulo `Af`).  The coprimality `(Af, n₁v) = 1` and
`(n₂lu, n₁v) = 1` needed for the inverses are *consequences* of the inverse hypotheses. -/
theorem ph1_phase {f l u v A B c n1 n2 ρ h s t : ℤ}
    (hf : f ≠ 0) (hl : l ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (hA : A ≠ 0) (hn1 : n1 ≠ 0)
    (c1 : n1 * ρ ≡ c [ZMOD f]) (c2 : A * n1 * ρ ≡ B [ZMOD l * u])
    (c3 : A * n2 * ρ ≡ B [ZMOD v])
    (hs : (A * f * n2 * l * u) * s ≡ 1 [ZMOD n1 * v])
    (ht : (l * u * n1 * v) * t ≡ 1 [ZMOD A * f]) :
    IntDiff (((h * ρ : ℤ) : ℚ) / (f * l * u * v))
      (((B * h : ℤ) : ℚ) / (A * n1 * f * l * u * v) +
        ((B * h * (n1 - n2) * s : ℤ) : ℚ) / (n1 * v) +
        ((h * (A * c - B) * t : ℤ) : ℚ) / (A * f)) := by
  obtain ⟨Y', hY⟩ := c2.symm.dvd
  obtain ⟨k1, hk1⟩ := ht.symm.dvd
  obtain ⟨k2, hk2⟩ := c1.dvd
  obtain ⟨k3, hk3⟩ := hs.symm.dvd
  obtain ⟨k4, hk4⟩ := c3.dvd
  set Z := Y' - B * (n1 - n2) * s * (A * f) - (A * c - B) * t * (n1 * v) with hZ
  have hAf : A * f ∣ Z := ⟨-(Y' * k1) - B * (n1 - n2) * s - k2 * t * n1 * v, by
    rw [hZ]; linear_combination (-(t * n1 * v)) * hY - Y' * hk1 - (A * t * n1 * v) * hk2⟩
  have hcop1 : IsCoprime (n2 * l * u) (n1 * v) := ⟨A * f * s, -k3, by linear_combination hk3⟩
  have hcop2 : IsCoprime (A * f) (n1 * v) := ⟨-k1, l * u * t, by linear_combination hk1⟩
  have hnv' : n1 * v ∣ (n2 * l * u) * Z := ⟨-k4 - B * (n1 - n2) * k3 -
      n2 * l * u * (A * c - B) * t, by
    rw [hZ]; linear_combination (-n2) * hY + (-(B * (n1 - n2))) * hk3 + (-n1) * hk4⟩
  have hnv : n1 * v ∣ Z := hcop1.symm.dvd_of_dvd_mul_left hnv'
  obtain ⟨W, hW⟩ := IsCoprime.mul_dvd hcop2 hAf hnv
  refine ⟨h * W, ?_⟩
  have hf' : (f : ℚ) ≠ 0 := by exact_mod_cast hf
  have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl
  have hu' : (u : ℚ) ≠ 0 := by exact_mod_cast hu
  have hv' : (v : ℚ) ≠ 0 := by exact_mod_cast hv
  have hA' : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  have hn1' : (n1 : ℚ) ≠ 0 := by exact_mod_cast hn1
  have hY'q : (Y' : ℚ) = A * f * (n1 * v) * W + B * (n1 - n2) * s * (A * f) +
      (A * c - B) * t * (n1 * v) := by
    have : ((Y' : ℤ) : ℚ) - B * (n1 - n2) * s * (A * f) - (A * c - B) * t * (n1 * v) =
        A * f * (n1 * v) * W := by exact_mod_cast hZ.symm.trans hW
    linarith
  have hρq : (ρ : ℚ) = (B + l * u * Y') / (A * n1) := by
    have : (A : ℚ) * n1 * ρ - B = l * u * Y' := by exact_mod_cast hY
    field_simp; linarith
  push_cast
  rw [hρq, hY'q]
  field_simp
  ring

/-- **PH.1, multiplicative form**: smooth factor × reciprocal (Kloosterman-type) factor ×
tiny-base colour. -/
theorem ph1_ePhase {f l u v A B c n1 n2 ρ h s t : ℤ}
    (hf : f ≠ 0) (hl : l ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (hA : A ≠ 0) (hn1 : n1 ≠ 0)
    (c1 : n1 * ρ ≡ c [ZMOD f]) (c2 : A * n1 * ρ ≡ B [ZMOD l * u])
    (c3 : A * n2 * ρ ≡ B [ZMOD v])
    (hs : (A * f * n2 * l * u) * s ≡ 1 [ZMOD n1 * v])
    (ht : (l * u * n1 * v) * t ≡ 1 [ZMOD A * f]) :
    ePhase (((h * ρ : ℤ) : ℚ) / (f * l * u * v)) =
      ePhase (((B * h : ℤ) : ℚ) / (A * n1 * f * l * u * v)) *
        ePhase (((B * h * (n1 - n2) * s : ℤ) : ℚ) / (n1 * v)) *
        ePhase (((h * (A * c - B) * t : ℤ) : ℚ) / (A * f)) := by
  rw [ePhase_intDiff (ph1_phase hf hl hu hv hA hn1 c1 c2 c3 hs ht), ePhase_add, ePhase_add]

end Erdos287.SourceChain
