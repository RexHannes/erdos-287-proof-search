import RequestProject.Erdos287.ResearchBankV18.ReciprocalMonomial

/-!
# Erdős #287 — Research Bank V18 §2: the scalar-variation bound `∑ |C_λ| ≤ E^{2/3}`

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Formulation without real powers: `(∑ |C_λ|)^3 ≤ E^2`.

Route: local prime factors; principal term; nonprincipal characters; explicit local variation

    M_p = (1 + (p − 2)√p) / (p − 1);

prove `M_p^3 ≤ p^2`; multiply over squarefree `E`.

Kernel-proved (LEAN BANK unless marked):
* `principal_sum` — the Ramanujan sum `∑_{a unit} e_p(c · a⁻¹) = −1` for `p ∤ c`, from Mathlib's
  primitive additive character `ZMod.stdAddChar` (no provider);
* `principal_coef_norm` — `‖C_1‖ = 1/(p − 1)`;
* `Mp_le_sqrt`, `Mp_sq_le`, **`Mp_cube_le`** — `M_p ≤ √p`, `M_p² ≤ p`, `M_p³ ≤ p²` for every
  `p ≥ 2` (no floating point; `p = 2` gives `M_2 = 1` exactly, `Mp_two`);
* **`local_variation_le`** (LEAN CONDITIONAL on `GaussMagnitudeProvider`) — the local scalar
  variation of the reciprocal phase mod `p` is `≤ M_p`, hence its cube is `≤ p²`;
* `crt_phase_split` — `e_{D₁D₂}(x) = e_{D₁}(x w) · e_{D₂}(x u)` whenever `u D₁ + w D₂ = 1`
  (the CRT factorization of the phase over coprime moduli);
* `prod_Mp_cube_le` — `(∏_{p∈S} M_p)^3 ≤ (∏_{p∈S} p)^2 = E^2` for a squarefree `E = ∏_{p∈S} p`.

`GaussMagnitudeProvider p c` isolates ONLY the Gauss-sum magnitude
`‖C_χ‖ ≤ √p/(p − 1)` for nonprincipal `χ` (Mathlib has `gaussSum_mul_gaussSum_eq_card` but no
norm form); it is an explicit hypothesis, never an axiom.
The identification of the character family mod `E` with the tensor product of the local families
is NOT formalized here (only the CRT phase split and the numerical product are).
-/

namespace Erdos287
namespace ResearchBankV18
namespace ScalarVariation

open ColourConductor CharacterExpansion ReciprocalMonomial

/-- The explicit local variation `M_p = (1 + (p − 2)√p)/(p − 1)`. -/
noncomputable def Mp (p : ℕ) : ℝ := (1 + ((p : ℝ) - 2) * Real.sqrt p) / ((p : ℝ) - 1)

theorem Mp_two : Mp 2 = 1 := by unfold Mp; norm_num

theorem Mp_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ Mp p := by
  have h : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold Mp
  apply div_nonneg _ (by linarith)
  have := Real.sqrt_nonneg (p : ℝ)
  nlinarith

/-- `M_p ≤ √p`. -/
theorem Mp_le_sqrt {p : ℕ} (hp : 2 ≤ p) : Mp p ≤ Real.sqrt p := by
  have h : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hs : 1 ≤ Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  unfold Mp
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem Mp_sq_le {p : ℕ} (hp : 2 ≤ p) : Mp p ^ 2 ≤ p := by
  have h1 := Mp_le_sqrt hp
  have h0 := Mp_nonneg hp
  calc Mp p ^ 2 ≤ Real.sqrt p ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = p := Real.sq_sqrt (by positivity)

/-- **`M_p³ ≤ p²`** for every `p ≥ 2`. -/
theorem Mp_cube_le {p : ℕ} (hp : 2 ≤ p) : Mp p ^ 3 ≤ (p : ℝ) ^ 2 := by
  have h : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 := Mp_le_sqrt hp
  have h0 := Mp_nonneg hp
  have h2 := Mp_sq_le hp
  have hsq : Real.sqrt p ≤ p := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  calc Mp p ^ 3 = Mp p ^ 2 * Mp p := by ring
    _ ≤ p * Real.sqrt p := mul_le_mul h2 h1 h0 (by linarith)
    _ ≤ p * p := mul_le_mul_of_nonneg_left hsq (by linarith)
    _ = (p : ℝ) ^ 2 := by ring

/-- **Product over a squarefree modulus**: `(∏ M_p)^3 ≤ (∏ p)^2`. -/
theorem prod_Mp_cube_le (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    (∏ p ∈ S, Mp p) ^ 3 ≤ ((∏ p ∈ S, p : ℕ) : ℝ) ^ 2 := by
  rw [← Finset.prod_pow, Nat.cast_prod, ← Finset.prod_pow]
  exact Finset.prod_le_prod (fun p hp => pow_nonneg (Mp_nonneg (hS p hp)) 3)
    fun p hp => Mp_cube_le (hS p hp)

/-- **CRT phase split** over coprime moduli. -/
theorem crt_phase_split {D₁ D₂ : ℕ} (h₁ : 0 < D₁) (h₂ : 0 < D₂) {u w : ℤ}
    (hB : u * D₁ + w * D₂ = 1) (x : ℤ) :
    e (D₁ * D₂) x = e D₁ (x * w) * e D₂ (x * u) := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  have h1 : (D₁ : ℂ) ≠ 0 := by exact_mod_cast h₁.ne'
  have h2 : (D₂ : ℂ) ≠ 0 := by exact_mod_cast h₂.ne'
  have hB' : (u : ℂ) * D₁ + (w : ℂ) * D₂ = 1 := by exact_mod_cast hB
  push_cast
  field_simp
  linear_combination -(x : ℂ) * hB'

section Prime

variable {p : ℕ} [Fact p.Prime]

theorem sum_units_eq (f : ZMod p → ℂ) :
    ∑ a : (ZMod p)ˣ, f a = ∑ x : ZMod p, f x - f 0 := by
  rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ 0), add_sub_cancel_right]
  rw [Finset.sum_subtype (Finset.univ.erase 0) (p := fun x : ZMod p => x ≠ 0)
    (fun x => by simp)]
  exact Fintype.sum_equiv unitsEquivNeZero _ _ fun a => rfl

theorem stdAddChar_eq_e (j : ZMod p) : (ZMod.stdAddChar j : ℂ) = e p (j.val : ℤ) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]; unfold e; push_cast; ring_nf

/-- **The principal (Ramanujan) sum**: `∑_{a unit} e_p(c · rep(a⁻¹)) = −1` for `p ∤ c`. -/
theorem principal_sum {c : ℤ} (hc : ¬ (p : ℤ) ∣ c) :
    ∑ a : (ZMod p)ˣ, recipPhase p c 1 a = -1 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  unfold recipPhase
  rw [← Equiv.sum_comp (Equiv.inv (ZMod p)ˣ)]
  simp only [Equiv.inv_apply, inv_inv, one_mul]
  rw [sum_units_eq (fun x : ZMod p => e p (c * (x.val : ℤ)))]
  have hc' : (c : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hsum : ∑ x : ZMod p, e p (c * (x.val : ℤ)) = 0 := by
    have h := AddChar.sum_mulShift (c : ZMod p) (ZMod.isPrimitive_stdAddChar p)
    rw [if_neg hc', Nat.cast_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [stdAddChar_eq_e]
    apply e_congr hp
    have h1 := val_mul_modEq x (c : ZMod p)
    have h2 : (((c : ZMod p).val : ℕ) : ℤ) ≡ c [ZMOD p] := by
      rw [ZMod.val_intCast]; exact Int.mod_modEq c p
    calc c * (x.val : ℤ) = (x.val : ℤ) * c := by ring
      _ ≡ (x.val : ℤ) * (((c : ZMod p).val : ℕ) : ℤ) [ZMOD p] := Int.ModEq.mul_left _ h2.symm
      _ ≡ (((x * (c : ZMod p)).val : ℕ) : ℤ) [ZMOD p] := h1.symm
  rw [hsum]
  simp [e]

theorem totient_real : ((p.totient : ℕ) : ℝ) = (p : ℝ) - 1 := by
  rw [Nat.totient_prime Fact.out, Nat.cast_sub (Fact.out : p.Prime).one_le]; simp

/-- **`‖C_1‖ = 1/(p − 1)`** for the principal character. -/
theorem principal_coef_norm {c : ℤ} (hc : ¬ (p : ℤ) ∣ c) :
    ‖coef (recipPhase p c 1) (1 : DirichletCharacter ℂ p)‖ = 1 / ((p : ℝ) - 1) := by
  unfold coef
  have : ∑ a : (ZMod p)ˣ, recipPhase p c 1 a * (1 : DirichletCharacter ℂ p) ((a : ZMod p)⁻¹) =
      ∑ a : (ZMod p)ˣ, recipPhase p c 1 a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ZMod.inv_coe_unit, MulChar.one_apply_coe, mul_one]
  rw [this, principal_sum hc, norm_mul, norm_neg, norm_one, mul_one, norm_inv]
  rw [show ‖((p.totient : ℕ) : ℂ)‖ = ((p.totient : ℕ) : ℝ) from by
    rw [Complex.norm_natCast]]
  rw [totient_real, one_div]

/-- **The Gauss-magnitude provider** (EXTERNAL PROVIDER; the only analytic input of V18.2). -/
structure GaussMagnitudeProvider (p : ℕ) [Fact p.Prime] (c : ℤ) : Prop where
  nonprincipal : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
    ‖coef (recipPhase p c 1) χ‖ ≤ Real.sqrt p / ((p : ℝ) - 1)

theorem card_characters :
    (Finset.univ : Finset (DirichletCharacter ℂ p)).card = p - 1 := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity, Nat.totient_prime Fact.out]

/-- **Local scalar variation** (conditional on the Gauss-magnitude provider). -/
theorem local_variation_le {c : ℤ} (hc : ¬ (p : ℤ) ∣ c) (G : GaussMagnitudeProvider p c) :
    variation (recipPhase p c 1) ≤ Mp p ∧ variation (recipPhase p c 1) ^ 3 ≤ (p : ℝ) ^ 2 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hv : variation (recipPhase p c 1) ≤ Mp p := by
    unfold variation
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ p)),
      principal_coef_norm hc]
    have hrest : ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ p),
        ‖coef (recipPhase p c 1) χ‖ ≤
        ((p : ℝ) - 2) * (Real.sqrt p / ((p : ℝ) - 1)) := by
      calc ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ p), ‖coef (recipPhase p c 1) χ‖
          ≤ ∑ _χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ p),
              Real.sqrt p / ((p : ℝ) - 1) :=
            Finset.sum_le_sum fun χ hχ => G.nonprincipal χ (Finset.ne_of_mem_erase hχ)
        _ = ((p : ℝ) - 2) * (Real.sqrt p / ((p : ℝ) - 1)) := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), card_characters,
              nsmul_eq_mul]
            congr 1
            rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    have : 1 / ((p : ℝ) - 1) + ((p : ℝ) - 2) * (Real.sqrt p / ((p : ℝ) - 1)) = Mp p := by
      unfold Mp; field_simp
    linarith
  refine ⟨hv, ?_⟩
  have h0 : 0 ≤ variation (recipPhase p c 1) :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  exact (pow_le_pow_left₀ h0 hv 3).trans (Mp_cube_le hp2)

end Prime

end ScalarVariation
end ResearchBankV18
end Erdos287
