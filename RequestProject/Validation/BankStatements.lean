import RequestProject.Audit.BankStatus

/-!
# External validation package

For an independent Lean comparator/checker: every important banked theorem is **re-stated
here from scratch, in unfolded form**, and discharged by the banked declaration.  The
statements below are written independently of the bank's own definitions (`lin`, `det`,
`kloostermanLike`, `zeroSet`, `J`, …), so if a bank definition were ever weakened or a
statement silently changed, these `example`s would stop compiling.

Nothing here is a new mathematical result; this file is a *statement audit*.
-/

open scoped BigOperators

namespace Validation

/-! ## Bank A — fixed-affine normal form -/

example {R : Type*} [CommRing R] (a₁ b₁ a₂ b₂ n : R) :
    a₁ * (a₂ * n + b₂) = a₂ * (a₁ * n + b₁) + (a₁ * b₂ - a₂ * b₁) :=
  TrustedBank.FixedAffine.affine_cross_identity a₁ b₁ a₂ b₂ n

example {K : Type*} [Field K] {a₁ b₁ a₂ b₂ n m : K} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hm : m = a₁ * n + b₁) :
    a₂ * n + b₂ = 0 ↔ m = -(a₁ * b₂ - a₂ * b₁) / a₂ :=
  TrustedBank.FixedAffine.second_root_iff ha₁ ha₂ hm

example {K : Type*} [Field K] {a₁ b₁ a₂ b₂ : K} (ha₂ : a₂ ≠ 0)
    (hΔ : a₁ * b₂ - a₂ * b₁ ≠ 0) :
    (fun x : K => -(a₂ / (a₁ * b₂ - a₂ * b₁)) * x) ''
        ({0, -(a₁ * b₂ - a₂ * b₁) / a₂} : Set K) = ({0, 1} : Set K) :=
  TrustedBank.FixedAffine.normUnit_image_roots ha₂ hΔ

/-! ## Bank B — unit / finite-sum transport -/

example {R : Type*} [Monoid R] (u : Rˣ) : Function.Bijective (fun x : R => (u : R) * x) :=
  TrustedBank.UnitTransport.unitMul_bijective u

example {R : Type*} [MonoidWithZero R] (u : Rˣ) (x : R) : (u : R) * x = 0 ↔ x = 0 :=
  TrustedBank.UnitTransport.unitMul_eq_zero_iff u x

example {I : Type*} [Fintype I] {E : Type*} [NormedAddCommGroup E] (e : Equiv.Perm I)
    (f : I → E) : ∑ i, ‖f (e i)‖ ^ 2 = ∑ i, ‖f i‖ ^ 2 :=
  TrustedBank.UnitTransport.l2_energy_perm e f

example {q : ℕ} [NeZero q] (ψ : ZMod q → ℂ) (A B : ZMod q) (lam : (ZMod q)ˣ) :
    (∑ x : (ZMod q)ˣ, ψ (A * ((x⁻¹ : (ZMod q)ˣ) : ZMod q) + B * (x : ZMod q)))
      = ∑ x : (ZMod q)ˣ, ψ (A * (lam : ZMod q) * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)
          + B * ((lam⁻¹ : (ZMod q)ˣ) : ZMod q) * (x : ZMod q)) :=
  TrustedBank.UnitTransport.kloostermanLike_unit_change ψ A B lam

/-! ## Bank C — fixed-unit portability of the simultaneous zero set -/

example {I : Type*} [Fintype I] {R₁ R₂ : Type*} [MonoidWithZero R₁] [MonoidWithZero R₂]
    (F₁ : I → R₁) (F₂ : I → R₂) (κ₁ : R₁ˣ) (κ₂ : R₂ˣ) (i : I) :
    ((κ₁ : R₁) * F₁ i = 0 ∧ (κ₂ : R₂) * F₂ i = 0) ↔ (F₁ i = 0 ∧ F₂ i = 0) :=
  TrustedBank.ZeroSetTransport.twist_simultaneous_zero_iff F₁ F₂ κ₁ κ₂ i

example (n p q : ℕ) [NeZero p] [NeZero q] (F₁ : Fin n → ZMod p) (F₂ : Fin n → ZMod q)
    (κ₁ : (ZMod p)ˣ) (κ₂ : (ZMod q)ˣ) :
    (Finset.univ.filter
        (fun i => (κ₁ : ZMod p) * F₁ i = 0 ∧ (κ₂ : ZMod q) * F₂ i = 0)).card
      = (Finset.univ.filter (fun i => F₁ i = 0 ∧ F₂ i = 0)).card :=
  TrustedBank.ZeroSetTransport.twist_zeroSet_card_eq F₁ F₂ κ₁ κ₂

/-! ## Bank D — Bézout parametrisation -/

example (B : TrustedBank.BoundedCofactor.Bez) (n : ℤ) :
    B.e * (B.d * n + B.v) - B.d * (B.e * n + B.u) = 1 :=
  B.key_identity n

example (B : TrustedBank.BoundedCofactor.Bez) (n : ℤ) :
    B.d * (B.e * n + B.u) + 1 = B.e * (B.d * n + B.v) :=
  B.dP_add_one n

example (B : TrustedBank.BoundedCofactor.Bez) :
    Int.gcd B.d B.e = 1 ∧ Int.gcd B.u B.e = 1 ∧ Int.gcd B.v B.d = 1 :=
  ⟨B.gcd_d_e, B.gcd_u_e, B.gcd_v_d⟩

/-! ## Bank E — local admissibility -/

example (B : TrustedBank.BoundedCofactor.Bez) :
    (∀ p : ℕ, p.Prime → ∃ n : ℤ,
        ¬ ((p : ℤ) ∣ B.e * n + B.u) ∧ ¬ ((p : ℤ) ∣ B.d * n + B.v))
      ↔ (2 : ℤ) ∣ B.d * B.e :=
  B.admissible_iff

/-! ## Bank F — local singular factors -/

example (B : TrustedBank.BoundedCofactor.Bez) (l : ℕ) [Fact (Nat.Prime l)]
    (h : (l : ℤ) ∣ B.d * B.e) :
    (Finset.univ.filter (fun n : ZMod l =>
        (B.e : ZMod l) * n + (B.u : ZMod l) = 0 ∨
        (B.d : ZMod l) * n + (B.v : ZMod l) = 0)).card = 1 :=
  TrustedBank.SingularFactors.nu_eq_one B l h

example (B : TrustedBank.BoundedCofactor.Bez) (l : ℕ) [Fact (Nat.Prime l)]
    (h : ¬ ((l : ℤ) ∣ B.d * B.e)) :
    (Finset.univ.filter (fun n : ZMod l =>
        (B.e : ZMod l) * n + (B.u : ZMod l) = 0 ∨
        (B.d : ZMod l) * n + (B.v : ZMod l) = 0)).card = 2 :=
  TrustedBank.SingularFactors.nu_eq_two B l h

example {l : ℚ} (hl : 3 ≤ l) :
    (1 - 1 / l) / (1 - 1 / l) ^ 2 = ((l - 1) / (l - 2)) * ((1 - 2 / l) / (1 - 1 / l) ^ 2) :=
  TrustedBank.SingularFactors.localFactor_ratio hl

/-! ## Bank G — cofactor intensity optimality -/

example {n : ℕ} (hn : 2 ∣ n) (hpos : 0 < n) :
    (1 / (n : ℚ)) * ∏ p ∈ n.primeFactors.filter (fun p => p ≠ 2),
        (((p : ℚ) - 1) / ((p : ℚ) - 2)) ≤ 1 / 2 :=
  TrustedBank.CofactorIntensity.J_le_half hn hpos

example {n : ℕ} (hn : 2 ∣ n) (hpos : 0 < n) (hne : n ≠ 2) :
    (1 / (n : ℚ)) * ∏ p ∈ n.primeFactors.filter (fun p => p ≠ 2),
        (((p : ℚ) - 1) / ((p : ℚ) - 2)) < 1 / 2 :=
  TrustedBank.CofactorIntensity.J_lt_half hn hpos hne

example (B : TrustedBank.BoundedCofactor.Bez) (h : B.d * B.e = 2) :
    (B.d = 1 ∧ B.e = 2) ∨ (B.d = 2 ∧ B.e = 1) :=
  TrustedBank.CofactorIntensity.de_eq_two B h

/-! ## Bank H — symmetric ± projection -/

example {R R' : Type*} [CommRing R] [CommRing R'] (χ : MulChar R R') (hχ : χ (-1) = -1) :
    χ 1 + χ (-1) = 0 :=
  TrustedBank.SymmetricPacket.odd_char_pair_cancel χ hχ

example {R R' : Type*} [CommRing R] [CommRing R'] (χ : MulChar R R') (hχ : χ (-1) = -1)
    (a : R) : χ a + χ (-a) = 0 :=
  TrustedBank.SymmetricPacket.odd_char_symm_pair χ hχ a

/-! ## Erdős #287 — carry tower -/

example (A : Finset ℕ) (hpos : ∀ a ∈ A, 0 < a) (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) :
    (A.lcm id) ^ 2 ∣ ∏ a ∈ A, a :=
  TrustedBank.CarryTower.lcm_sq_dvd_prod A hpos hsum

example (A : Finset ℕ) (hpos : ∀ a ∈ A, 0 < a) (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) :
    (A.lcm id) ∣ ∏ q ∈ A.offDiag.filter (fun q => q.1 < q.2), (q.2 - q.1) :=
  TrustedBank.CarryTower.lcm_dvd_pairwise_diff_prod A hpos hsum

example (A : Finset ℕ) (p : ℕ) (hp : p.Prime) (hpos : ∀ a ∈ A, 0 < a)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) (he : 1 ≤ Erdos287.topExp A p) :
    2 ≤ (Erdos287.topLayer A p).card :=
  TrustedBank.CarryTower.two_le_card_topLayer A p hp hpos hsum he

/-! ## Erdős #287 — generalized fixed-cofactor blocker -/

example (ce : Erdos287.Gap2CE) {p q r e j : ℕ}
    (hp : p.Prime) (hr : r.Prime) (he : 1 ≤ e) (hj : 1 ≤ j) (hq : q = r ^ e)
    (heq : p = j * q + 1)
    (hpN : ce.N + 1 ≤ p) (hpM : p ≤ ce.M) (hM2 : ce.M < 2 * p)
    (hqsq : ce.M < q ^ 2) (hthr : Erdos287.C (2 * j) < (r : ℤ)) : False :=
  TrustedBank.Erdos287Blockers.Gap2CE.fixedCofactor_blocker_sub ce hp hr he hj hq heq
    hpN hpM hM2 hqsq hthr

example (ce : Erdos287.Gap2CE) {p q r e j : ℕ}
    (hp : p.Prime) (hr : r.Prime) (he : 1 ≤ e) (hj : 1 ≤ j) (hq : q = r ^ e)
    (heq : p + 1 = j * q)
    (hpN : ce.N ≤ p) (hpM : p + 1 ≤ ce.M) (hM2 : ce.M < 2 * p)
    (hqsq : ce.M < q ^ 2) (hthr : Erdos287.C (2 * j) < (r : ℤ)) : False :=
  TrustedBank.Erdos287Blockers.Gap2CE.fixedCofactor_blocker_add ce hp hr he hj hq heq
    hpN hpM hM2 hqsq hthr

end Validation
