import Mathlib
import RequestProject.Erdos287.CharacterGram3221

/-!
# V20, Phases A / C / D / F — the exact high-conductor character Gram

`3221-HIGHCOND-CHARACTER-EXPANSION45 : LEAN_PROVED_FINITE`
`3221-INVERSE-SAMPLED-CHARACTER-ALGEBRA45 : LEAN_PROVED`
`3221-MSAMPLED-CHARACTER-GRAM45 : LEAN_PROVED_FINITE`
`3221-SEPARATE-GRAM-L2-45 : CAPACITY NONCLOSING BY 12/35`

Everything in this file is a **finite identity or a finite inequality**.  No analytic
estimate is proved, assumed, or axiomatised, and no interface is inhabited.

## Contents

* **§2 (Phase A).**  The high-conductor character set is the *literal* conductor filter
  `Erdos287.CharGram3221.highSet q Dcut` (Dirichlet-character and conductor infrastructure
  is available, so nothing is invented): `mem_highSet_iff_lt_conductor`.
* **§3.**  The inverse-sampled residue character algebra: `affineSample`,
  `affineSample_mul_eq_one`, `affineSample_isUnit`, `affineSample_inv`,
  `affineSample_character_factor`, `inverseSample_character_identity`.  All hypotheses
  (`q` odd via `2m` invertible, `m` a unit, `s² = 1`) are explicit.
* **§4.**  The high-conductor expansion compiler: `cHigh_inverseSampled_expansion`,
  the literal identity
  `C_q^{>D}(a_m) = φ(q)⁻¹ ∑_{χ ∈ H_q} χ(−2s) χ(m) ĉ_q(χ)`.
* **§7/§8 (Phase C).**  `unitBox`, `shortMGram`, `highCoeff`, `autocorr`.
* **§9.**  The central V20 finite theorem `inverseSampledVariance_eq_characterGram`
  (with its abstract kernel `charSource_variance_eq_gram`): the exact regrouping of the
  inverse-sampled variance by `ξ = χ ψ⁻¹`.  **No Cauchy, no Burgess, no large sieve.**
* **§10.**  The same-primitive lift firewall at a fixed modulus:
  `fixedModulus_samePrimitive_induced_unique`.
* **§11 (Phase D).**  The finite diagonal/off-diagonal split `characterGram_diag_split`
  and `autocorr_principal_eq_energy`.
* **§17/§18 (Phase F).**  `gram_parseval` (character orthogonality Parseval for the
  short-`m` Gram, under the injectivity hypothesis that is exactly the `M < q` condition)
  and the autocorrelation Young bounds `autocorr_sup_le`, `autocorr_l2_sq_le`.
* **§19.**  The separate-`L²` death certificate: the source-blind chain
  `separateL2_compiler` plus the exponent audit `separateGramL2_capacity_deficit`
  (`51/35 − 39/35 = 12/35 > 0`), a permanent anti-loop firewall.

Erdős #287 remains OPEN; Balanced7 remains OPEN.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

open Finset
open scoped BigOperators

namespace Erdos287
namespace V20Gram

open Erdos287.CharGram3221

/-! ## §2. The high-conductor character set, as literal data -/

/-- Membership in the literal high-conductor set `H_q = {χ : cond(χ) > Dcut}`. -/
theorem mem_highSet_iff_lt_conductor {q Dcut : ℕ} (chi : DirichletCharacter ℂ q) :
    chi ∈ highSet q Dcut ↔ Dcut < chi.conductor := by
  rw [highSet, Finset.mem_filter]
  exact ⟨fun h => Nat.not_le.mp h.2, fun h => ⟨Finset.mem_univ _, Nat.not_le.mpr h⟩⟩

/-- Rewriting a sum over the high-conductor set as a full character sum with an explicit
conductor test. -/
theorem sum_highSet_eq_sum_ite {q Dcut : ℕ} (g : DirichletCharacter ℂ q → ℂ) :
    ∑ chi ∈ highSet q Dcut, g chi
      = ∑ chi : DirichletCharacter ℂ q, (if Dcut < chi.conductor then g chi else 0) := by
  rw [highSet, Finset.sum_filter]
  refine Finset.sum_congr rfl fun chi _ => ?_
  by_cases h : Dcut < chi.conductor
  · rw [if_pos (Nat.not_le.mpr h), if_pos h]
  · rw [if_neg (by simpa using Nat.le_of_not_lt h), if_neg h]

/-! ## §3. The inverse-sampled residue character algebra -/

/-- The affine inverse sample `a_m = −s · (2m)⁻¹` in `ZMod q`.  This is definitionally the
`samplePoint` of the V19 data structure. -/
def affineSample (q : ℕ) (s : ℤ) (m : ℕ) : ZMod q :=
  -(s : ZMod q) * ((2 * m : ℕ) : ZMod q)⁻¹

/-- The V19 sample point is exactly `affineSample`. -/
theorem affineSample_eq_samplePoint
    (Dat : Erdos287.HighCond3221.InverseSampledHighCond3221Data) (q m : ℕ) :
    affineSample q Dat.sign m = Dat.samplePoint q m := rfl

/-- `a_m · (−s · 2m) = 1`: the explicit inverse of the affine sample. -/
theorem affineSample_mul_eq_one {q : ℕ} {s : ℤ} {m : ℕ} (hs : s ^ 2 = 1)
    (hu : IsUnit ((2 * m : ℕ) : ZMod q)) :
    affineSample q s m * (-(s : ZMod q) * ((2 * m : ℕ) : ZMod q)) = 1 := by
  have hs' : ((s : ZMod q)) * (s : ZMod q) = 1 := by
    have h : ((s ^ 2 : ℤ) : ZMod q) = ((1 : ℤ) : ZMod q) := by rw [hs]
    push_cast at h
    linear_combination h
  rw [affineSample, show -(s : ZMod q) * ((2 * m : ℕ) : ZMod q)⁻¹ *
      (-(s : ZMod q) * ((2 * m : ℕ) : ZMod q))
      = ((s : ZMod q) * (s : ZMod q)) *
        (((2 * m : ℕ) : ZMod q)⁻¹ * ((2 * m : ℕ) : ZMod q)) from by ring,
    hs', ZMod.inv_mul_of_unit _ hu, one_mul]

/-- The affine sample is a unit. -/
theorem affineSample_isUnit {q : ℕ} {s : ℤ} {m : ℕ} (hs : s ^ 2 = 1)
    (hu : IsUnit ((2 * m : ℕ) : ZMod q)) : IsUnit (affineSample q s m) :=
  IsUnit.of_mul_eq_one _ (affineSample_mul_eq_one hs hu)

/-- `a_m⁻¹ = −2 s m`. -/
theorem affineSample_inv {q : ℕ} {s : ℤ} {m : ℕ} (hs : s ^ 2 = 1)
    (hu : IsUnit ((2 * m : ℕ) : ZMod q)) :
    (affineSample q s m)⁻¹ = ((-2 * s : ℤ) : ZMod q) * ((m : ℕ) : ZMod q) := by
  rw [ZMod.inv_eq_of_mul_eq_one _ _ _ (affineSample_mul_eq_one hs hu)]
  push_cast
  ring

/-- Conjugation of a character value at a unit is evaluation at the inverse. -/
theorem conj_char_apply {q : ℕ} (chi : DirichletCharacter ℂ q) {a : ZMod q} (ha : IsUnit a) :
    (starRingEnd ℂ) (chi a) = chi a⁻¹ := by
  have h1 : chi a * chi a⁻¹ = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit _ ha, MulChar.map_one]
  have h2 : ‖chi a‖ = 1 := by
    have := chi.unit_norm_eq_one ha.unit
    simpa [IsUnit.unit_spec] using this
  rw [← Complex.inv_eq_conj h2]
  exact inv_eq_of_mul_eq_one_right h1

/-- Conjugation of a character value at a unit is the value of the inverse character. -/
theorem conj_char_eq_inv_char {q : ℕ} (chi : DirichletCharacter ℂ q) {a : ZMod q}
    (ha : IsUnit a) : (starRingEnd ℂ) (chi a) = chi⁻¹ a := by
  rw [MulChar.inv_apply_eq_inv', ← Complex.inv_eq_conj]
  have := chi.unit_norm_eq_one ha.unit
  simpa [IsUnit.unit_spec] using this

/-- **`affineSample_character_factor`.**  `LEAN_PROVED`.

`χ(a_m⁻¹) = χ(−2s) · χ(m)`. -/
theorem affineSample_character_factor {q : ℕ} {s : ℤ} {m : ℕ} (hs : s ^ 2 = 1)
    (hu : IsUnit ((2 * m : ℕ) : ZMod q)) (chi : DirichletCharacter ℂ q) :
    chi ((affineSample q s m)⁻¹)
      = chi (((-2 * s : ℤ) : ZMod q)) * chi ((m : ℕ) : ZMod q) := by
  rw [affineSample_inv hs hu, map_mul]

/-- **`inverseSample_character_identity`.**  `LEAN_PROVED`.

The exact character identity at the inverse sample, in the repository's conjugation
convention:

`conj(χ(a_m)) = χ(−2s) · χ(m)`,

for `s = ±1` and `2m` invertible modulo `q` (in particular `q` odd and `m` a unit). -/
theorem inverseSample_character_identity {q : ℕ} {s : ℤ} {m : ℕ} (hs : s ^ 2 = 1)
    (hu : IsUnit ((2 * m : ℕ) : ZMod q)) (chi : DirichletCharacter ℂ q) :
    (starRingEnd ℂ) (chi (affineSample q s m))
      = chi (((-2 * s : ℤ) : ZMod q)) * chi ((m : ℕ) : ZMod q) := by
  rw [conj_char_apply chi (affineSample_isUnit hs hu)]
  exact affineSample_character_factor hs hu chi

/-! ## §4. The high-conductor expansion compiler -/

/-- The high-conductor character coefficient `F_q(χ) = 1_{cond χ > Dcut} · ĉ_q(χ)`. -/
noncomputable def highCoeff (q Dcut : ℕ) (Wbox : Finset ℤ) (c : ℤ → ℂ)
    (chi : DirichletCharacter ℂ q) : ℂ :=
  if Dcut < chi.conductor then cHat q Wbox c chi else 0

/-- **`cHigh_inverseSampled_expansion`.**  `LEAN_PROVED_FINITE`.

The literal high-conductor expansion at the inverse sample:

`C_q^{>D}(a_m) = φ(q)⁻¹ ∑_{χ ∈ H_q} χ(−2s) χ(m) ĉ_q(χ)`.

Every object is a literal Dirichlet-character construction; nothing is postulated. -/
theorem cHigh_inverseSampled_expansion {q : ℕ} {s : ℤ} {m : ℕ} (Dcut : ℕ)
    (Wbox : Finset ℤ) (c : ℤ → ℂ) (hs : s ^ 2 = 1)
    (hu : IsUnit ((2 * m : ℕ) : ZMod q)) :
    cHigh q Dcut Wbox c (affineSample q s m)
      = (q.totient : ℂ)⁻¹ * ∑ chi ∈ highSet q Dcut,
          chi (((-2 * s : ℤ) : ZMod q)) * chi ((m : ℕ) : ZMod q) * cHat q Wbox c chi := by
  rw [cHigh]
  congr 1
  refine Finset.sum_congr rfl fun chi _ => ?_
  rw [affineSample_character_factor hs hu chi]

/-! ## §7/§8. The short-`m` Gram, the high-conductor coefficient and its autocorrelation -/

/-- The unit sector of the `m`-box: `{m ∈ Mbox : (m, q) = 1}`. -/
def unitBox (q : ℕ) (Mset : Finset ℕ) : Finset ℕ :=
  Mset.filter (fun m => Nat.Coprime m q)

/-- Members of the unit box are units modulo `q`. -/
theorem mem_unitBox_isUnit {q : ℕ} [NeZero q] {Mset : Finset ℕ} {m : ℕ}
    (hm : m ∈ unitBox q Mset) : IsUnit ((m : ZMod q)) :=
  (ZMod.isUnit_iff_coprime m q).mpr (Finset.mem_filter.mp hm).2

/-- **The short-`m` character Gram** `G_{q,M}(ξ) = ∑_{m ∈ Mbox, (m,q)=1} Φ(m) ξ(m)`. -/
noncomputable def shortMGram (q : ℕ) (Mset : Finset ℕ) (Phi : ℕ → ℂ)
    (xi : DirichletCharacter ℂ q) : ℂ :=
  ∑ m ∈ unitBox q Mset, Phi m * xi ((m : ℕ) : ZMod q)

/-- **The character-group autocorrelation** `A_q(ξ) = ∑_χ F(χ) conj(F(χ ξ⁻¹))`. -/
noncomputable def autocorr (q : ℕ) (F : DirichletCharacter ℂ q → ℂ)
    (xi : DirichletCharacter ℂ q) : ℂ :=
  ∑ chi : DirichletCharacter ℂ q, F chi * (starRingEnd ℂ) (F (chi * xi⁻¹))

/-- The shifted form of the autocorrelation, `A_q(ξ) = ∑_ψ F(ξψ) conj(F(ψ))`. -/
theorem autocorr_reindex (q : ℕ) (F : DirichletCharacter ℂ q → ℂ)
    (xi : DirichletCharacter ℂ q) :
    autocorr q F xi
      = ∑ psi : DirichletCharacter ℂ q, F (xi * psi) * (starRingEnd ℂ) (F psi) := by
  rw [autocorr]
  refine (Fintype.sum_equiv (Equiv.mulLeft xi) _ _ ?_).symm
  intro psi
  simp [mul_assoc]

/-- The abstract character source `C(m) = φ(q)⁻¹ ∑_χ F(χ) χ(t) χ(m)`; with
`t = −2s` and `F = highCoeff` this is exactly `C_q^{>D}(a_m)` (see
`charSrc_eq_cHigh_inverseSampled`). -/
noncomputable def charSrc (q : ℕ) (F : DirichletCharacter ℂ q → ℂ) (t : ZMod q) (m : ℕ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : DirichletCharacter ℂ q, F chi * chi t * chi ((m : ℕ) : ZMod q)

/-- The abstract source specialises to the literal high-conductor residue projection at the
inverse sample. -/
theorem charSrc_eq_cHigh_inverseSampled {q : ℕ} {s : ℤ} {m : ℕ} (Dcut : ℕ)
    (Wbox : Finset ℤ) (c : ℤ → ℂ) (hs : s ^ 2 = 1)
    (hu : IsUnit ((2 * m : ℕ) : ZMod q)) :
    charSrc q (highCoeff q Dcut Wbox c) (((-2 * s : ℤ) : ZMod q)) m
      = cHigh q Dcut Wbox c (affineSample q s m) := by
  rw [cHigh_inverseSampled_expansion Dcut Wbox c hs hu, charSrc,
    sum_highSet_eq_sum_ite]
  congr 1
  refine Finset.sum_congr rfl fun chi _ => ?_
  rw [highCoeff]
  by_cases h : Dcut < chi.conductor
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]; ring

/-! ## §9. The controlling Gram identity -/

/-- **`charSource_variance_eq_gram`** — the abstract kernel of the central V20 theorem.
`LEAN_PROVED_FINITE`.

For any coefficient family `F` on the character group and any unit `t`,

`∑_{m unit} Φ(m) |C(m)|² = φ(q)⁻² ∑_ξ ξ(t) G_{q,M}(ξ) A_q(ξ)`,

where `C(m) = φ(q)⁻¹ ∑_χ F(χ) χ(t) χ(m)`.  The regrouping is by `ξ = χ ψ⁻¹`.

**Exact identity: no Cauchy–Schwarz, no Burgess, no large sieve.** -/
theorem charSource_variance_eq_gram (q : ℕ) [NeZero q] (F : DirichletCharacter ℂ q → ℂ)
    {t : ZMod q} (ht : IsUnit t) (Mset : Finset ℕ) (Phi : ℕ → ℂ) :
    ∑ m ∈ unitBox q Mset, Phi m * (charSrc q F t m * (starRingEnd ℂ) (charSrc q F t m))
      = (q.totient : ℂ)⁻¹ ^ 2 *
        ∑ xi : DirichletCharacter ℂ q, xi t * shortMGram q Mset Phi xi * autocorr q F xi := by
  have hct : (starRingEnd ℂ) ((q.totient : ℂ)⁻¹) = (q.totient : ℂ)⁻¹ := by
    rw [map_inv₀]; norm_num
  have hpt : ∀ m ∈ unitBox q Mset,
      Phi m * (charSrc q F t m * (starRingEnd ℂ) (charSrc q F t m))
        = (q.totient : ℂ)⁻¹ ^ 2 * ∑ chi : DirichletCharacter ℂ q,
            ∑ psi : DirichletCharacter ℂ q,
              F chi * (starRingEnd ℂ) (F psi) * (chi * psi⁻¹) t *
                (Phi m * (chi * psi⁻¹) ((m : ℕ) : ZMod q)) := by
    intro m hm
    have hmu : IsUnit ((m : ZMod q)) := mem_unitBox_isUnit hm
    have hA : (∑ chi : DirichletCharacter ℂ q, F chi * chi t * chi ((m : ℕ) : ZMod q)) *
        (∑ psi : DirichletCharacter ℂ q,
          (starRingEnd ℂ) (F psi * psi t * psi ((m : ℕ) : ZMod q)))
        = ∑ chi : DirichletCharacter ℂ q, ∑ psi : DirichletCharacter ℂ q,
            F chi * (starRingEnd ℂ) (F psi) * (chi * psi⁻¹) t *
              (chi * psi⁻¹) ((m : ℕ) : ZMod q) := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun chi _ => Finset.sum_congr rfl fun psi _ => ?_
      rw [map_mul, map_mul, MulChar.mul_apply, MulChar.mul_apply,
        ← conj_char_eq_inv_char psi ht, ← conj_char_eq_inv_char psi hmu]
      ring
    calc Phi m * (charSrc q F t m * (starRingEnd ℂ) (charSrc q F t m))
        = (q.totient : ℂ)⁻¹ ^ 2 * (Phi m *
            ((∑ chi : DirichletCharacter ℂ q, F chi * chi t * chi ((m : ℕ) : ZMod q)) *
              (∑ psi : DirichletCharacter ℂ q,
                (starRingEnd ℂ) (F psi * psi t * psi ((m : ℕ) : ZMod q))))) := by
          rw [charSrc, map_mul, hct, map_sum]; ring
      _ = (q.totient : ℂ)⁻¹ ^ 2 * (Phi m * ∑ chi : DirichletCharacter ℂ q,
            ∑ psi : DirichletCharacter ℂ q, F chi * (starRingEnd ℂ) (F psi) *
              (chi * psi⁻¹) t * (chi * psi⁻¹) ((m : ℕ) : ZMod q)) := by rw [hA]
      _ = _ := by
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun chi _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun psi _ => by ring
  rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum]
  congr 1
  have hswap : ∑ m ∈ unitBox q Mset, ∑ chi : DirichletCharacter ℂ q,
      ∑ psi : DirichletCharacter ℂ q, F chi * (starRingEnd ℂ) (F psi) * (chi * psi⁻¹) t *
        (Phi m * (chi * psi⁻¹) ((m : ℕ) : ZMod q))
      = ∑ chi : DirichletCharacter ℂ q, ∑ psi : DirichletCharacter ℂ q,
          F chi * (starRingEnd ℂ) (F psi) * (chi * psi⁻¹) t *
            shortMGram q Mset Phi (chi * psi⁻¹) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun chi _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun psi _ => by rw [shortMGram, Finset.mul_sum]
  rw [hswap]
  have hre : ∀ (f : DirichletCharacter ℂ q → DirichletCharacter ℂ q → ℂ),
      ∑ chi : DirichletCharacter ℂ q, ∑ psi : DirichletCharacter ℂ q, f chi psi
        = ∑ xi : DirichletCharacter ℂ q, ∑ psi : DirichletCharacter ℂ q, f (xi * psi) psi := by
    intro f
    rw [Finset.sum_comm]
    rw [show (∑ psi : DirichletCharacter ℂ q, ∑ chi : DirichletCharacter ℂ q, f chi psi)
        = ∑ psi : DirichletCharacter ℂ q, ∑ xi : DirichletCharacter ℂ q, f (xi * psi) psi from
      Finset.sum_congr rfl fun psi _ =>
        (Fintype.sum_equiv (Equiv.mulRight psi) _ _ (fun _ => rfl)).symm]
    exact Finset.sum_comm
  rw [hre]
  refine Finset.sum_congr rfl fun xi _ => ?_
  rw [autocorr_reindex, Finset.mul_sum]
  refine Finset.sum_congr rfl fun psi _ => ?_
  rw [show (xi * psi) * psi⁻¹ = xi from by group]
  ring

/-- **`inverseSampledVariance_eq_characterGram`** — the central V20 finite theorem.
`LEAN_PROVED_FINITE`.

Summed over the modulus box with the (post-Cauchy, unsigned) weight `μ²(q)/φ(q)²`:

`V_hi = ∑_q μ²(q)/φ(q)² ∑_ξ ξ(−2s) G_{q,M}(ξ) A_q(ξ)`,

where the `m`-sum runs over the unit sector of the `m`-box and the inner source is the
literal high-conductor projection at the inverse sample `a_m = −s(2m)⁻¹`.

**Exact identity.  No Cauchy, no Burgess, no large sieve.** -/
theorem inverseSampledVariance_eq_characterGram (Qbox : Finset ℕ) (wt : ℕ → ℂ)
    (s : ℤ) (hs : s ^ 2 = 1) (Mset : Finset ℕ) (Phi : ℕ → ℂ)
    (Dcut : ℕ) (Wbox : Finset ℤ) (c : ℤ → ℂ)
    (hQ : ∀ q ∈ Qbox, NeZero q)
    (hunit : ∀ q ∈ Qbox, ∀ m ∈ unitBox q Mset, IsUnit ((2 * m : ℕ) : ZMod q))
    (ht : ∀ q ∈ Qbox, IsUnit (((-2 * s : ℤ) : ZMod q))) :
    ∑ q ∈ Qbox, wt q * ∑ m ∈ unitBox q Mset,
        Phi m * (cHigh q Dcut Wbox c (affineSample q s m) *
          (starRingEnd ℂ) (cHigh q Dcut Wbox c (affineSample q s m)))
      = ∑ q ∈ Qbox, wt q * ((q.totient : ℂ)⁻¹ ^ 2 *
          ∑ xi : DirichletCharacter ℂ q, xi (((-2 * s : ℤ) : ZMod q)) *
            shortMGram q Mset Phi xi * autocorr q (highCoeff q Dcut Wbox c) xi) := by
  refine Finset.sum_congr rfl fun q hq => ?_
  haveI : NeZero q := hQ q hq
  congr 1
  rw [← charSource_variance_eq_gram q (highCoeff q Dcut Wbox c) (ht q hq) Mset Phi]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [charSrc_eq_cHigh_inverseSampled Dcut Wbox c hs (hunit q hq m hm)]

/-! ## §10. The same-primitive lift firewall (fixed modulus) -/

/-- **`fixedModulus_samePrimitive_induced_unique`.**  `LEAN_PROVED`.

At a **fixed** modulus `q`, a primitive character `θ` of conductor `r ∣ q` determines a
*unique* induced character modulo `q`.  Hence two distinct characters `χ ≠ ψ` modulo the
same `q` can never be lifts of exactly the same primitive character.

This statement is deliberately *not* generalised across different moduli. -/
theorem fixedModulus_samePrimitive_induced_unique {q r : ℕ} (hr : r ∣ q)
    (theta : DirichletCharacter ℂ r) {chi psi : DirichletCharacter ℂ q}
    (hchi : chi = DirichletCharacter.changeLevel hr theta)
    (hpsi : psi = DirichletCharacter.changeLevel hr theta) : chi = psi := by
  rw [hchi, hpsi]

/-- The contrapositive form used downstream: distinct characters at the same modulus have
distinct primitive sources. -/
theorem fixedModulus_ne_of_lift_ne {q r : ℕ} (hr : r ∣ q)
    {theta theta' : DirichletCharacter ℂ r}
    (h : DirichletCharacter.changeLevel hr theta ≠ DirichletCharacter.changeLevel hr theta') :
    theta ≠ theta' := fun hc => h (by rw [hc])

/-! ## §11. The diagonal / off-diagonal split -/

/-- **`characterGram_diag_split`.**  `LEAN_PROVED_FINITE`.

The exact finite decomposition `V = V_diag + V_offdiag`, separating the principal
character `ξ = 1`. -/
theorem characterGram_diag_split (q : ℕ) [DecidableEq (DirichletCharacter ℂ q)]
    (T : DirichletCharacter ℂ q → ℂ) :
    ∑ xi : DirichletCharacter ℂ q, T xi
      = T 1 + ∑ xi ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), T xi := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ q))]

/-- **`autocorr_principal_eq_energy`.**  `LEAN_PROVED_FINITE`.

At the principal character the autocorrelation is the high-conductor energy:
`A_q(1) = ∑_{χ} |F(χ)|²`, which for `F = highCoeff` is `∑_{χ high} |ĉ_q(χ)|²`. -/
theorem autocorr_principal_eq_energy (q : ℕ) (F : DirichletCharacter ℂ q → ℂ) :
    autocorr q F 1 = ∑ chi : DirichletCharacter ℂ q, F chi * (starRingEnd ℂ) (F chi) := by
  rw [autocorr]
  exact Finset.sum_congr rfl fun chi _ => by rw [inv_one, mul_one]

/-- The principal autocorrelation of the high-conductor coefficient is literally the
high-conductor energy `∑_{χ ∈ H_q} |ĉ_q(χ)|²`. -/
theorem autocorr_principal_highCoeff (q Dcut : ℕ) (Wbox : Finset ℤ) (c : ℤ → ℂ) :
    autocorr q (highCoeff q Dcut Wbox c) 1
      = ∑ chi ∈ highSet q Dcut, cHat q Wbox c chi * (starRingEnd ℂ) (cHat q Wbox c chi) := by
  rw [autocorr_principal_eq_energy, sum_highSet_eq_sum_ite]
  refine Finset.sum_congr rfl fun chi _ => ?_
  rw [highCoeff]
  by_cases h : Dcut < chi.conductor
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]; simp

/-! ## §17. Character Gram Parseval -/

/-- **`gram_parseval`.**  `LEAN_PROVED_FINITE`.

Exact character orthogonality Parseval for the short-`m` Gram:

`∑_ξ |G_{q,M}(ξ)|² = φ(q) ∑_{m ∈ Mbox, (m,q)=1} |Φ(m)|²`,

under the hypothesis that reduction mod `q` is injective on the unit box — which is exactly
the physical condition `M < q`. -/
theorem gram_parseval (q : ℕ) [NeZero q] (Mset : Finset ℕ) (Phi : ℕ → ℂ)
    (hinj : ∀ m ∈ unitBox q Mset, ∀ m' ∈ unitBox q Mset,
      ((m : ZMod q)) = ((m' : ZMod q)) → m = m') :
    ∑ xi : DirichletCharacter ℂ q, shortMGram q Mset Phi xi *
        (starRingEnd ℂ) (shortMGram q Mset Phi xi)
      = (q.totient : ℂ) * ∑ m ∈ unitBox q Mset, Phi m * (starRingEnd ℂ) (Phi m) := by
  have hexp : ∀ xi : DirichletCharacter ℂ q,
      shortMGram q Mset Phi xi * (starRingEnd ℂ) (shortMGram q Mset Phi xi)
        = ∑ m ∈ unitBox q Mset, ∑ m' ∈ unitBox q Mset,
            Phi m * (starRingEnd ℂ) (Phi m') * (xi ((m' : ZMod q))⁻¹ * xi ((m : ZMod q))) := by
    intro xi
    rw [shortMGram, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' hm' => ?_
    rw [map_mul, conj_char_apply xi (mem_unitBox_isUnit hm')]
    ring
  calc ∑ xi : DirichletCharacter ℂ q, shortMGram q Mset Phi xi *
          (starRingEnd ℂ) (shortMGram q Mset Phi xi)
      = ∑ m ∈ unitBox q Mset, ∑ m' ∈ unitBox q Mset, Phi m * (starRingEnd ℂ) (Phi m') *
          ∑ xi : DirichletCharacter ℂ q, xi ((m' : ZMod q))⁻¹ * xi ((m : ZMod q)) := by
        rw [Finset.sum_congr rfl (fun xi _ => hexp xi), Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m' _ => by rw [Finset.mul_sum]
    _ = (q.totient : ℂ) * ∑ m ∈ unitBox q Mset, Phi m * (starRingEnd ℂ) (Phi m) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [Finset.sum_eq_single m]
        · rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ (mem_unitBox_isUnit hm)]
          simp
          ring
        · intro m' hm' hne
          rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ (mem_unitBox_isUnit hm')]
          have hne' : ((m' : ZMod q)) ≠ ((m : ZMod q)) := fun h => hne (hinj m' hm' m hm h)
          simp [hne']
        · intro h; exact absurd hm h

/-! ## §18. The autocorrelation Young bound -/

/-- The character-group energy `E_q = ∑_χ |F(χ)|²` is invariant under a shift. -/
theorem energy_shift_invariant (q : ℕ) (F : DirichletCharacter ℂ q → ℂ)
    (xi : DirichletCharacter ℂ q) :
    ∑ chi : DirichletCharacter ℂ q, ‖F (chi * xi⁻¹)‖ ^ 2
      = ∑ chi : DirichletCharacter ℂ q, ‖F chi‖ ^ 2 :=
  Fintype.sum_equiv (Equiv.mulRight xi⁻¹) _ _ (fun _ => rfl)

/-- **`autocorr_sup_le`.**  `LEAN_PROVED_FINITE`.

Pure finite harmonic analysis: `|A_q(ξ)| ≤ E_q = ∑_χ |F(χ)|²`, uniformly in `ξ`. -/
theorem autocorr_sup_le (q : ℕ) (F : DirichletCharacter ℂ q → ℂ)
    (xi : DirichletCharacter ℂ q) :
    ‖autocorr q F xi‖ ≤ ∑ chi : DirichletCharacter ℂ q, ‖F chi‖ ^ 2 := by
  have hE : (0 : ℝ) ≤ ∑ chi : DirichletCharacter ℂ q, ‖F chi‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : ‖autocorr q F xi‖
      ≤ ∑ chi : DirichletCharacter ℂ q, ‖F chi‖ * ‖F (chi * xi⁻¹)‖ := by
    rw [autocorr]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun chi _ => ?_)
    rw [norm_mul, RCLike.norm_conj]
  have h2 := sum_mul_sq_le_sq_mul_sq Finset.univ (fun chi : DirichletCharacter ℂ q => ‖F chi‖)
    (fun chi : DirichletCharacter ℂ q => ‖F (chi * xi⁻¹)‖)
  rw [energy_shift_invariant q F xi] at h2
  have h3 : (∑ chi : DirichletCharacter ℂ q, ‖F chi‖ * ‖F (chi * xi⁻¹)‖)
      ≤ ∑ chi : DirichletCharacter ℂ q, ‖F chi‖ ^ 2 := by
    nlinarith [Finset.sum_nonneg (fun chi (_ : chi ∈ (Finset.univ : Finset (DirichletCharacter ℂ q))) =>
      mul_nonneg (norm_nonneg (F chi)) (norm_nonneg (F (chi * xi⁻¹))))]
  linarith

/-- **`autocorr_l2_sq_le`.**  `LEAN_PROVED_FINITE`.

The `L²` (Young) bound on the character group: `‖A_q‖₂² ≤ #Ĝ · E_q²`, i.e.
`‖A_q‖₂ ≤ √(#Ĝ) · E_q` — the precise normalised analogue of the schematic
`‖A_q‖₂ ≤ √(φ(q)) E_q`. -/
theorem autocorr_l2_sq_le (q : ℕ) (F : DirichletCharacter ℂ q → ℂ) :
    ∑ xi : DirichletCharacter ℂ q, ‖autocorr q F xi‖ ^ 2
      ≤ (Fintype.card (DirichletCharacter ℂ q) : ℝ) *
        (∑ chi : DirichletCharacter ℂ q, ‖F chi‖ ^ 2) ^ 2 := by
  have hE : (0 : ℝ) ≤ ∑ chi : DirichletCharacter ℂ q, ‖F chi‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hterm : ∀ xi : DirichletCharacter ℂ q, ‖autocorr q F xi‖ ^ 2
      ≤ (∑ chi : DirichletCharacter ℂ q, ‖F chi‖ ^ 2) ^ 2 := by
    intro xi
    have := autocorr_sup_le q F xi
    nlinarith [norm_nonneg (autocorr q F xi)]
  calc ∑ xi : DirichletCharacter ℂ q, ‖autocorr q F xi‖ ^ 2
      ≤ ∑ _xi : DirichletCharacter ℂ q, (∑ chi : DirichletCharacter ℂ q, ‖F chi‖ ^ 2) ^ 2 :=
        Finset.sum_le_sum fun xi _ => hterm xi
    _ = (Fintype.card (DirichletCharacter ℂ q) : ℝ) *
          (∑ chi : DirichletCharacter ℂ q, ‖F chi‖ ^ 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ## §19. The source-blind separate-`L²` death certificate -/

/-- **`separateL2_compiler`.**  `LEAN_PROVED_FINITE`.

Combining Parseval (§17) and the Young bound (§18) by Cauchy–Schwarz gives the
*source-blind* separate-`L²` route: for any `ξ`-supported family,

`|∑_ξ w(ξ) G(ξ) A(ξ)| ≤ ‖G‖₂ · ‖A‖₂`  when `|w(ξ)| ≤ 1`.

This is the exact inequality whose capacity is audited (and found nonclosing) below. -/
theorem separateL2_compiler (q : ℕ) (w G A : DirichletCharacter ℂ q → ℂ)
    (hw : ∀ xi : DirichletCharacter ℂ q, ‖w xi‖ ≤ 1) :
    ‖∑ xi : DirichletCharacter ℂ q, w xi * G xi * A xi‖
      ≤ Real.sqrt (∑ xi : DirichletCharacter ℂ q, ‖G xi‖ ^ 2) *
        Real.sqrt (∑ xi : DirichletCharacter ℂ q, ‖A xi‖ ^ 2) := by
  have h1 : ‖∑ xi : DirichletCharacter ℂ q, w xi * G xi * A xi‖
      ≤ ∑ xi : DirichletCharacter ℂ q, ‖G xi‖ * ‖A xi‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun xi _ => ?_)
    rw [norm_mul, norm_mul]
    have h := hw xi
    have hGA : (0 : ℝ) ≤ ‖G xi‖ * ‖A xi‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith [hGA, h, norm_nonneg (w xi)]
  have h2 := sum_mul_sq_le_sq_mul_sq Finset.univ (fun xi : DirichletCharacter ℂ q => ‖G xi‖)
    (fun xi : DirichletCharacter ℂ q => ‖A xi‖)
  have hGnn : (0 : ℝ) ≤ ∑ xi : DirichletCharacter ℂ q, ‖G xi‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hAnn : (0 : ℝ) ≤ ∑ xi : DirichletCharacter ℂ q, ‖A xi‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3 : (∑ xi : DirichletCharacter ℂ q, ‖G xi‖ * ‖A xi‖)
      ≤ Real.sqrt (∑ xi : DirichletCharacter ℂ q, ‖G xi‖ ^ 2) *
        Real.sqrt (∑ xi : DirichletCharacter ℂ q, ‖A xi‖ ^ 2) := by
    have hsq : (∑ xi : DirichletCharacter ℂ q, ‖G xi‖ * ‖A xi‖) ^ 2
        ≤ (Real.sqrt (∑ xi : DirichletCharacter ℂ q, ‖G xi‖ ^ 2) *
            Real.sqrt (∑ xi : DirichletCharacter ℂ q, ‖A xi‖ ^ 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hGnn, Real.sq_sqrt hAnn]
      exact h2
    have hnn : (0 : ℝ) ≤ Real.sqrt (∑ xi : DirichletCharacter ℂ q, ‖G xi‖ ^ 2) *
        Real.sqrt (∑ xi : DirichletCharacter ℂ q, ‖A xi‖ ^ 2) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [Finset.sum_nonneg (fun xi (_ : xi ∈ (Finset.univ : Finset (DirichletCharacter ℂ q))) =>
      mul_nonneg (norm_nonneg (G xi)) (norm_nonneg (A xi)))]
  linarith

/-- **`separateGramL2_capacity_deficit`.**  `PROVED_ALGEBRAIC / METADATA_ONLY`.

The exponent audit of the separate-`L²` route: the produced exponent `51/35` exceeds the
admissible `39/35` by `12/35 > 0`.  Hence the source-blind separation of the short-`m` Gram
from the five-box autocorrelation is **capacity nonclosing**; this is a permanent
anti-loop firewall and **not** a statement about any external theorem. -/
theorem separateGramL2_capacity_deficit :
    (51 : ℚ) / 35 - 39 / 35 = 12 / 35 ∧ (0 : ℚ) < 12 / 35 := by
  constructor <;> norm_num

end V20Gram
end Erdos287
