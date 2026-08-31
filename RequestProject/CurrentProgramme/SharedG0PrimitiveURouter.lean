import Mathlib
import RequestProject.CurrentProgramme.PrimitiveRamanujanAlgebra
import RequestProject.CurrentProgramme.SharedG0PrimitiveUParam
import RequestProject.CurrentProgramme.SharedG0UnitSectorGcd

/-!
# Exact shared-`g₀` local product — Erdős #287, SHARED-g₀ REPAIR Δ, §3

**Exact finite algebra over the repository's own additive phase** `e(x) = exp(2πix)`
(`Erdos287.NormalForm3221.phase`).  No analytic input.

The primitive-`u` sum of the shared-`g₀` router is

```
U_{g₀,D}(C) = ∑_{u mod g₀, u primitive} e(Cu/g₀),
```

where *primitive* means that both `t₁(u) = t₁⁰ + r₁u` and `t₂(u) = t₂⁰ + r₂u` are units
modulo `g₀` — exactly the two primitive exclusions of §2.

Proved here:

* `primitiveUSum_eq_complete_sub_excluded` — the **exact local factor**: for a prime `p`,
  `U_p(C) = p·1_{p ∣ C} - ∑_{u excluded} e(Cu/p)`, the excluded residues being the
  `ν_p(D) ≤ 2` residues of §2;
* `norm_primitiveUSum_le_modulus` — `|U_p(C)| ≤ p` (in fact for any modulus);
* `norm_primitiveUSum_le_two` — `|U_p(C)| ≤ 2` when `p ∤ C`;
* `prod_primeFactors_dvd_gcd` — for squarefree `g₀`, `∏_{p ∣ g₀, p ∣ C} p ∣ gcd(g₀,C)`;
* `abs_prod_local_le` — the router bound: if `U` factors as `∏_{p ∣ g₀} U_p` with local
  factors obeying the two elementary bounds, then `|U| ≤ 2^{ω(g₀)}·gcd(g₀,C)`.

Research status: `DET1-SHAREDG0-PRIMITIVE-U-ROUTER45 : FORMALLY PROVED ALGEBRAIC/FINITE
CORE.`
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace Erdos287
namespace SharedG0Router

open Erdos287.NormalForm3221
open Erdos287.PrimitiveRamanujan
open Erdos287.SharedG0Param

/-! ## §3.1  The primitive-`u` sum -/

/-- The two primitive conditions on the parameter `u` at modulus `g₀`. -/
def admissible (g0 : ℕ) (t10 t20 r1 r2 : ℤ) (u : ℕ) : Prop :=
  Int.gcd (t10 + r1 * u) (g0 : ℤ) = 1 ∧ Int.gcd (t20 + r2 * u) (g0 : ℤ) = 1

instance (g0 : ℕ) (t10 t20 r1 r2 : ℤ) (u : ℕ) :
    Decidable (admissible g0 t10 t20 r1 r2 u) := by
  unfold admissible; infer_instance

/-- The finite primitive-`u` sum `U_{g₀,D}(C) = ∑_{u mod g₀ primitive} e(Cu/g₀)`. -/
noncomputable def primitiveUSum (g0 : ℕ) (t10 t20 r1 r2 C : ℤ) : ℂ :=
  ∑ u ∈ Finset.range g0,
    if admissible g0 t10 t20 r1 r2 u then phase ((u : ℝ) * (C : ℝ) / (g0 : ℝ)) else 0

/-- The excluded residues at modulus `g₀`. -/
def excludedResidues (g0 : ℕ) (t10 t20 r1 r2 : ℤ) : Finset ℕ :=
  (Finset.range g0).filter (fun u => ¬ admissible g0 t10 t20 r1 r2 u)

/-- Each phase has modulus one. -/
theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  unfold phase
  rw [Complex.norm_exp_ofReal_mul_I]

/-! ## §3.2  The exact local factor -/

/-- **Exact local factor.**  `LEAN_PROVED`.

```
U_{g₀}(C) = g₀·1_{g₀ ∣ C} - ∑_{u excluded} e(Cu/g₀).
```

For `g₀ = p` prime this is the exact local factor of the router, the excluded set having
`ν_p(D) ≤ 2` elements by §2. -/
theorem primitiveUSum_eq_complete_sub_excluded {g0 : ℕ} (hg0 : 0 < g0) (t10 t20 r1 r2 C : ℤ) :
    primitiveUSum g0 t10 t20 r1 r2 C
      = (if (g0 : ℤ) ∣ C then (g0 : ℂ) else 0)
        - ∑ u ∈ excludedResidues g0 t10 t20 r1 r2, phase ((u : ℝ) * (C : ℝ) / (g0 : ℝ)) := by
  classical
  have hfull := full_phase_sum g0 hg0 C
  have hsplit : ∑ u ∈ Finset.range g0, phase ((u : ℝ) * (C : ℝ) / (g0 : ℝ))
      = (∑ u ∈ (Finset.range g0).filter (fun u => admissible g0 t10 t20 r1 r2 u),
          phase ((u : ℝ) * (C : ℝ) / (g0 : ℝ)))
        + ∑ u ∈ excludedResidues g0 t10 t20 r1 r2, phase ((u : ℝ) * (C : ℝ) / (g0 : ℝ)) := by
    rw [excludedResidues]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hU : primitiveUSum g0 t10 t20 r1 r2 C
      = ∑ u ∈ (Finset.range g0).filter (fun u => admissible g0 t10 t20 r1 r2 u),
          phase ((u : ℝ) * (C : ℝ) / (g0 : ℝ)) := by
    rw [primitiveUSum, Finset.sum_filter]
  rw [hU, hfull] at *
  rw [hsplit]
  ring

/-! ## §3.3  The two elementary local bounds -/

/-- `|U_{g₀}(C)| ≤ g₀`: in particular `|U_p(C)| ≤ p`, the bound used when `p ∣ C`. -/
theorem norm_primitiveUSum_le_modulus (g0 : ℕ) (t10 t20 r1 r2 C : ℤ) :
    ‖primitiveUSum g0 t10 t20 r1 r2 C‖ ≤ g0 := by
  classical
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ u ∈ Finset.range g0,
      ‖if admissible g0 t10 t20 r1 r2 u then phase ((u : ℝ) * (C : ℝ) / (g0 : ℝ)) else 0‖
        ≤ 1 := by
    intro u _
    by_cases h : admissible g0 t10 t20 r1 r2 u
    · rw [if_pos h, norm_phase]
    · rw [if_neg h, norm_zero]; norm_num
  calc ∑ u ∈ Finset.range g0,
        ‖if admissible g0 t10 t20 r1 r2 u then phase ((u : ℝ) * (C : ℝ) / (g0 : ℝ)) else 0‖
      ≤ ∑ _u ∈ Finset.range g0, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = g0 := by simp

/-- The excluded residues modulo a prime `p` inject into the two-element set of §2. -/
theorem card_excludedResidues_le_two {p : ℕ} (hp : p.Prime) {t10 t20 r1 r2 : ℤ}
    (hr1 : ¬ (p : ℤ) ∣ r1) (hr2 : ¬ (p : ℤ) ∣ r2) :
    (excludedResidues p t10 t20 r1 r2).card ≤ 2 := by
  classical
  haveI := Fact.mk hp
  have hmaps : ∀ u ∈ excludedResidues p t10 t20 r1 r2,
      ((u : ZMod p)) ∈ excludedU p t10 t20 r1 r2 := by
    intro u hu
    rw [excludedResidues, Finset.mem_filter, admissible] at hu
    obtain ⟨-, hnot⟩ := hu
    rw [excludedU_mem_iff hp hr1 hr2]
    have hgcd : ∀ z : ℤ, Int.gcd z (p : ℤ) ≠ 1 → (p : ℤ) ∣ z := by
      intro z hz
      by_contra hcon
      refine hz ?_
      have : Nat.Coprime p z.natAbs := (Nat.Prime.coprime_iff_not_dvd hp).2 (by
        intro hdvd
        exact hcon (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hdvd)))
      rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
      exact Nat.Coprime.symm this
    rcases not_and_or.1 hnot with h | h
    · left
      have hd := hgcd _ h
      have : ((t10 + r1 * u : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hd
      push_cast at this ⊢
      linear_combination this
    · right
      have hd := hgcd _ h
      have : ((t20 + r2 * u : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hd
      push_cast at this ⊢
      linear_combination this
  have hinj : ∀ u ∈ excludedResidues p t10 t20 r1 r2,
      ∀ v ∈ excludedResidues p t10 t20 r1 r2, ((u : ZMod p)) = ((v : ZMod p)) → u = v := by
    intro u hu v hv huv
    rw [excludedResidues, Finset.mem_filter, Finset.mem_range] at hu hv
    have h1 : (u : ZMod p).val = u := ZMod.val_natCast_of_lt hu.1
    have h2 : (v : ZMod p).val = v := ZMod.val_natCast_of_lt hv.1
    rw [← h1, ← h2, huv]
  have hcard := Finset.card_le_card_of_injOn (s := excludedResidues p t10 t20 r1 r2)
    (t := excludedU p t10 t20 r1 r2) (fun u : ℕ => (u : ZMod p)) hmaps
    (fun u hu v hv h => hinj u hu v hv h)
  have hle : (excludedU p t10 t20 r1 r2).card ≤ 2 := by
    rw [excludedU]
    exact le_trans (Finset.card_insert_le _ _) (by simp)
  omega

/-- **`|U_p(C)| ≤ 2` when `p ∤ C`.**  `LEAN_PROVED`.  This is the second elementary local
bound of the router. -/
theorem norm_primitiveUSum_le_two {p : ℕ} (hp : p.Prime) {t10 t20 r1 r2 C : ℤ}
    (hr1 : ¬ (p : ℤ) ∣ r1) (hr2 : ¬ (p : ℤ) ∣ r2) (hC : ¬ (p : ℤ) ∣ C) :
    ‖primitiveUSum p t10 t20 r1 r2 C‖ ≤ 2 := by
  classical
  rw [primitiveUSum_eq_complete_sub_excluded hp.pos, if_neg hC, zero_sub, norm_neg]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ u ∈ excludedResidues p t10 t20 r1 r2,
      ‖phase ((u : ℝ) * (C : ℝ) / (p : ℝ))‖ ≤ 1 := by
    intro u _
    rw [norm_phase]
  calc ∑ u ∈ excludedResidues p t10 t20 r1 r2, ‖phase ((u : ℝ) * (C : ℝ) / (p : ℝ))‖
      ≤ ∑ _u ∈ excludedResidues p t10 t20 r1 r2, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = (excludedResidues p t10 t20 r1 r2).card := by simp
    _ ≤ 2 := by exact_mod_cast card_excludedResidues_le_two hp hr1 hr2

/-! ## §3.4  The `gcd` bookkeeping of the product bound -/

/-- For squarefree `g₀`, the product of the primes dividing both `g₀` and `C` divides
`gcd(g₀,C)`. -/
theorem prod_primeFactors_dvd_gcd (g0 : ℕ) (C : ℤ) :
    (∏ p ∈ g0.primeFactors.filter (fun p : ℕ => ((p : ℤ) ∣ C)), p) ∣ Int.gcd (g0 : ℤ) C := by
  classical
  refine Finset.prod_primes_dvd _ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp
    exact (Nat.prime_of_mem_primeFactors hp.1).prime
  · intro p hp
    rw [Finset.mem_filter] at hp
    have hpg : (p : ℤ) ∣ (g0 : ℤ) :=
      Int.natCast_dvd_natCast.2 (Nat.dvd_of_mem_primeFactors hp.1)
    exact Int.dvd_gcd hpg hp.2

/-- **Router bound.**  `LEAN_PROVED`.

If the primitive-`u` sum factors over the primes of a squarefree `g₀` into local factors
obeying the two elementary bounds of §3.3, then

```
|U_{g₀,D}(C)| ≤ 2^{ω(g₀)} · gcd(g₀,C).
```
-/
theorem abs_prod_local_le {g0 : ℕ} {C : ℤ} (hC : C ≠ 0)
    (Uloc : ℕ → ℂ) (hbound : ∀ p ∈ g0.primeFactors,
      ‖Uloc p‖ ≤ (if ((p : ℤ) ∣ C) then (p : ℝ) else 2)) :
    ‖∏ p ∈ g0.primeFactors, Uloc p‖
      ≤ 2 ^ g0.primeFactors.card * (Int.gcd (g0 : ℤ) C : ℝ) := by
  classical
  have hprod : ‖∏ p ∈ g0.primeFactors, Uloc p‖
      = ∏ p ∈ g0.primeFactors, ‖Uloc p‖ := by
    rw [norm_prod]
  have hstep : ∏ p ∈ g0.primeFactors, ‖Uloc p‖
      ≤ ∏ p ∈ g0.primeFactors, (if ((p : ℤ) ∣ C) then (p : ℝ) else 2) := by
    refine Finset.prod_le_prod (fun p _ => norm_nonneg _) hbound
  have hsplit : ∏ p ∈ g0.primeFactors, (if ((p : ℤ) ∣ C) then (p : ℝ) else 2)
      = (∏ p ∈ g0.primeFactors.filter (fun p : ℕ => ((p : ℤ) ∣ C)), (p : ℝ))
        * ∏ p ∈ g0.primeFactors.filter (fun p : ℕ => ¬ ((p : ℤ) ∣ C)), (2 : ℝ) := by
    rw [← Finset.prod_filter_mul_prod_filter_not g0.primeFactors (fun p : ℕ => ((p : ℤ) ∣ C))]
    congr 1
    · exact Finset.prod_congr rfl (fun p hp => by rw [if_pos (Finset.mem_filter.1 hp).2])
    · exact Finset.prod_congr rfl (fun p hp => by rw [if_neg (Finset.mem_filter.1 hp).2])
  have hpow : ∏ p ∈ g0.primeFactors.filter (fun p : ℕ => ¬ ((p : ℤ) ∣ C)), (2 : ℝ)
      ≤ 2 ^ g0.primeFactors.card := by
    rw [Finset.prod_const]
    exact pow_le_pow_right₀ (by norm_num)
      (Finset.card_le_card (Finset.filter_subset _ _))
  have hgcdpos : 0 < Int.gcd (g0 : ℤ) C := Int.gcd_pos_of_ne_zero_right _ hC
  have hdvd := prod_primeFactors_dvd_gcd g0 C
  have hle : (∏ p ∈ g0.primeFactors.filter (fun p : ℕ => ((p : ℤ) ∣ C)), p) ≤ Int.gcd (g0 : ℤ) C :=
    Nat.le_of_dvd hgcdpos hdvd
  have hleR : (∏ p ∈ g0.primeFactors.filter (fun p : ℕ => ((p : ℤ) ∣ C)), (p : ℝ))
      ≤ (Int.gcd (g0 : ℤ) C : ℝ) := by
    have hcast : ((∏ p ∈ g0.primeFactors.filter (fun p : ℕ => ((p : ℤ) ∣ C)), p : ℕ) : ℝ)
        = ∏ p ∈ g0.primeFactors.filter (fun p : ℕ => ((p : ℤ) ∣ C)), (p : ℝ) := by
      push_cast
      rfl
    rw [← hcast]
    exact_mod_cast hle
  have hnn1 : (0 : ℝ) ≤ ∏ p ∈ g0.primeFactors.filter (fun p : ℕ => ((p : ℤ) ∣ C)), (p : ℝ) :=
    Finset.prod_nonneg (fun p _ => by positivity)
  have hnn2 : (0 : ℝ) ≤ ∏ p ∈ g0.primeFactors.filter (fun p : ℕ => ¬ ((p : ℤ) ∣ C)), (2 : ℝ) :=
    Finset.prod_nonneg (fun p _ => by norm_num)
  calc ‖∏ p ∈ g0.primeFactors, Uloc p‖
      = ∏ p ∈ g0.primeFactors, ‖Uloc p‖ := hprod
    _ ≤ ∏ p ∈ g0.primeFactors, (if ((p : ℤ) ∣ C) then (p : ℝ) else 2) := hstep
    _ = (∏ p ∈ g0.primeFactors.filter (fun p : ℕ => ((p : ℤ) ∣ C)), (p : ℝ))
          * ∏ p ∈ g0.primeFactors.filter (fun p : ℕ => ¬ ((p : ℤ) ∣ C)), (2 : ℝ) := hsplit
    _ ≤ (Int.gcd (g0 : ℤ) C : ℝ) * 2 ^ g0.primeFactors.card := by
        exact mul_le_mul hleR hpow hnn2 (by positivity)
    _ = 2 ^ g0.primeFactors.card * (Int.gcd (g0 : ℤ) C : ℝ) := by ring

/-! ## §3.5  The CRT factorisation -/

/-- The additive phase is additive. -/
theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Admissibility at a composite modulus splits over coprime factors, and each factor only
sees the corresponding residue of `u`. -/
theorem admissible_mul_iff {m n : ℕ} (t10 t20 r1 r2 : ℤ) (u : ℕ) :
    admissible (m * n) t10 t20 r1 r2 u ↔
      (admissible m t10 t20 r1 r2 (u % m) ∧ admissible n t10 t20 r1 r2 (u % n)) := by
  have hres : ∀ (k : ℕ) (t r : ℤ), Int.gcd (t + r * u) (k : ℤ)
      = Int.gcd (t + r * ((u % k : ℕ) : ℤ)) (k : ℤ) := by
    intro k t r
    have hu : ((u : ℤ)) - ((u % k : ℕ) : ℤ) = (k : ℤ) * ((u / k : ℕ) : ℤ) := by
      have hz := congrArg (fun t : ℕ => (t : ℤ)) (Nat.div_add_mod u k)
      simp only [Nat.cast_add, Nat.cast_mul] at hz
      linarith
    have hdvd : (k : ℤ) ∣ (t + r * u) - (t + r * ((u % k : ℕ) : ℤ)) := by
      refine ⟨r * ((u / k : ℕ) : ℤ), ?_⟩
      have hexp : (t + r * (u : ℤ)) - (t + r * ((u % k : ℕ) : ℤ))
          = r * ((u : ℤ) - ((u % k : ℕ) : ℤ)) := by ring
      rw [hexp, hu]
      ring
    rw [Int.gcd_comm, Int.gcd_comm (t + r * ((u % k : ℕ) : ℤ))]
    exact Erdos287.SharedG0UnitSector.gcd_congr_of_dvd_sub _ _ _ hdvd
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    have e1 : Nat.Coprime (t10 + r1 * (u : ℤ)).natAbs (m * n) := by
      rw [Int.gcd_eq_natAbs, Int.natAbs_natCast] at h1
      exact h1
    have e2 : Nat.Coprime (t20 + r2 * (u : ℤ)).natAbs (m * n) := by
      rw [Int.gcd_eq_natAbs, Int.natAbs_natCast] at h2
      exact h2
    rw [Nat.coprime_mul_iff_right] at e1 e2
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [← hres m t10 r1, Int.gcd_eq_natAbs, Int.natAbs_natCast]; exact e1.1
    · rw [← hres m t20 r2, Int.gcd_eq_natAbs, Int.natAbs_natCast]; exact e2.1
    · rw [← hres n t10 r1, Int.gcd_eq_natAbs, Int.natAbs_natCast]; exact e1.2
    · rw [← hres n t20 r2, Int.gcd_eq_natAbs, Int.natAbs_natCast]; exact e2.2
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    rw [← hres m t10 r1, Int.gcd_eq_natAbs, Int.natAbs_natCast] at h1
    rw [← hres m t20 r2, Int.gcd_eq_natAbs, Int.natAbs_natCast] at h2
    rw [← hres n t10 r1, Int.gcd_eq_natAbs, Int.natAbs_natCast] at h3
    rw [← hres n t20 r2, Int.gcd_eq_natAbs, Int.natAbs_natCast] at h4
    constructor
    · rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
      exact Nat.coprime_mul_iff_right.2 ⟨h1, h3⟩
    · rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
      exact Nat.coprime_mul_iff_right.2 ⟨h2, h4⟩

/-- The phase factorises along the CRT decomposition, with the explicit twists `a` and `b`
coming from a Bézout relation `an + bm = 1`. -/
theorem phase_crt_split {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {a b : ℤ} (hab : a * n + b * m = 1)
    (C : ℤ) (u : ℕ) :
    phase ((u : ℝ) * (C : ℝ) / ((m * n : ℕ) : ℝ))
      = phase (((u % m : ℕ) : ℝ) * ((C * a : ℤ) : ℝ) / (m : ℝ))
        * phase (((u % n : ℕ) : ℝ) * ((C * b : ℤ) : ℝ) / (n : ℝ)) := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  obtain ⟨q1, hq1⟩ : ∃ q : ℕ, u = m * q + u % m := ⟨u / m, (Nat.div_add_mod u m).symm⟩
  obtain ⟨q2, hq2⟩ : ∃ q : ℕ, u = n * q + u % n := ⟨u / n, (Nat.div_add_mod u n).symm⟩
  rw [← phase_add]
  refine phase_congr (C * a * (q1 : ℤ) + C * b * (q2 : ℤ)) ?_
  have habR : (a : ℝ) * (n : ℝ) + (b : ℝ) * (m : ℝ) = 1 := by exact_mod_cast hab
  have hvR : ((u % m : ℕ) : ℝ) = (u : ℝ) - (m : ℝ) * (q1 : ℝ) := by
    have hz := congrArg (fun t : ℕ => (t : ℝ)) hq1
    simp only [Nat.cast_add, Nat.cast_mul] at hz
    linarith
  have hwR : ((u % n : ℕ) : ℝ) = (u : ℝ) - (n : ℝ) * (q2 : ℝ) := by
    have hz := congrArg (fun t : ℕ => (t : ℝ)) hq2
    simp only [Nat.cast_add, Nat.cast_mul] at hz
    linarith
  have hmnR : (((m * n : ℕ)) : ℝ) = (m : ℝ) * (n : ℝ) := by push_cast; ring
  rw [hvR, hwR, hmnR]
  push_cast
  have expand : (u : ℝ) * (C : ℝ) / ((m : ℝ) * (n : ℝ))
      = (u : ℝ) * (C : ℝ) * ((a : ℝ) * (n : ℝ) + (b : ℝ) * (m : ℝ)) / ((m : ℝ) * (n : ℝ)) := by
    rw [habR]; ring
  rw [expand]
  field_simp
  ring

/-- **`DET1-SHAREDG0-PRIMITIVE-U-ROUTER45`, CRT factorisation.**  `LEAN_PROVED`.

For coprime moduli `m, n` and any Bézout pair `an + bm = 1`,

```
U_{mn}(C) = U_m(Ca) · U_n(Cb),
```

with the two twists `a, b` units modulo `m`, resp. `n`.  Iterating this over the primes of a
squarefree `g₀` is exactly the CRT factorisation `U_{g₀,D}(C) = ∏_{p ∣ g₀} U_p`. -/
theorem primitiveUSum_crt_split {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n)
    {a b : ℤ} (hab : a * n + b * m = 1) (t10 t20 r1 r2 C : ℤ) :
    primitiveUSum (m * n) t10 t20 r1 r2 C
      = primitiveUSum m t10 t20 r1 r2 (C * a) * primitiveUSum n t10 t20 r1 r2 (C * b) := by
  classical
  rw [primitiveUSum, primitiveUSum, primitiveUSum, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (i := fun u => (u % m, u % n))
    (j := fun q : ℕ × ℕ => (Nat.chineseRemainder hmn q.1 q.2 : ℕ) % (m * n)) ?_ ?_ ?_ ?_ ?_
  · intro u _
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨Nat.mod_lt _ hm, Nat.mod_lt _ hn⟩
  · intro q _
    rw [Finset.mem_range]
    exact Nat.mod_lt _ (by positivity)
  · intro u hu
    rw [Finset.mem_range] at hu
    show (Nat.chineseRemainder hmn (u % m) (u % n) : ℕ) % (m * n) = u
    have hk1 : (Nat.chineseRemainder hmn (u % m) (u % n) : ℕ) ≡ u % m [MOD m] :=
      (Nat.chineseRemainder hmn (u % m) (u % n)).2.1
    have hk2 : (Nat.chineseRemainder hmn (u % m) (u % n) : ℕ) ≡ u % n [MOD n] :=
      (Nat.chineseRemainder hmn (u % m) (u % n)).2.2
    have hu1 : (Nat.chineseRemainder hmn (u % m) (u % n) : ℕ) ≡ u [MOD m] :=
      hk1.trans (Nat.mod_modEq u m)
    have hu2 : (Nat.chineseRemainder hmn (u % m) (u % n) : ℕ) ≡ u [MOD n] :=
      hk2.trans (Nat.mod_modEq u n)
    have hmod : (Nat.chineseRemainder hmn (u % m) (u % n) : ℕ) ≡ u [MOD m * n] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hmn).1 ⟨hu1, hu2⟩
    have heq : (Nat.chineseRemainder hmn (u % m) (u % n) : ℕ) % (m * n) = u % (m * n) := hmod
    rw [heq, Nat.mod_eq_of_lt hu]
  · rintro ⟨v, w⟩ hq
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hq
    show (((Nat.chineseRemainder hmn v w : ℕ) % (m * n)) % m,
      ((Nat.chineseRemainder hmn v w : ℕ) % (m * n)) % n) = (v, w)
    have hk1 : (Nat.chineseRemainder hmn v w : ℕ) ≡ v [MOD m] :=
      (Nat.chineseRemainder hmn v w).2.1
    have hk2 : (Nat.chineseRemainder hmn v w : ℕ) ≡ w [MOD n] :=
      (Nat.chineseRemainder hmn v w).2.2
    have hm1 : ((Nat.chineseRemainder hmn v w : ℕ) % (m * n)) % m = v := by
      have h1 : ((Nat.chineseRemainder hmn v w : ℕ) % (m * n)) % m
          = (Nat.chineseRemainder hmn v w : ℕ) % m :=
        Nat.mod_mod_of_dvd _ ⟨n, rfl⟩
      have h2 : (Nat.chineseRemainder hmn v w : ℕ) % m = v % m := hk1
      rw [h1, h2, Nat.mod_eq_of_lt hq.1]
    have hm2 : ((Nat.chineseRemainder hmn v w : ℕ) % (m * n)) % n = w := by
      have h1 : ((Nat.chineseRemainder hmn v w : ℕ) % (m * n)) % n
          = (Nat.chineseRemainder hmn v w : ℕ) % n :=
        Nat.mod_mod_of_dvd _ ⟨m, by ring⟩
      have h2 : (Nat.chineseRemainder hmn v w : ℕ) % n = w % n := hk2
      rw [h1, h2, Nat.mod_eq_of_lt hq.2]
    rw [hm1, hm2]
  · intro u _
    by_cases hadm : admissible (m * n) t10 t20 r1 r2 u
    · obtain ⟨h1, h2⟩ := (admissible_mul_iff t10 t20 r1 r2 u).1 hadm
      show (if admissible (m * n) t10 t20 r1 r2 u then _ else _) = _
      rw [if_pos hadm, if_pos h1, if_pos h2]
      exact phase_crt_split hm hn hab C u
    · show (if admissible (m * n) t10 t20 r1 r2 u then _ else _) = _
      rw [if_neg hadm]
      rcases not_and_or.1 (fun h => hadm ((admissible_mul_iff t10 t20 r1 r2 u).2 h)) with h | h
      · rw [if_neg h, zero_mul]
      · rw [if_neg h, mul_zero]

end SharedG0Router
end Erdos287
