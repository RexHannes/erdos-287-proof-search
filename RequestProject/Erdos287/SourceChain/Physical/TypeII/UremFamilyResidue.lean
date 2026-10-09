import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilyFinite

/-!
# Erdős #287 — the exact residue rearrangement of the literal `h_l U_r` term

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

`inner_urem_eq_relDisc` is the identity (5.1) of the family repair, proved for the literal inner
sum of `physUrem`:

`∑_{v < K'} (α * β)(v) 1_{v ≡ c (f)} h_l(v) U_r(v)
   = φ(r)⁻¹ ∑_{m ∼ M} β_m 1_{(m, f l r) = 1} Δ^{f, c m̄}_{α^{(r)}}(l, B (A m)⁻¹)`,

where `α^{(r)}_n = α_n 1_{(n,r)=1}`, `m̄` is the inverse of `m` modulo `f` and `(A m)⁻¹` the inverse
modulo `l`.  Hypotheses: `(c, f) = 1` and `(A · |B|, l) = 1` (the latter is supplied for the actual
packets by the presieve, `physData_affinePrimesDivideBase`).  No inverse of `A` modulo `f` is used.

`sum_occupancy_le` is (5.2): for a nonnegative function `g` of the residue pair, the sum over
`m ∈ [M, 2M)` with `(m, f l) = 1` of `g(c m̄, B (A m)⁻¹)` is at most `(M/(f l) + 1)` times the sum of
`g` over all unit pairs, because the map `m ↦ (c m̄, B (Am)⁻¹)` is injective on unit classes
modulo `f l`.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII.UremFamily

open Erdos287.Physical.TypeII

/-- The residue `c m̄ mod f` (as a natural number `< f`). -/
noncomputable def cRes (f c m : ℕ) : ℕ := ((c : ZMod f) * (m : ZMod f)⁻¹).val

/-- The residue `B (A m)⁻¹ mod l` (as a natural number `< l`). -/
noncomputable def aRes (l A : ℕ) (B : ℤ) (m : ℕ) : ℕ := ((B : ZMod l) * ((A * m : ℕ) : ZMod l)⁻¹).val

/-- The masked sequence `α^{(r)}_n = α_n 1_{(n,r)=1}`. -/
noncomputable def maskR (α : ℕ → ℝ) (r : ℕ) (n : ℕ) : ℝ :=
  α n * (if Nat.Coprime n r then 1 else 0)

/-- `1_{(m, q) = 1}`. -/
noncomputable def copInd (m q : ℕ) : ℝ := if Nat.Coprime m q then 1 else 0

lemma resMask_mul {f c : ℕ} (hf : 0 < f) (hcf : Nat.Coprime c f) (m n : ℕ) :
    resMask f c (m * n) = copInd m f * ind f (cRes f c m) n := by
  haveI : NeZero f := ⟨hf.ne'⟩
  unfold resMask copInd ind cRes
  by_cases hm : Nat.Coprime m f
  · have key : m * n ≡ c [MOD f] ↔ n ≡ ((c : ZMod f) * (m : ZMod f)⁻¹).val [MOD f] := by
      rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val,
        Nat.cast_mul]
      have hu := ZMod.coe_mul_inv_eq_one m hm
      constructor
      · intro h; rw [← h]
        calc (n : ZMod f) = n * (m * (m : ZMod f)⁻¹) := by rw [hu, mul_one]
          _ = _ := by ring
      · intro h; rw [h]
        calc (m : ZMod f) * (c * (m : ZMod f)⁻¹) = c * (m * (m : ZMod f)⁻¹) := by ring
          _ = c := by rw [hu, mul_one]
    rw [if_pos hm, one_mul]; simp only [key]
  · simp only [hm, if_false, zero_mul]
    rw [if_neg]
    intro h
    apply hm
    have := Nat.ModEq.gcd_eq h
    rw [Nat.Coprime.gcd_eq_one hcf] at this
    exact Nat.Coprime.coprime_mul_right this

lemma Iz_mul_eq {l A : ℕ} {B : ℤ} (hl : 0 < l) (hAB : Nat.Coprime (A * B.natAbs) l) (m n : ℕ) :
    Iz A B l (m * n) = copInd m l * ind l (aRes l A B m) n := by
  haveI : NeZero l := ⟨hl.ne'⟩
  have hA : Nat.Coprime A l := Nat.Coprime.coprime_mul_right hAB
  have hBn : Nat.Coprime B.natAbs l := Nat.Coprime.coprime_mul_left hAB
  have hBu : IsUnit (B : ZMod l) := by
    rcases Int.natAbs_eq B with e | e
    · rw [e, Int.cast_natCast]; exact (ZMod.isUnit_iff_coprime _ _).2 hBn
    · rw [e, Int.cast_neg, Int.cast_natCast]; exact ((ZMod.isUnit_iff_coprime _ _).2 hBn).neg
  have hcond : ((A : ℤ) * ((m * n : ℕ) : ℤ) ≡ B [ZMOD l]) ↔
      ((A * m : ℕ) : ZMod l) * n = (B : ZMod l) := by
    rw [← ZMod.intCast_eq_intCast_iff]; push_cast; ring_nf
  unfold Iz copInd ind aRes
  rw [if_congr hcond rfl rfl]
  by_cases hm : Nat.Coprime m l
  · have hAm : Nat.Coprime (A * m) l := Nat.Coprime.mul_left hA hm
    have hu := ZMod.coe_mul_inv_eq_one (A * m) hAm
    have key : ((A * m : ℕ) : ZMod l) * n = (B : ZMod l) ↔
        n ≡ ((B : ZMod l) * ((A * m : ℕ) : ZMod l)⁻¹).val [MOD l] := by
      rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
      constructor
      · intro h; rw [← h]
        calc (n : ZMod l) = n * (((A * m : ℕ) : ZMod l) * ((A * m : ℕ) : ZMod l)⁻¹) := by
              rw [hu, mul_one]
          _ = _ := by ring
      · intro h; rw [h]
        calc ((A * m : ℕ) : ZMod l) * ((B : ZMod l) * ((A * m : ℕ) : ZMod l)⁻¹) =
            (B : ZMod l) * (((A * m : ℕ) : ZMod l) * ((A * m : ℕ) : ZMod l)⁻¹) := by ring
          _ = B := by rw [hu, mul_one]
    rw [if_pos hm, one_mul]; simp only [key]
  · simp only [hm, if_false, zero_mul]
    rw [if_neg]
    intro h
    apply hm
    have h1 : IsUnit (((A * m : ℕ) : ZMod l) * n) := h ▸ hBu
    have h2 : IsUnit ((A * m : ℕ) : ZMod l) := isUnit_of_mul_isUnit_left h1
    rw [ZMod.isUnit_iff_coprime] at h2
    exact Nat.Coprime.coprime_mul_left h2

lemma Uz_mul_left (r m n : ℕ) : Uz r (m * n) = copInd m r * Uz r n := by
  unfold Uz copInd
  simp only [Nat.coprime_mul_iff_left]
  split_ifs <;> first | (exfalso; tauto) | ring

/-- **(5.1) Exact residue rearrangement** of the literal inner `h_l U_r` sum. -/
theorem inner_urem_eq_relDisc (α β : ArithmeticFunction ℝ) {N M K' : ℕ}
    (hα : ∀ n, α n ≠ 0 → N ≤ n ∧ n < 2 * N) (hβ : ∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M)
    (hK' : 4 * N * M ≤ K') {f c l A r : ℕ} {B : ℤ} (hf : 0 < f) (hl : 0 < l)
    (hcf : Nat.Coprime c f) (hAB : Nat.Coprime (A * B.natAbs) l) :
    ∑ v ∈ range K', (α * β) v * (resMask f c v * (hz A B l v * Uz r v)) =
      (1 / (Nat.totient r : ℝ)) * ∑ m ∈ Ico M (2 * M), β m * copInd m (f * l * r) *
        relDisc (Ico N (2 * N)) (maskR α r) f (cRes f c m) l (aRes l A B m) := by
  rw [sum_conv_dyadic α β hα hβ hK', sum_comm]
  unfold relDisc maskR
  rw [mul_sum]
  refine sum_congr rfl (fun m _ => ?_)
  rw [mul_sum, mul_sum]
  refine sum_congr rfl (fun n _ => ?_)
  unfold hz
  rw [resMask_mul hf hcf, Iz_mul_eq hl hAB, Uz_mul_left, Uz_mul_left]
  have e : copInd m (f * l * r) = copInd m f * copInd m l * copInd m r := by
    unfold copInd
    simp only [Nat.coprime_mul_iff_right]
    split_ifs <;> first | (exfalso; tauto) | ring
  rw [e]
  have eU : Uz r n = (if Nat.Coprime n r then 1 else 0) * (1 / (Nat.totient r : ℝ)) := by
    unfold Uz; split_ifs <;> simp
  rw [eU]
  unfold copInd
  split_ifs <;> ring

end Erdos287.Physical.TypeII.UremFamily
