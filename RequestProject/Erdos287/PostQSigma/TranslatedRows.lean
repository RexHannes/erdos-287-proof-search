import RequestProject.Erdos287.PostQSigma.FirstDigit

/-!
# Erdős #287 — post-`Q_Σ` bank, §14 (translated first-digit rows) and §5 (V54 exact identity)

**Status: BANK (proved in Lean).**

## Translated rows

For the first-digit layer of `p` (`q = p^e ‖ W`, raw source) the physical cofactor row is
`cofInt a M q = {k : a < qk < M}`, which begins at `⌊a/q⌋ + 1`, not necessarily at `1`.
Since `W/(qk) ≡ (W/q)·k⁻¹ (mod p)` with `W/q ≢ 0`, zero-sum subsets of the layer are exactly
zero-sum subsets of the reciprocal row `{k⁻¹ mod p}`.

* `RecipZSF p K` — no nonempty `G ⊆ K` has `∑_{k∈G} k⁻¹ ≡ 0 (mod p)` (hereditary);
* `translated_row_zero_sum_free` — a certified reciprocal interval `K ⊇ cofInt a M q` makes the
  physical layer zero-sum free;
* `translated_row_mandatory` — together with `S ≠ ∅` and `η = 0`, the layer is **mandatory**;
* `prefix_row_mandatory` — prefix rows `K = [1, m]` as the special case.
* Regression fixture (`p = 7`, `a = 27`, `M = 43`): the physical row is `{4,5,6}`
  (`fixture_cofInt`); the translated row is certified (`fixture_translated_ok`) while the prefix
  row `[1,6]` is not (`fixture_prefix_fails`, `1⁻¹ + 6⁻¹ ≡ 0`).

The large certificate chains up to `10^18`/`10^24` are validation only and are not used.

## V54 source-qualification identity

`source_qualification` — if the omitted set `D = [a,M] \ A` splits disjointly as compulsory
deletions `R` and optional omissions `E`, then `|E ∩ U| = |D ∩ U| - |R ∩ U|` for every window `U`.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

open Erdos287.ExactSource

variable {a M p : ℕ}

/-- Reciprocal zero-sum-freeness of a cofactor row modulo `p`. -/
def RecipZSF (p : ℕ) (K : Finset ℕ) : Prop :=
  ∀ G ∈ K.powerset, G.Nonempty → ∑ k ∈ G, ((k : ZMod p))⁻¹ ≠ 0

instance (p : ℕ) (K : Finset ℕ) : Decidable (RecipZSF p K) := by
  unfold RecipZSF; infer_instance

lemma RecipZSF.mono {K K' : Finset ℕ} (h : RecipZSF p K) (hK : K' ⊆ K) : RecipZSF p K' :=
  fun G hG hne => h G (Finset.mem_powerset.2 ((Finset.mem_powerset.1 hG).trans hK)) hne

/-- **Translated-row theorem**: a certified reciprocal row containing the actual physical
cofactor row makes the first-digit layer zero-sum free. -/
theorem translated_row_zero_sum_free (ha : 0 < a) (hp : p.Prime) (he : 1 ≤ eW a M ∅ p)
    {K : Finset ℕ} (hK : cofInt a M (p ^ eW a M ∅ p) ⊆ K) (hcert : RecipZSF p K) :
    ∀ G ⊆ S a M ∅ p 1, G.Nonempty → ∑ n ∈ G, res a M ∅ p 1 n ≠ 0 := by
  classical
  haveI := Fact.mk hp
  intro G hG hne hzero
  set q := p ^ eW a M ∅ p
  have hq : 0 < q := pow_pos hp.pos _
  have hS : S a M ∅ p 1 = (cofInt a M q).image (fun k => q * k) := by
    rw [S_empty_eq_cofactor_image hp, qpd_one he]
  rw [hS] at hG
  obtain ⟨G', hG', rfl⟩ := Finset.subset_image_iff.1 hG
  have hinj : Set.InjOn (fun k => q * k) (G' : Set ℕ) :=
    fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hq h
  rw [sum_res_one_eq_zero_iff, Finset.sum_image hinj] at hzero
  have hmemB : ∀ k ∈ G', q * k ∈ B a M ∅ := by
    intro k hk
    have h := (Finset.mem_filter.1 (hG' hk)).2
    exact mem_B.2 ⟨by omega, by omega, by simp⟩
  have hw : ((W a M ∅ / q : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact not_dvd_W_div_top ha hp
  have hterm : ∀ k ∈ G', ((W a M ∅ / (q * k) : ℕ) : ZMod p) =
      ((W a M ∅ / q : ℕ) : ZMod p) * ((k : ZMod p))⁻¹ := by
    intro k hk
    have hk0 : (k : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact not_dvd_cofactor ha hp (hmemB k hk)
    rw [← cast_W_div_mul ha (hmemB k hk), mul_assoc, mul_inv_cancel₀ hk0, mul_one]
  have hz : ((∑ k ∈ G', W a M ∅ / (q * k) : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hzero
  rw [Nat.cast_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hz
  have hne' : G'.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨k, hk, -⟩ := Finset.mem_image.1 hx
    exact ⟨k, hk⟩
  exact hcert G' (Finset.mem_powerset.2 ((Finset.coe_subset.1 hG').trans hK)) hne'
    ((mul_eq_zero.1 hz).resolve_left hw)

/-- **Mandatory conclusion from a translated-row certificate.** -/
theorem translated_row_mandatory (ha : 0 < a) (hp : p.Prime) (he : 1 ≤ eW a M ∅ p)
    {K : Finset ℕ} (hK : cofInt a M (p ^ eW a M ∅ p) ⊆ K) (hcert : RecipZSF p K)
    (hne : (cofInt a M (p ^ eW a M ∅ p)).Nonempty) (heta : eta a M ∅ p 1 = 0) :
    Mandatory a M ∅ p 1 := by
  refine (mandatory_iff_local ha hp he).2 ⟨?_, heta, translated_row_zero_sum_free ha hp he hK hcert⟩
  rw [S_nonempty_iff_cofactor hp, qpd_one he]; exact hne

/-- Prefix rows `[1, m]` as a special case. -/
theorem prefix_row_mandatory (ha : 0 < a) (hp : p.Prime) (he : 1 ≤ eW a M ∅ p) {m : ℕ}
    (hK : cofInt a M (p ^ eW a M ∅ p) ⊆ Finset.Icc 1 m) (hcert : RecipZSF p (Finset.Icc 1 m))
    (hne : (cofInt a M (p ^ eW a M ∅ p)).Nonempty) (heta : eta a M ∅ p 1 = 0) :
    Mandatory a M ∅ p 1 :=
  translated_row_mandatory ha hp he hK hcert hne heta

/-! ### Regression fixture: translated row succeeds where the prefix fails -/

/-- The physical row of `q = 7` in `(27, 43)` is `{4, 5, 6}`. -/
theorem fixture_cofInt : cofInt 27 43 7 = {4, 5, 6} := by decide

/-- The translated reciprocal row `{4,5,6}` is zero-sum free mod `7`. -/
theorem fixture_translated_ok : RecipZSF 7 {4, 5, 6} := by decide

/-- The prefix row `[1, 6]` is **not** zero-sum free mod `7` (`1⁻¹ + 6⁻¹ ≡ 0`). -/
theorem fixture_prefix_fails : ¬ RecipZSF 7 (Finset.Icc 1 6) := by decide

/-! ### V54 source-qualification identity -/

/-- **Source qualification**: `|E ∩ U| = |D ∩ U| - |R ∩ U|` when `D = R ⊔ E`. -/
theorem source_qualification (D R E U : Finset ℕ) (hD : D = R ∪ E) (hdisj : Disjoint R E) :
    (E ∩ U).card = (D ∩ U).card - (R ∩ U).card := by
  classical
  have : D ∩ U = (R ∩ U) ∪ (E ∩ U) := by rw [hD, Finset.union_inter_distrib_right]
  rw [this, Finset.card_union_of_disjoint
    (Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left hdisj))]
  omega

end Erdos287.PostQSigma
