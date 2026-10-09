import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Contact-core route — the complete proper-power row, layer counting and the valuation lift

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For a prime base `ℓ` and a cofactor interval `C = [A, N] ∩ ℤ` with `J = lcm C` and `t = v_ℓ(J)`,
the **complete proper-power row condition** (PP-ROW) is

`∑_{c ∈ C} ε_c · (J / c) ≡ 0  (mod ℓ^{t+1})`.

This is `PPRow` below.  It is *not* the naive unit-inverse congruence modulo `ℓ`:
`ppRow_ne_naive` exhibits a selection satisfying the naive condition and violating PP-ROW.

The file also banks the exact interval counting used by the proper-power obstruction dichotomy:

* `layerCount_le` : `D_v ≤ 2 n_v + 5`, where `D_v = #{c ∈ C : ℓ^v ∣ c}` and `n_v` counts the
  cofactors of exact valuation `v`;
* `sparse_layer_bound` : `n_v < 2ℓ ⟹ D_v ≤ 6ℓ` (the sparse `p`-adic tail);
* `deficient_layer_bound` : `n_v ≤ ℓ - 1 ⟹ D_v ≤ 4ℓ` (the raw forced-zero port cap);
* `heavy_layer_majority` : `n_v ≥ 2ℓ` and `|P ∩ C_v| ≥ n_v - (ℓ-2)` force `|P ∩ C_v| > n_v / 2`.

Finally `valuationLift_*` records the exact valuation lift `q d = h d₀`, `h = ℓ^{e₀+v}`, together
with the floor identity `⌊⌊M/q⌋/ℓ^v⌋ = ⌊M/h⌋`.
-/

namespace Erdos287
namespace ResearchBankV5
namespace ContactCore

open Finset

/-! ## 1.  Counting multiples in an interval -/

/-- The number of multiples of `k` in the integer interval `[A, N]`. -/
def mulCount (A N k : ℕ) : ℕ := ((Finset.Icc A N).filter (fun c => k ∣ c)).card

/-- Upper bound for the number of multiples of `k` in `[A, N]`. -/
theorem mulCount_le (A N k : ℕ) : mulCount A N k ≤ N / k - A / k + 1 := by
  classical
  unfold mulCount
  have himg : ((Finset.Icc A N).filter (fun c => k ∣ c)).image (fun c => c / k)
      ⊆ Finset.Icc (A / k) (N / k) := by
    intro m hm
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨c, ⟨⟨hA, hN⟩, _⟩, rfl⟩ := hm
    exact Finset.mem_Icc.2 ⟨Nat.div_le_div_right hA, Nat.div_le_div_right hN⟩
  have hinj : Set.InjOn (fun c => c / k) ((Finset.Icc A N).filter (fun c => k ∣ c)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    obtain ⟨-, hdx⟩ := hx
    obtain ⟨-, hdy⟩ := hy
    have hxy' : x / k = y / k := hxy
    calc x = k * (x / k) := (Nat.mul_div_cancel' hdx).symm
    _ = k * (y / k) := by rw [hxy']
    _ = y := Nat.mul_div_cancel' hdy
  have hcard := Finset.card_le_card himg
  rw [Finset.card_image_of_injOn hinj, Nat.card_Icc] at hcard
  omega

/-- Lower bound for the number of multiples of `k` in `[A, N]`. -/
theorem mulCount_ge (A N k : ℕ) (hk : 0 < k) : N / k - A / k ≤ mulCount A N k := by
  classical
  unfold mulCount
  have hsub : (Finset.Icc (A / k + 1) (N / k)).image (fun m => k * m)
      ⊆ (Finset.Icc A N).filter (fun c => k ∣ c) := by
    intro c hc
    simp only [Finset.mem_image, Finset.mem_Icc] at hc
    obtain ⟨m, ⟨hm1, hm2⟩, rfl⟩ := hc
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨?_, ?_⟩, ⟨m, rfl⟩⟩
    · have h1 : k * (A / k) + A % k = A := Nat.div_add_mod A k
      have h2 : A % k < k := Nat.mod_lt _ hk
      have h3 : A < k * (A / k + 1) := by
        have hexp : k * (A / k + 1) = k * (A / k) + k := by ring
        omega
      exact le_of_lt (lt_of_lt_of_le h3 (Nat.mul_le_mul_left k hm1))
    · rw [mul_comm]; exact Nat.mul_le_of_le_div k m N hm2
  have hinj : Set.InjOn (fun m => k * m) (Finset.Icc (A / k + 1) (N / k)) := by
    intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left hk hxy
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Nat.card_Icc] at hcard
  omega

/-! ## 2.  Valuation layers of the cofactor interval -/

/-- `D_v` : the number of cofactors in `[A, N]` divisible by `ℓ^v`. -/
def layerCount (A N ℓ v : ℕ) : ℕ := mulCount A N (ℓ ^ v)

/-- `n_v` : the number of cofactors in `[A, N]` of *exact* `ℓ`-valuation `v`. -/
def exactLayerCount (A N ℓ v : ℕ) : ℕ :=
  ((Finset.Icc A N).filter (fun c => ℓ ^ v ∣ c ∧ ¬ ℓ ^ (v + 1) ∣ c)).card

/-- The layer splitting `D_{v+1} + n_v = D_v`. -/
theorem layer_split (A N ℓ v : ℕ) :
    layerCount A N ℓ (v + 1) + exactLayerCount A N ℓ v = layerCount A N ℓ v := by
  classical
  have hmono : ∀ c : ℕ, ℓ ^ (v + 1) ∣ c → ℓ ^ v ∣ c := by
    intro c hc
    exact dvd_trans (pow_dvd_pow ℓ (Nat.le_succ v)) hc
  have h1 : ((Finset.Icc A N).filter (fun c => ℓ ^ v ∣ c)).filter (fun c => ℓ ^ (v + 1) ∣ c)
      = (Finset.Icc A N).filter (fun c => ℓ ^ (v + 1) ∣ c) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun c _ => by
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨hmono c h, h⟩
  have h2 : ((Finset.Icc A N).filter (fun c => ℓ ^ v ∣ c)).filter (fun c => ¬ ℓ ^ (v + 1) ∣ c)
      = (Finset.Icc A N).filter (fun c => ℓ ^ v ∣ c ∧ ¬ ℓ ^ (v + 1) ∣ c) := by
    rw [Finset.filter_filter]
  have := Finset.card_filter_add_card_filter_not
    (s := (Finset.Icc A N).filter (fun c => ℓ ^ v ∣ c)) (p := fun c => ℓ ^ (v + 1) ∣ c)
  rw [h1, h2] at this
  simpa [layerCount, exactLayerCount, mulCount] using this

private theorem le_add_sub_aux (a b : ℕ) : a ≤ b + (a - b) := by omega

private theorem add_div_le_aux (x y ℓ : ℕ) (hℓ : 0 < ℓ) : (x + y) / ℓ ≤ x / ℓ + y / ℓ + 1 := by
  rw [Nat.add_div hℓ]
  split <;> simp

private theorem layer_arith {D D1 n A1 B1 A2 B2 q ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (hDge : B1 - A1 ≤ D) (hDle : D ≤ B1 - A1 + 1) (hD1le : D1 ≤ B2 - A2 + 1)
    (hstep : B2 ≤ A2 + q + 1) (hsum : D1 + n = D) (hqℓ : q * ℓ ≤ B1 - A1) :
    D ≤ 2 * n + 5 := by
  have hq2 : q * 2 ≤ q * ℓ := Nat.mul_le_mul_left q hℓ
  have hWq : B1 - A1 ≤ q + n + 2 := by omega
  have hqn : q ≤ n + 2 := by linarith
  omega

/-- **Master layer bound.**  `D_v ≤ 2 n_v + 5` for any base `ℓ ≥ 2`: a valuation layer with few
elements of exact valuation `v` contains few multiples of `ℓ^v` altogether. -/
theorem layerCount_le (A N ℓ v : ℕ) (hℓ : 2 ≤ ℓ) :
    layerCount A N ℓ v ≤ 2 * exactLayerCount A N ℓ v + 5 := by
  have hℓ0 : 0 < ℓ := by omega
  have hkpos : 0 < ℓ ^ v := pow_pos hℓ0 v
  have hDge : N / ℓ ^ v - A / ℓ ^ v ≤ layerCount A N ℓ v := mulCount_ge A N (ℓ ^ v) hkpos
  have hDle : layerCount A N ℓ v ≤ N / ℓ ^ v - A / ℓ ^ v + 1 := mulCount_le A N (ℓ ^ v)
  have hk1 : ℓ ^ (v + 1) = ℓ ^ v * ℓ := pow_succ ℓ v
  have hNdiv : N / ℓ ^ (v + 1) = N / ℓ ^ v / ℓ := by rw [hk1, Nat.div_div_eq_div_mul]
  have hAdiv : A / ℓ ^ (v + 1) = A / ℓ ^ v / ℓ := by rw [hk1, Nat.div_div_eq_div_mul]
  have hD1le : layerCount A N ℓ (v + 1) ≤ N / ℓ ^ v / ℓ - A / ℓ ^ v / ℓ + 1 := by
    have h := mulCount_le A N (ℓ ^ (v + 1))
    rw [hNdiv, hAdiv] at h
    exact h
  have hstep : N / ℓ ^ v / ℓ ≤ A / ℓ ^ v / ℓ + (N / ℓ ^ v - A / ℓ ^ v) / ℓ + 1 := by
    refine le_trans (Nat.div_le_div_right (le_add_sub_aux (N / ℓ ^ v) (A / ℓ ^ v))) ?_
    exact add_div_le_aux _ _ ℓ hℓ0
  have hqℓ : (N / ℓ ^ v - A / ℓ ^ v) / ℓ * ℓ ≤ N / ℓ ^ v - A / ℓ ^ v :=
    Nat.div_mul_le_self _ _
  exact layer_arith hℓ hDge hDle hD1le hstep (layer_split A N ℓ v) hqℓ

/-- **Sparse `p`-adic tail.**  If the layer of exact valuation `v` has fewer than `2ℓ` cofactors,
then `D_v ≤ 6ℓ`. -/
theorem sparse_layer_bound (A N ℓ v : ℕ) (hℓ : 2 ≤ ℓ)
    (hn : exactLayerCount A N ℓ v < 2 * ℓ) : layerCount A N ℓ v ≤ 6 * ℓ := by
  have := layerCount_le A N ℓ v hℓ
  omega

/-- **Deficient layer.**  If the layer of exact valuation `v` has at most `ℓ - 1` cofactors, then
`D_v ≤ 4ℓ`. -/
theorem deficient_layer_bound (A N ℓ v : ℕ) (hℓ : 2 ≤ ℓ)
    (hn : exactLayerCount A N ℓ v ≤ ℓ - 1) : layerCount A N ℓ v ≤ 4 * ℓ := by
  have := layerCount_le A N ℓ v hℓ
  omega

/-- **Heavy layer.**  If a valuation layer is heavy (`n_v ≥ 2ℓ`) and the required-selected set
already meets it in at least `n_v - (ℓ - 2)` positions, then it occupies a strict majority of the
layer. -/
theorem heavy_layer_majority (nv x ℓ : ℕ) (hℓ : 2 ≤ ℓ) (hheavy : 2 * ℓ ≤ nv)
    (hx : nv - (ℓ - 2) ≤ x) : nv < 2 * x := by omega

/-! ## 3.  Raw forced-zero ports -/

/-- A valuation layer is **deficient** when it carries at most `ℓ - 1` cofactors of exact
valuation `v`. -/
def DeficientLayer (A N ℓ v : ℕ) : Prop := exactLayerCount A N ℓ v ≤ ℓ - 1

/-- **(RAW-PP).**  All cofactors of valuation at least the first deficient level `v✱` live in the
layer `D_{v✱}`, whose cardinality is at most `4ℓ`.  Hence at most `4ℓ` raw forced-zero ports can
occur in one base-`ℓ` proper-power row. -/
theorem rawPort_cap (A N ℓ vstar : ℕ) (hℓ : 2 ≤ ℓ) (hdef : DeficientLayer A N ℓ vstar) :
    ((Finset.Icc A N).filter (fun c => ℓ ^ vstar ∣ c)).card ≤ 4 * ℓ :=
  deficient_layer_bound A N ℓ vstar hℓ hdef

/-- If no valuation layer is deficient up to level `v`, then every layer up to `v` carries at least
`ℓ` cofactors of exact valuation, so no raw forced-zero port can be produced there. -/
theorem no_deficient_layer_no_port (A N ℓ : ℕ) (hno : ∀ v, ¬ DeficientLayer A N ℓ v) (v : ℕ) :
    ℓ ≤ exactLayerCount A N ℓ v := by
  have := hno v
  unfold DeficientLayer at this
  omega

/-! ## 4.  The complete proper-power row condition -/

/-- The cofactor interval `C = [A, N] ∩ ℤ`. -/
def cofactorInterval (A N : ℕ) : Finset ℕ := Finset.Icc A N

/-- `J = lcm C`. -/
def rowLcm (A N : ℕ) : ℕ := (cofactorInterval A N).lcm id

/-- `t = v_ℓ(J)`. -/
noncomputable def rowExp (ℓ A N : ℕ) : ℕ := padicValNat ℓ (rowLcm A N)

/-- **(PP-ROW).**  The complete proper-power row condition
`∑_{c ∈ C} ε_c (J/c) ≡ 0 (mod ℓ^{t+1})`. -/
noncomputable def PPRow (ℓ A N : ℕ) (ε : ℕ → ℤ) : Prop :=
  ((ℓ : ℤ) ^ (rowExp ℓ A N + 1)) ∣ ∑ c ∈ cofactorInterval A N, ε c * ((rowLcm A N / c : ℕ) : ℤ)

/-- The naive (and **insufficient**) unit-inverse condition modulo `ℓ`. -/
def NaiveRow (ℓ A N : ℕ) (ε : ℕ → ℤ) : Prop :=
  (ℓ : ℤ) ∣ ∑ c ∈ cofactorInterval A N, ε c * ((rowLcm A N / c : ℕ) : ℤ)

/-- `J = lcm [1,2] = 2`. -/
theorem rowLcm_one_two : rowLcm 1 2 = 2 := by decide

/-- `t = v₂(2) = 1`. -/
theorem rowExp_one_two : rowExp 2 1 2 = 1 := by
  unfold rowExp
  rw [rowLcm_one_two]
  exact padicValNat.self (by norm_num)

/-- **PP-ROW is strictly stronger than the naive congruence.**  With `ℓ = 2`, `C = [1,2]`,
`J = 2`, `t = 1`, the selection `ε₁ = 1, ε₂ = 0` satisfies the naive condition modulo `2` but
violates the complete row condition modulo `4`. -/
theorem ppRow_ne_naive :
    ∃ (ℓ A N : ℕ) (ε : ℕ → ℤ), NaiveRow ℓ A N ε ∧ ¬ PPRow ℓ A N ε := by
  refine ⟨2, 1, 2, fun c => if c = 1 then 1 else 0, ?_, ?_⟩
  · unfold NaiveRow cofactorInterval
    rw [rowLcm_one_two]
    norm_num [Finset.sum_Icc_succ_top]
  · unfold PPRow cofactorInterval
    rw [rowExp_one_two, rowLcm_one_two]
    norm_num [Finset.sum_Icc_succ_top]

/-! ## 5.  The valuation lift -/

/-- **Valuation lift, multiplicative part.**  For a proper-power owner `q = ℓ^{e₀}` and terminal
cofactor `d = ℓ^v d₀`, the lifted owner `h = ℓ^{e₀+v}` satisfies `q d = h d₀`. -/
theorem valuationLift_mul (ℓ e₀ v d₀ : ℕ) :
    ℓ ^ e₀ * (ℓ ^ v * d₀) = ℓ ^ (e₀ + v) * d₀ := by
  rw [pow_add]; ring

/-- **Valuation lift, floor part.**  `⌊⌊M/q⌋ / ℓ^v⌋ = ⌊M/h⌋` for `q = ℓ^{e₀}`, `h = ℓ^{e₀+v}`. -/
theorem valuationLift_floor (M ℓ e₀ v : ℕ) :
    M / ℓ ^ e₀ / ℓ ^ v = M / ℓ ^ (e₀ + v) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]

/-- Consequently `d₀` is the genuine unit cofactor for the lifted owner `h`: it is prime to `ℓ`
and bounded by the lifted height. -/
theorem valuationLift_unit_cofactor {M ℓ e₀ v d₀ : ℕ} (hd : ¬ ℓ ∣ d₀)
    (hbound : ℓ ^ v * d₀ ≤ M / ℓ ^ e₀) (hℓ : 0 < ℓ) :
    ¬ ℓ ∣ d₀ ∧ d₀ ≤ M / ℓ ^ (e₀ + v) := by
  refine ⟨hd, ?_⟩
  rw [← valuationLift_floor]
  exact Nat.le_div_iff_mul_le (pow_pos hℓ v) |>.2 (by rw [mul_comm] at hbound; exact hbound)

end ContactCore
end ResearchBankV5
end Erdos287
