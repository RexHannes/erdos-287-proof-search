import RequestProject.Erdos287.PostV64V71.ResidualDenominator

/-!
# Erdős #287 — V70/V71 determinant tuples

**Status: BANK (LEAN PROVED).**

A determinant tuple is `x = (k, q, t, r, ε) ∈ ℕ × ℕ × ℕ × ℕ × ℤ` with

* `1 ≤ k ≤ H`, `1 ≤ t ≤ H`, `⌊M/H⌋ < q ≤ M`, `⌊M/H⌋ < r ≤ M`, `ε ∈ {1, -1}`;
* `k q - t r = ε` (in `ℤ`), i.e. `det [[k, t], [r, q]] = ε = ±1`;
* `M/2 < k q < 3M/4` (as `M < 2kq` and `4kq < 3M`).

`detBox M H` is the finite set of such tuples (`q, r` are *integer* variables; primality is
carried by the weights in `ExceptionAccounting.lean`).

* `det_eq` — `Matrix.det !![k, t; r, q] = k q - t r`;
* `rough_factor_iff_determinant_tuple` — **V70 parametrisation**: a prime `r > M/H`, `r ≤ M`,
  divides a forced neighbour `kq - ε` of a good multiple iff there is `t` with `1 ≤ t ≤ H` and
  `kq - tr = ε`;
* `owner_multiplicity_le_twoH_r`, `owner_multiplicity_le_twoH_q` — **V71**: for a fixed prime
  owner, at most `2H` tuples with prime partner (needs `M < (⌊M/H⌋+1)²`);
* `good_tuple_excludes` — **terminal source step**: a tuple whose two owners are both good
  primes (`∤ Ξ_H`) yields two adjacent omissions `kq`, `tr` in `[N, M]`: contradiction.
-/

open scoped BigOperators

namespace Erdos287.PostV64V71

open Erdos287

/-- A determinant tuple `(k, q, t, r, ε)`. -/
abbrev DTup := ℕ × ℕ × ℕ × ℕ × ℤ

/-- `k`-coordinate. -/
abbrev DTup.k (x : DTup) : ℕ := x.1
/-- `q`-coordinate (first owner). -/
abbrev DTup.q (x : DTup) : ℕ := x.2.1
/-- `t`-coordinate. -/
abbrev DTup.t (x : DTup) : ℕ := x.2.2.1
/-- `r`-coordinate (second owner). -/
abbrev DTup.r (x : DTup) : ℕ := x.2.2.2.1
/-- sign `ε`. -/
abbrev DTup.eps (x : DTup) : ℤ := x.2.2.2.2

/-- The V70/V71 determinant box. -/
def detBox (M H : ℕ) : Finset DTup :=
  (Finset.Icc 1 H ×ˢ Finset.Ioc (M / H) M ×ˢ Finset.Icc 1 H ×ˢ Finset.Ioc (M / H) M ×ˢ
      ({1, -1} : Finset ℤ)).filter
    (fun x => ((x.1 * x.2.1 : ℕ) : ℤ) - ((x.2.2.1 * x.2.2.2.1 : ℕ) : ℤ) = x.2.2.2.2 ∧
      M < 2 * (x.1 * x.2.1) ∧ 4 * (x.1 * x.2.1) < 3 * M)

theorem mem_detBox {M H : ℕ} {x : DTup} :
    x ∈ detBox M H ↔
      (1 ≤ x.k ∧ x.k ≤ H) ∧ (M / H < x.q ∧ x.q ≤ M) ∧ (1 ≤ x.t ∧ x.t ≤ H) ∧
      (M / H < x.r ∧ x.r ≤ M) ∧ (x.eps = 1 ∨ x.eps = -1) ∧
      (((x.k * x.q : ℕ) : ℤ) - ((x.t * x.r : ℕ) : ℤ) = x.eps ∧
        M < 2 * (x.k * x.q) ∧ 4 * (x.k * x.q) < 3 * M) := by
  obtain ⟨k, q, t, r, e⟩ := x
  simp [detBox, and_assoc]

/-- `det [[k, t], [r, q]] = k q - t r`. -/
theorem det_eq (k t r q : ℤ) : Matrix.det !![k, t; r, q] = k * q - t * r := by
  rw [Matrix.det_fin_two_of]

/-- Basic arithmetic facts of a box tuple: `t r = k q - ε` with both sides in `[1, M]`. -/
theorem detBox_facts {M H : ℕ} {x : DTup} (hx : x ∈ detBox M H) :
    1 ≤ x.t * x.r ∧ x.t * x.r ≤ M ∧ 1 ≤ x.k * x.q ∧ x.k * x.q + 1 ≤ M ∧
      ((x.t * x.r : ℕ) : ℤ) = (x.k * x.q : ℕ) - x.eps := by
  rw [mem_detBox] at hx
  obtain ⟨⟨hk1, hkH⟩, ⟨hq1, hqM⟩, ⟨ht1, htH⟩, ⟨hr1, hrM⟩, he, hdet, hlo, hhi⟩ := hx
  have hq0 : 1 ≤ x.q := lt_of_le_of_lt (Nat.zero_le _) hq1
  have hr0 : 1 ≤ x.r := lt_of_le_of_lt (Nat.zero_le _) hr1
  have hkq : 1 ≤ x.k * x.q := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have htr : 1 ≤ x.t * x.r := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  refine ⟨htr, ?_, hkq, by omega, by linarith⟩
  have : ((x.t * x.r : ℕ) : ℤ) ≤ (x.k * x.q : ℕ) + 1 := by rcases he with h | h <;> omega
  have h2 : x.k * x.q + 1 ≤ M := by omega
  omega

/-! ## V70 determinant parametrisation -/

/-- The data of a forced neighbour `kq - ε` of a good multiple (relative to an exception set
`E`): `q` prime, `M/H < q ≤ M`, `q ∉ E`, `1 ≤ k ≤ H`, `M/2 < kq < 3M/4`, `ε = ±1`. -/
def ForcedData (M H : ℕ) (E : Finset ℕ) (k q : ℕ) (ε : ℤ) : Prop :=
  q.Prime ∧ (M / H < q ∧ q ≤ M) ∧ q ∉ E ∧ (1 ≤ k ∧ k ≤ H) ∧
    M < 2 * (k * q) ∧ 4 * (k * q) < 3 * M ∧ (ε = 1 ∨ ε = -1)

/-- **V70 rough factor ⟺ determinant tuple.**  Let `0 < H` and let `r` be a prime with
`M/H < r ≤ M`.  Then `r` divides a forced neighbour `kq - ε` iff `kq - tr = ε` for some `t`
with `1 ≤ t ≤ H`. -/
theorem rough_factor_iff_determinant_tuple {M H : ℕ} (hH : 0 < H) (E : Finset ℕ) {r : ℕ}
    (hr : r.Prime) (hrM : M / H < r) :
    (∃ k q : ℕ, ∃ ε : ℤ, ForcedData M H E k q ε ∧ (r : ℤ) ∣ ((k * q : ℕ) : ℤ) - ε) ↔
      (∃ k q t : ℕ, ∃ ε : ℤ, ForcedData M H E k q ε ∧ (1 ≤ t ∧ t ≤ H) ∧
        ((k * q : ℕ) : ℤ) - ((t * r : ℕ) : ℤ) = ε) := by
  constructor
  · rintro ⟨k, q, ε, hF, c, hc⟩
    obtain ⟨-, -, -, -, hlo, hhi, he⟩ := id hF
    have hr0 : (0 : ℤ) < r := by exact_mod_cast hr.pos
    have hkq2 : 2 ≤ k * q := by omega
    have hpos : (0 : ℤ) < ((k * q : ℕ) : ℤ) - ε := by
      rcases he with rfl | rfl <;> push_cast <;> omega
    have hc0 : 0 < c := by
      by_contra h; push_neg at h
      have : (r : ℤ) * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0.le h
      linarith
    have hrH : M < r * H := lt_mul_of_div_lt hH hrM
    have hle : ((k * q : ℕ) : ℤ) - ε ≤ M := by rcases he with rfl | rfl <;> push_cast <;> omega
    refine ⟨k, q, c.toNat, ε, hF, ⟨by omega, ?_⟩, ?_⟩
    · -- `t r ≤ M < r H`
      have h1 : (r : ℤ) * c ≤ M := hc ▸ hle
      have h2 : ((M : ℕ) : ℤ) < (r : ℤ) * H := by exact_mod_cast hrH
      have h3 : c < H := by
        by_contra h; push_neg at h
        have : (r : ℤ) * H ≤ r * c := mul_le_mul_of_nonneg_left h hr0.le
        linarith
      omega
    · have hct : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg hc0.le
      rw [Nat.cast_mul (c.toNat) r, hct]
      linarith [hc, mul_comm (r : ℤ) c]
  · rintro ⟨k, q, t, ε, hF, -, h⟩
    refine ⟨k, q, ε, hF, ⟨t, ?_⟩⟩
    push_cast at h ⊢
    linarith

/-! ## V71 owner multiplicity `≤ 2H` -/

/-- Two distinct primes `> y` cannot both divide `n` when `n < (y+1)²`. -/
theorem prime_dvd_unique {y n q q' : ℕ} (hn : n < (y + 1) ^ 2) (hq : q.Prime) (hq' : q'.Prime)
    (hyq : y < q) (hyq' : y < q') (hqn : q ∣ n) (hqn' : q' ∣ n) (hn0 : n ≠ 0) : q = q' := by
  by_contra hne
  have hcop : Nat.Coprime q q' := (Nat.coprime_primes hq hq').2 hne
  have hdvd : q * q' ∣ n := hcop.mul_dvd_of_dvd_of_dvd hqn hqn'
  have hle : q * q' ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
  have : (y + 1) ^ 2 ≤ q * q' := by
    rw [sq]; exact Nat.mul_le_mul hyq hyq'
  omega

/-- **V71 owner multiplicity (second owner fixed).**  If `M < (⌊M/H⌋+1)²`, then for every `r₀`
at most `2H` box tuples have `r = r₀` and prime first owner `q`. -/
theorem owner_multiplicity_le_twoH_r {M H : ℕ} (hy : M < (M / H + 1) ^ 2) (r₀ : ℕ) :
    ((detBox M H).filter (fun x => x.r = r₀ ∧ x.q.Prime)).card ≤ 2 * H := by
  set S := (detBox M H).filter (fun x => x.r = r₀ ∧ x.q.Prime)
  have hmaps : ∀ x ∈ S, (x.t, x.eps) ∈ Finset.Icc 1 H ×ˢ ({1, -1} : Finset ℤ) := by
    intro x hx
    have hx' := (Finset.mem_filter.1 hx).1
    rw [mem_detBox] at hx'
    simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hx'.2.2.1, hx'.2.2.2.2.1⟩
  have hinj : Set.InjOn (fun x : DTup => (x.t, x.eps)) S := by
    intro x hx x' hx' hxx
    simp only [Prod.mk.injEq] at hxx
    obtain ⟨htt, hee⟩ := hxx
    have hxS := Finset.mem_filter.1 hx
    have hxS' := Finset.mem_filter.1 hx'
    have f1 := detBox_facts hxS.1
    have f2 := detBox_facts hxS'.1
    have m1 := mem_detBox.1 hxS.1
    have m2 := mem_detBox.1 hxS'.1
    -- the common value `n = t r₀ + ε = k q = k' q'`
    have hkq : x.k * x.q = x'.k * x'.q := by
      have e1 := f1.2.2.2.2; have e2 := f2.2.2.2.2
      rw [hxS.2.1] at e1; rw [hxS'.2.1, ← htt, ← hee] at e2
      have : ((x.k * x.q : ℕ) : ℤ) = ((x'.k * x'.q : ℕ) : ℤ) := by linarith
      exact_mod_cast this
    have hqq : x.q = x'.q := by
      refine prime_dvd_unique (y := M / H) (n := x.k * x.q) (by have := f1.2.2.2.1; omega)
        hxS.2.2 hxS'.2.2 m1.2.1.1 m2.2.1.1 (dvd_mul_left _ _) (hkq ▸ dvd_mul_left _ _)
        (by have := f1.2.2.1; omega)
    have hkk : x.k = x'.k := by
      rw [hqq] at hkq
      exact Nat.eq_of_mul_eq_mul_right (lt_of_le_of_lt (Nat.zero_le _) m2.2.1.1) hkq
    have hrr : x.r = x'.r := hxS.2.1.trans hxS'.2.1.symm
    obtain ⟨k, q, t, r, e⟩ := x
    obtain ⟨k', q', t', r', e'⟩ := x'
    simp only at hkk hqq htt hrr hee
    subst hkk hqq htt hrr hee
    rfl
  calc S.card ≤ (Finset.Icc 1 H ×ˢ ({1, -1} : Finset ℤ)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ H * 2 := by
        rw [Finset.card_product]; simp only [Nat.card_Icc, add_tsub_cancel_right]
        exact Nat.mul_le_mul_left _ (Finset.card_le_two)
    _ = 2 * H := mul_comm _ _

/-- **V71 owner multiplicity (first owner fixed).**  If `M < (⌊M/H⌋+1)²`, then for every `q₀`
at most `2H` box tuples have `q = q₀` and prime second owner `r`. -/
theorem owner_multiplicity_le_twoH_q {M H : ℕ} (hy : M < (M / H + 1) ^ 2) (q₀ : ℕ) :
    ((detBox M H).filter (fun x => x.q = q₀ ∧ x.r.Prime)).card ≤ 2 * H := by
  set S := (detBox M H).filter (fun x => x.q = q₀ ∧ x.r.Prime)
  have hmaps : ∀ x ∈ S, (x.k, x.eps) ∈ Finset.Icc 1 H ×ˢ ({1, -1} : Finset ℤ) := by
    intro x hx
    have hx' := (Finset.mem_filter.1 hx).1
    rw [mem_detBox] at hx'
    simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hx'.1, hx'.2.2.2.2.1⟩
  have hinj : Set.InjOn (fun x : DTup => (x.k, x.eps)) S := by
    intro x hx x' hx' hxx
    simp only [Prod.mk.injEq] at hxx
    obtain ⟨hkk, hee⟩ := hxx
    have hxS := Finset.mem_filter.1 hx
    have hxS' := Finset.mem_filter.1 hx'
    have f1 := detBox_facts hxS.1
    have f2 := detBox_facts hxS'.1
    have m1 := mem_detBox.1 hxS.1
    have m2 := mem_detBox.1 hxS'.1
    have hqq : x.q = x'.q := hxS.2.1.trans hxS'.2.1.symm
    have htr : x.t * x.r = x'.t * x'.r := by
      have e1 := f1.2.2.2.2; have e2 := f2.2.2.2.2
      rw [← hkk, ← hqq, ← hee] at e2
      have : ((x.t * x.r : ℕ) : ℤ) = ((x'.t * x'.r : ℕ) : ℤ) := by linarith
      exact_mod_cast this
    have hrr : x.r = x'.r := by
      refine prime_dvd_unique (y := M / H) (n := x.t * x.r) (by have := f1.2.1; omega)
        hxS.2.2 hxS'.2.2 m1.2.2.2.1.1 m2.2.2.2.1.1 (dvd_mul_left _ _) (htr ▸ dvd_mul_left _ _)
        (by have := f1.1; omega)
    have htt : x.t = x'.t := by
      rw [hrr] at htr
      exact Nat.eq_of_mul_eq_mul_right (lt_of_le_of_lt (Nat.zero_le _) m2.2.2.2.1.1) htr
    obtain ⟨k, q, t, r, e⟩ := x
    obtain ⟨k', q', t', r', e'⟩ := x'
    simp only at hkk hqq htt hrr hee
    subst hkk hqq htt hrr hee
    rfl
  calc S.card ≤ (Finset.Icc 1 H ×ˢ ({1, -1} : Finset ℤ)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ H * 2 := by
        rw [Finset.card_product]; simp only [Nat.card_Icc, add_tsub_cancel_right]
        exact Nat.mul_le_mul_left _ (Finset.card_le_two)
    _ = 2 * H := mul_comm _ _

/-! ## Terminal source step -/

namespace Gap2CE

variable (ce : Erdos287.Gap2CE)

/-- **Good tuple ⇒ contradiction.**  If some box tuple (for `M = max A`, `M ≥ 4`) has both
owners `q, r` prime and good (`q ∤ Ξ_H`, `r ∤ Ξ_H`), then `kq` and `tr` are both omitted,
`|kq - tr| = 1`, and both lie in `[N, M]`: two adjacent omissions, contradiction. -/
theorem good_tuple_excludes (hM : 4 ≤ ce.M) {H : ℕ} (hH : 0 < H) {x : DTup}
    (hx : x ∈ detBox ce.M H) (hq : x.q.Prime) (hr : x.r.Prime)
    (hqXi : ¬ x.q ∣ Xi H) (hrXi : ¬ x.r ∣ Xi H) : False := by
  have m := mem_detBox.1 hx
  have f := detBox_facts hx
  have hN := two_mul_N_le_M ce hM
  have h1 : x.k * x.q ∉ ce.A :=
    all_good_multiples_omitted ce hq (lt_mul_of_div_lt hH m.2.1.1) hqXi (dvd_mul_left _ _)
  have h2 : x.t * x.r ∉ ce.A :=
    all_good_multiples_omitted ce hr (lt_mul_of_div_lt hH m.2.2.2.1.1) hrXi (dvd_mul_left _ _)
  have hlo := m.2.2.2.2.2.2.1
  rcases m.2.2.2.2.1 with he | he
  · -- `t r = k q - 1`
    have htr : x.t * x.r + 1 = x.k * x.q := by
      have := f.2.2.2.2; rw [he] at this; omega
    exact ce.blockerPair_contradiction (x := x.t * x.r) (by omega) (by omega) h2 (htr ▸ h1)
  · -- `t r = k q + 1`
    have htr : x.t * x.r = x.k * x.q + 1 := by
      have := f.2.2.2.2; rw [he] at this; omega
    exact ce.blockerPair_contradiction (x := x.k * x.q) (by omega) (by omega) h1 (htr ▸ h2)

end Gap2CE

end Erdos287.PostV64V71
