import RequestProject.Erdos287.PostV71V87.Positional

/-!
# Erdős #287 — V86 endpoint-anchored CRT (unconditional)

For coprime absent moduli `d, e ≥ 2` of a gap-two word on `[a, M]` the two *oriented CRT
contacts* are the residue classes modulo `de` of

* `x` with `d ∣ x` and `e ∣ x + 1`  (orientation `d → e`), and
* `x` with `e ∣ x` and `d ∣ x + 1`  (orientation `e → d`).

A contact `x` with `a ≤ x` and `x + 1 ≤ M` would be two consecutive omissions.  We prove
the exact **endpoint-anchored theorem** (`endpoint_anchored_crt`):

  `de > M`   or   `M - a < de < 2a`,

valid for every word (no exact mass needed), all endpoint cases included (`a ≤ x`,
`x + 1 ≤ M` are the only constraints; the endpoints themselves are selected).  In fact
`M - a < de` always holds (`window_lt_mul`), and `de ≤ M` forces `de < 2a`.

Consequences:

* `Q_mul_Q_gt_D`        — `Q_p Q_r > M - a` for distinct primes;
* `small_ceiling_unique` / `card_small_ceilings_le_one` — at most one prime has
  `Q_p² ≤ M - a`, i.e. `#{p : Q_p ≤ √(M-a)} ≤ 1`;
* `low_start_chamber`   — if `3a ≤ M + 1` then every coprime absent pair has `de > M`;
* `dyadic_two_sided_saturation` — (exact words, `a > 1`) the window contains an interior
  multiple `y` of `Q_2`, and every such `y` carries the guard `(1,0,1)`;
* `ceiling_annulus`     — every non-exceptional prime has `M - a < Q_p²` and `Q_p ≤ p·M`;
* `owner_disjoint`      — rows of distinct primes `ℓ, ℓ'` with `ℓℓ' > M` are disjoint, and
  a prime `ℓ > M - a` divides at most one window position.

The aggregate rough-part estimate is **not** claimed here (it is OPEN in the ledger).
-/

open scoped BigOperators

namespace Erdos287.PostV71V87

/-- Every residue class modulo `m ≥ 1` meets every interval `[N, N + m)`. -/
theorem exists_residue_in_window {N m : ℕ} (hm : 1 ≤ m) (c : ℕ) :
    ∃ x, N ≤ x ∧ x < N + m ∧ x ≡ c [MOD m] := by
  have hc : c % m ∈ Finset.range m := Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
  rw [← Nat.image_Ico_mod N m] at hc
  obtain ⟨x, hx, hxm⟩ := Finset.mem_image.mp hc
  rw [Finset.mem_Ico] at hx
  exact ⟨x, hx.1, hx.2, hxm⟩

/-- An oriented CRT contact `d → e`: `d ∣ x` and `e ∣ x + 1`. -/
def Contact (d e x : ℕ) : Prop := d ∣ x ∧ e ∣ x + 1

/-- The oriented contact `d → e` exists below `de`. -/
theorem exists_contact {d e : ℕ} (hcop : Nat.Coprime d e) (hd : 1 ≤ d) (he : 1 ≤ e) :
    ∃ r, r < d * e ∧ Contact d e r := by
  let k := Nat.chineseRemainder hcop 0 (e - 1)
  refine ⟨k.1, Nat.chineseRemainder_lt_mul hcop 0 (e - 1) (by omega) (by omega), ?_, ?_⟩
  · exact (Nat.modEq_zero_iff_dvd).1 k.2.1
  · have h2 : k.1 % e = (e - 1) % e := k.2.2
    rw [Nat.mod_eq_of_lt (by omega : e - 1 < e)] at h2
    exact Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, h2]; simp; rw [Nat.sub_add_cancel he]; simp)

/-- Contacts are periodic modulo `de`. -/
theorem contact_of_modEq {d e x r : ℕ} (h : Contact d e r) (hx : x ≡ r [MOD d * e]) :
    Contact d e x := by
  constructor
  · exact (Nat.ModEq.dvd_iff (Nat.ModEq.of_mul_right e hx) (dvd_refl d)).2 h.1
  · exact (Nat.ModEq.dvd_iff (Nat.ModEq.add_right 1 (Nat.ModEq.of_mul_left d hx))
      (dvd_refl e)).2 h.2

/-- The reflected contact: if `r → (d,e)` then `de - 1 - r` is a contact `e → d`. -/
theorem contact_reflect {d e r : ℕ} (h : Contact d e r) (hr : r < d * e) :
    Contact e d (d * e - 1 - r) := by
  obtain ⟨⟨u, hu⟩, ⟨w, hw⟩⟩ := h
  have hw1 : 1 ≤ w := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · subst h0; simp at hw
    · exact h0
  constructor
  · refine ⟨d - w, ?_⟩
    have : d * e - 1 - r = d * e - (r + 1) := by omega
    rw [this, hw, Nat.mul_sub, mul_comm e d]
  · refine ⟨e - u, ?_⟩
    have : d * e - 1 - r + 1 = d * e - r := by omega
    rw [this, hu, Nat.mul_sub]

namespace Word

variable (W : Word)

/-- A contact of two absent moduli cannot sit inside the window. -/
theorem no_contact_in_window {d e x : ℕ} (hd : W.Absent d) (he : W.Absent e)
    (h : Contact d e x) (hx : W.a ≤ x) (hx1 : x + 1 ≤ W.M) : False := by
  rcases W.gap x hx hx1 with h1 | h1
  · exact hd x h1 h.1
  · exact he (x + 1) h1 h.2

/-- **`M - a < de` for every coprime absent pair.** -/
theorem window_lt_mul {d e : ℕ} (hcop : Nat.Coprime d e) (hd : 1 ≤ d) (he : 1 ≤ e)
    (had : W.Absent d) (hae : W.Absent e) : W.M - W.a < d * e := by
  obtain ⟨r, -, hr⟩ := exists_contact hcop hd he
  have hm : 1 ≤ d * e := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨x, hx1, hx2, hxr⟩ := exists_residue_in_window (N := W.a) hm r
  have hc := contact_of_modEq hr hxr
  by_contra hcon
  push_neg at hcon
  exact W.no_contact_in_window had hae hc hx1 (by have := W.a_le_M; omega)

/-- **`de ≤ M` forces `de < 2a`.** -/
theorem mul_lt_two_a {d e : ℕ} (hcop : Nat.Coprime d e) (hd : 1 ≤ d) (he : 1 ≤ e)
    (had : W.Absent d) (hae : W.Absent e) (hle : d * e ≤ W.M) : d * e < 2 * W.a := by
  obtain ⟨r, hrlt, hr⟩ := exists_contact hcop hd he
  have hr' := contact_reflect hr hrlt
  -- both contacts `r` and `de - 1 - r` have `x + 1 ≤ de ≤ M`, so both lie below `a`
  have h1 : r < W.a := by
    by_contra hc; push_neg at hc
    exact W.no_contact_in_window had hae hr hc (by omega)
  have h2 : d * e - 1 - r < W.a := by
    by_contra hc; push_neg at hc
    exact W.no_contact_in_window hae had hr' hc (by omega)
  omega

/-- **V86 endpoint-anchored CRT theorem.**  For coprime absent moduli `d, e ≥ 2`:
`de > M` or `M - a < de < 2a`. -/
theorem endpoint_anchored_crt {d e : ℕ} (hcop : Nat.Coprime d e) (hd : 2 ≤ d) (he : 2 ≤ e)
    (had : W.Absent d) (hae : W.Absent e) :
    W.M < d * e ∨ (W.M - W.a < d * e ∧ d * e < 2 * W.a) := by
  by_cases h : W.M < d * e
  · exact Or.inl h
  · push_neg at h
    exact Or.inr ⟨W.window_lt_mul hcop (by omega) (by omega) had hae,
      W.mul_lt_two_a hcop (by omega) (by omega) had hae h⟩

/-- Ceilings of distinct primes are coprime. -/
theorem Q_coprime {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) :
    Nat.Coprime (W.Q p) (W.Q r) :=
  Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hr).2 hpr)

/-- **`Q_p Q_r > M - a`** for distinct primes `p ≠ r`. -/
theorem Q_mul_Q_gt_D {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) :
    W.D < W.Q p * W.Q r :=
  W.window_lt_mul (W.Q_coprime hp hr hpr) (W.one_lt_Q hp).le (W.one_lt_Q hr).le
    (W.Q_absent hp) (W.Q_absent hr)

/-- A prime is *exceptional* when its ceiling is at most `√(M - a)`, i.e. `Q_p² ≤ M - a`. -/
def Exceptional (p : ℕ) : Prop := W.Q p * W.Q p ≤ W.D

instance : DecidablePred W.Exceptional := fun p => by unfold Exceptional; infer_instance

/-- At most one prime is exceptional. -/
theorem small_ceiling_unique {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hpE : W.Exceptional p) (hrE : W.Exceptional r) : p = r := by
  by_contra hpr
  have h := W.Q_mul_Q_gt_D hp hr hpr
  unfold Exceptional at hpE hrE
  rcases le_total (W.Q p) (W.Q r) with hle | hle
  · have : W.Q p * W.Q r ≤ W.Q r * W.Q r := Nat.mul_le_mul_right _ hle
    omega
  · have : W.Q p * W.Q r ≤ W.Q p * W.Q p := Nat.mul_le_mul_left _ hle
    omega

/-- **`#{p : Q_p ≤ √(M-a)} ≤ 1`** (over any finite set of primes). -/
theorem card_small_ceilings_le_one (S : Finset ℕ) :
    (S.filter (fun p => p.Prime ∧ W.Exceptional p)).card ≤ 1 := by
  refine Finset.card_le_one.2 ?_
  intro p hp r hr
  simp only [Finset.mem_filter] at hp hr
  exact W.small_ceiling_unique hp.2.1 hr.2.1 hp.2.2 hr.2.2

/-- **Low-start chamber.**  If `3a ≤ M + 1`, the second alternative is empty: every coprime
absent pair `d, e ≥ 2` has `de > M`. -/
theorem low_start_chamber (hlow : 3 * W.a ≤ W.M + 1) {d e : ℕ} (hcop : Nat.Coprime d e)
    (hd : 2 ≤ d) (he : 2 ≤ e) (had : W.Absent d) (hae : W.Absent e) : W.M < d * e := by
  rcases W.endpoint_anchored_crt hcop hd he had hae with h | ⟨h1, h2⟩
  · exact h
  · have := W.a_le_M; omega

/-- In the low-start chamber, distinct primes have `Q_p Q_r > M`. -/
theorem low_start_Q_mul_Q_gt_M (hlow : 3 * W.a ≤ W.M + 1) {p r : ℕ} (hp : p.Prime)
    (hr : r.Prime) (hpr : p ≠ r) : W.M < W.Q p * W.Q r :=
  W.low_start_chamber hlow (W.Q_coprime hp hr hpr) (W.one_lt_Q hp) (W.one_lt_Q hr)
    (W.Q_absent hp) (W.Q_absent hr)

/-- Outside the low-start chamber, a pair of ceilings with product at most `M` lies in the
annulus `M - a < Q_p Q_r < 2a`. -/
theorem Q_pair_annulus {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    (hle : W.Q p * W.Q r ≤ W.M) : W.D < W.Q p * W.Q r ∧ W.Q p * W.Q r < 2 * W.a := by
  rcases W.endpoint_anchored_crt (W.Q_coprime hp hr hpr) (W.one_lt_Q hp) (W.one_lt_Q hr)
    (W.Q_absent hp) (W.Q_absent hr) with h | h
  · omega
  · exact h

/-- A prime larger than the window length divides at most one window position. -/
theorem large_prime_unique_multiple {ℓ x y : ℕ} (hℓ : W.D < ℓ)
    (hx : W.a ≤ x ∧ x ≤ W.M) (hy : W.a ≤ y ∧ y ≤ W.M) (hxd : ℓ ∣ x) (hyd : ℓ ∣ y) :
    x = y := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := Nat.le_of_dvd (by omega) (Nat.dvd_sub hyd hxd)
    unfold D at hℓ; omega
  · have := Nat.le_of_dvd (by omega) (Nat.dvd_sub hxd hyd)
    unfold D at hℓ; omega

/-- **Owner-disjointness.**  Selected rows of distinct primes `ℓ ≠ ℓ'` with `ℓ ℓ' > M` are
disjoint: a selected element has at most one such large prime owner. -/
theorem owner_disjoint {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ')
    (hbig : W.M < ℓ * ℓ') : Disjoint (W.selRow ℓ) (W.selRow ℓ') := by
  rw [Finset.disjoint_left]
  intro n hn hn'
  simp only [selRow, Finset.mem_filter] at hn hn'
  have hcop : Nat.Coprime ℓ ℓ' := (Nat.coprime_primes hℓ hℓ').2 hne
  have hd := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hn.2 hn'.2
  have := Nat.le_of_dvd (W.pos_of_mem hn.1) hd
  have := (W.mem_Icc hn.1).2
  omega

/-- A prime `ℓ ≥ 3` divides at most one element of a guard triple `(y-1, y, y+1)`. -/
theorem guard_triple_owner_unique {ℓ y u w : ℕ} (hℓ : 3 ≤ ℓ)
    (hu : y ≤ u + 1 ∧ u ≤ y + 1) (hw : y ≤ w + 1 ∧ w ≤ y + 1) (hud : ℓ ∣ u) (hwd : ℓ ∣ w) :
    u = w := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := Nat.le_of_dvd (by omega) (Nat.dvd_sub hwd hud); omega
  · have := Nat.le_of_dvd (by omega) (Nat.dvd_sub hud hwd); omega

end Word

namespace ExactWord

variable (W : ExactWord)

/-- **Dyadic two-sided saturation.**  For an exact word with `a > 1` the window contains a
multiple `y` of the dyadic ceiling `Q_2`, it is interior, and both its neighbours are
selected; moreover every multiple of `Q_2` in the window carries the guard `(1,0,1)`. -/
theorem dyadic_two_sided_saturation (ha : 1 < W.a) :
    (∃ y, W.Q 2 ∣ y ∧ W.a < y ∧ y < W.M ∧ y - 1 ∈ W.A ∧ y ∉ W.A ∧ y + 1 ∈ W.A) ∧
    (∀ y, W.Q 2 ∣ y → W.a ≤ y → y ≤ W.M →
      W.x (y - 1) = true ∧ W.x y = false ∧ W.x (y + 1) = true) := by
  refine ⟨?_, fun y hy h1 h2 => W.guard_pattern (W.Q_absent Nat.prime_two) hy ⟨h1, h2⟩⟩
  have hQ := W.Q_two_le_D ha
  have hQ1 := W.one_lt_Q Nat.prime_two
  obtain ⟨y, hy1, hy2, hyr⟩ := exists_residue_in_window (N := W.a) (m := W.Q 2) (by omega) 0
  have hdy : W.Q 2 ∣ y := (Nat.modEq_zero_iff_dvd).1 hyr
  have hwin : W.a ≤ y ∧ y ≤ W.M := ⟨hy1, by unfold Word.D at hQ; have := W.a_le_M; omega⟩
  have hom := W.forced_omitted (W.Q_absent Nat.prime_two) hdy
  have hi := W.interior_of_omitted hwin hom
  have hn := W.neighbours_of_omitted hwin hom
  exact ⟨y, hdy, hi.1, hi.2, hn.1, hom, hn.2⟩

/-- **Primary-ceiling annulus.**  Every non-exceptional prime has `M - a < Q_p²`, and every
prime has `Q_p ≤ p · M`. -/
theorem ceiling_annulus {p : ℕ} (hp : p.Prime) (hne : ¬ W.Exceptional p) :
    W.D < W.Q p * W.Q p ∧ W.Q p ≤ p * W.M := by
  refine ⟨by unfold Word.Exceptional at hne; omega, ?_⟩
  rw [W.Q_eq_mul]
  refine Nat.mul_le_mul_left _ ?_
  obtain ⟨n, hn⟩ := W.layer_nonempty p
  exact le_trans (Nat.le_of_dvd (W.pos_of_mem (W.mem_of_mem_layer hn))
    (W.P_dvd_of_mem_layer hp hn)) (W.mem_Icc (W.mem_of_mem_layer hn)).2

end ExactWord

end Erdos287.PostV71V87
