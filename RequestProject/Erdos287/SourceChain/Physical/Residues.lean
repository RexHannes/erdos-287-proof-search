import RequestProject.Erdos287.SourceChain.Physical.Packet

/-!
# Erdős #287 — physical source: residues `c_ξ`, `b_{ξ,d}` and the physical prime congruences

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**  Kernel-proved source identities of
`sources/physical_spec.md` §§9–10, under the explicit presieve hypotheses `PhysData.WGood`
and the admissible support `PhysData.Admissible`:

* `cRes_spec`, `cRes_unique`, `cRes_unit` — `c_ξ` is the unique CRT solution mod `f_ξ` of
  `p ≡ 1 (mod a_j W)`, `p ≡ 1 - a_j a_i⁻¹ (mod q_i)`, and `(c_ξ, f_ξ) = 1`;
* `AB_coprime` — `(A_{jℓ}, B_{jℓ}) = 1` (proved, *not* assumed);
* `g_coprime` — `(g_{jℓ}, d) = 1` for `(d, W) = 1`;
* `reduce_iff` — `a_ℓ p ≡ a_ℓ - a_j (mod d) ↔ A_{jℓ} p ≡ B_{jℓ} (mod d)`;
* `bRes_spec`, `bRes_unique`, `bRes_unit` — existence, uniqueness and unit status of
  `b_{ξ,d}` mod `f_ξ d`;
* `base_iff`, `spectator_iff`, `scalar_iff` — for `p = L_j(t) = a_j t + 1`:
  `W ∣ t ↔ p ≡ 1 (mod a_j W)`, `q_i ∣ L_i(t) ↔ p ≡ 1 - a_j a_i⁻¹ (mod q_i)`,
  `d ∣ L_ℓ(t) ↔ A_{jℓ} p ≡ B_{jℓ} (mod d)`;
* `packet_congruence_iff` — **all packet divisibility conditions on `t` together are
  equivalent to the single congruence `L_j(t) ≡ b_{ξ,d} (mod f_ξ d)`.**

No inverse is used without a proved coprimality: every `a⁻¹` is the explicit Bézout
coefficient `Nat.gcdA` and its validity is `gcdA_inv`.
-/

open scoped BigOperators
open Finset

namespace Erdos287.Physical

/-- General form of the inverse lemma: for `(a, m) = 1`, `a x ≡ y ↔ x ≡ y a⁻¹ (mod m)`. -/
theorem mul_congr_iff_inv' {a m : ℕ} (h : Nat.Coprime a m) (x y : ℤ) :
    (a : ℤ) * x ≡ y [ZMOD m] ↔ x ≡ y * Nat.gcdA a m [ZMOD m] := by
  have hu := gcdA_inv h
  constructor
  · intro hx
    calc x = 1 * x := by ring
      _ ≡ (a * Nat.gcdA a m) * x [ZMOD m] := (hu.mul_right x).symm
      _ = Nat.gcdA a m * (a * x) := by ring
      _ ≡ Nat.gcdA a m * y [ZMOD m] := hx.mul_left _
      _ = y * Nat.gcdA a m := by ring
  · intro hx
    calc (a : ℤ) * x ≡ a * (y * Nat.gcdA a m) [ZMOD m] := hx.mul_left _
      _ = y * (a * Nat.gcdA a m) := by ring
      _ ≡ y * 1 [ZMOD m] := hu.mul_left _
      _ = y := by ring

namespace PhysData

variable {P : PhysData}

/-! ### Presieve consequences -/

theorem WGood.coprime_slope (hP : P.WGood) {n : ℕ} (hn : Nat.Coprime n P.W) (i : Fin P.k) :
    Nat.Coprime (P.a i) n := by
  apply Nat.coprime_of_dvd
  intro p hp h1 h2
  have := Nat.dvd_gcd h2 (hP.slope i p hp h1)
  rw [hn] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem WGood.not_dvd_diff (hP : P.WGood) {n : ℕ} (hn : Nat.Coprime n P.W) {i i' : Fin P.k}
    (hii : i ≠ i') {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) : ¬ (p : ℤ) ∣ (P.a i : ℤ) - P.a i' := by
  intro h
  have := Nat.dvd_gcd hpn (hP.diff i i' hii p hp h)
  rw [hn] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- A prime coprime to `W` cannot divide two distinct affine forms at the same `t`. -/
theorem WGood.no_common_prime (hP : P.WGood) {n : ℕ} (hn : Nat.Coprime n P.W) {i i' : Fin P.k}
    (hii : i ≠ i') {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) (t : ℕ) (h1 : p ∣ P.L i t)
    (h2 : p ∣ P.L i' t) : False := by
  apply hP.not_dvd_diff hn (Ne.symm hii) hp hpn
  have e : (P.a i' : ℤ) - P.a i = P.a i' * (P.L i t : ℕ) - P.a i * (P.L i' t : ℕ) := by
    unfold L; push_cast; ring
  rw [e]
  exact dvd_sub (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr h1) _)
    (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr h2) _)

theorem q_coprime_W {ξ : Packet P.k} (hξ : P.Admissible ξ) (i : Fin P.k) :
    Nat.Coprime (P.q ξ i) P.W := by
  obtain ⟨-, -, -, -, -, -, hW, -⟩ := hξ
  exact Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul _ _)
    (Nat.Coprime.mul_left (hW i).1 (hW i).2)

theorem q_pos {ξ : Packet P.k} (hξ : P.Admissible ξ) (i : Fin P.k) : 0 < P.q ξ i := by
  obtain ⟨-, -, -, -, -, hpos, -, -⟩ := hξ
  exact Nat.lcm_pos (hpos i).1 (hpos i).2

theorem q0_coprime_W {ξ : Packet P.k} (hξ : P.Admissible ξ) : Nat.Coprime (P.q0 ξ) P.W :=
  Nat.Coprime.prod_left (fun i _ => q_coprime_W hξ i)

theorem f_pos (hP : P.WGood) {ξ : Packet P.k} (hξ : P.Admissible ξ) : 0 < P.f ξ := by
  unfold f q0
  exact Nat.mul_pos (Nat.mul_pos (hP.a_pos _) hP.W_pos)
    (Finset.prod_pos (fun i _ => q_pos hξ i))

theorem aW_coprime_q (hP : P.WGood) {ξ : Packet P.k} (hξ : P.Admissible ξ) (i : Fin P.k) :
    Nat.Coprime (P.a ξ.j * P.W) (P.q ξ i) :=
  Nat.Coprime.mul_left (hP.coprime_slope (q_coprime_W hξ i) _) (q_coprime_W hξ i).symm

/-! ### `c_ξ` -/

/-- CRT existence for the `c_ξ` system. -/
theorem system_crt (hP : P.WGood) {ξ : Packet P.k} (hξ : P.Admissible ξ) :
    ∃ c : ℕ, c < P.f ξ ∧ ∀ x : ℤ, P.System ξ x ↔ x ≡ c [ZMOD (P.f ξ : ℕ)] := by
  classical
  let s : Finset (Option (Fin P.k)) := insert none ((P.spec ξ).map Function.Embedding.some)
  let m : Option (Fin P.k) → ℕ := fun o => o.elim (P.a ξ.j * P.W) (P.q ξ)
  let r : Option (Fin P.k) → ℤ := fun o => o.elim 1 (P.specRes ξ)
  have hnone : none ∉ (P.spec ξ).map Function.Embedding.some := by simp
  have hprod : ∏ o ∈ s, m o = P.f ξ := by
    simp only [s, Finset.prod_insert hnone, Finset.prod_map]
    simp [m, f, q0, mul_assoc]
  have hpw := hξ.2.2.2.2.2.2.2
  obtain ⟨c, hc, hiff⟩ := crt_int s m r
    (by
      intro o ho
      rcases o with _ | i
      · exact Nat.mul_pos (hP.a_pos _) hP.W_pos
      · exact q_pos hξ i)
    (by
      intro o ho o' ho' hne
      simp only [s, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_map, Set.mem_image,
        Finset.mem_coe] at ho ho'
      rcases o with _ | i <;> rcases o' with _ | i'
      · exact absurd rfl hne
      · exact aW_coprime_q hP hξ i'
      · exact (aW_coprime_q hP hξ i).symm
      · obtain ⟨u, hu, hu'⟩ := ho.resolve_left (by simp)
        obtain ⟨u', hv, hv'⟩ := ho'.resolve_left (by simp)
        simp only [Function.Embedding.some_apply, Option.some.injEq] at hu' hv'
        subst hu' hv'
        exact hpw hu hv (fun h => hne (by rw [h])))
  refine ⟨c, hprod ▸ hc, fun x => ?_⟩
  rw [← hprod, ← hiff]
  constructor
  · rintro ⟨h1, h2⟩ o ho
    simp only [s, Finset.mem_insert, Finset.mem_map] at ho
    rcases ho with rfl | ⟨i, hi, rfl⟩
    · exact h1
    · exact h2 i hi
  · intro h
    exact ⟨h none (Finset.mem_insert_self _ _),
      fun i hi => h (some i) (Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hi))⟩

/-- **`c_ξ` is the CRT residue**: `c_ξ < f_ξ` and the system is equivalent to
`x ≡ c_ξ (mod f_ξ)`. -/
theorem cRes_spec (hP : P.WGood) {ξ : Packet P.k} (hξ : P.Admissible ξ) :
    P.cRes ξ < P.f ξ ∧ ∀ x : ℤ, P.System ξ x ↔ x ≡ P.cRes ξ [ZMOD (P.f ξ : ℕ)] := by
  classical
  obtain ⟨c, hc, hiff⟩ := system_crt hP hξ
  have h : ∃ c, c < P.f ξ ∧ P.System ξ c := ⟨c, hc, (hiff c).2 (Int.ModEq.refl _)⟩
  have hdef : P.cRes ξ = Nat.find h := by unfold cRes; rw [dif_pos h]
  have hs := Nat.find_spec h
  rw [hdef]
  refine ⟨hs.1, fun x => ?_⟩
  have hcc : ((Nat.find h : ℕ) : ℤ) ≡ c [ZMOD (P.f ξ : ℕ)] := (hiff _).1 hs.2
  rw [hiff x]
  exact ⟨fun hx => hx.trans hcc.symm, fun hx => hx.trans hcc⟩

/-- Uniqueness of `c_ξ` in `[0, f_ξ)`. -/
theorem cRes_unique (hP : P.WGood) {ξ : Packet P.k} (hξ : P.Admissible ξ) {c' : ℕ}
    (hc' : c' < P.f ξ) (hs : P.System ξ c') : c' = P.cRes ξ := by
  obtain ⟨hlt, hiff⟩ := cRes_spec hP hξ
  exact Nat.ModEq.eq_of_lt_of_lt ((Int.natCast_modEq_iff).mp ((hiff c').1 hs)) hc' hlt

/-- **`(c_ξ, f_ξ) = 1`.** -/
theorem cRes_unit (hP : P.WGood) {ξ : Packet P.k} (hξ : P.Admissible ξ) :
    Nat.Coprime (P.cRes ξ) (P.f ξ) := by
  obtain ⟨-, hiff⟩ := cRes_spec hP hξ
  have hsys := (hiff (P.cRes ξ)).2 (Int.ModEq.refl _)
  apply Nat.coprime_of_dvd
  intro p hp hpc hpf
  have hpc' : (p : ℤ) ∣ (P.cRes ξ : ℤ) := by exact_mod_cast hpc
  unfold f q0 at hpf
  rcases (Nat.Prime.dvd_mul hp).1 hpf with h1 | h1
  · have h2 : ((P.a ξ.j * P.W : ℕ) : ℤ) ∣ 1 - P.cRes ξ := hsys.1.dvd
    have h3 : (p : ℤ) ∣ 1 - P.cRes ξ := (Int.natCast_dvd_natCast.mpr h1).trans h2
    have h4 : (p : ℤ) ∣ 1 := by simpa using dvd_add h3 hpc'
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h4)
  · obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 h1
    have hcop := q_coprime_W hξ i
    have hai : Nat.Coprime (P.a i) (P.q ξ i) := hP.coprime_slope hcop i
    have h2 := (mul_congr_iff_inv (a' := P.a ξ.j) hai (P.cRes ξ : ℤ)).2 (hsys.2 i hi)
    have h3 : ((P.q ξ i : ℕ) : ℤ) ∣ ((P.a i : ℤ) - P.a ξ.j) - P.a i * P.cRes ξ := h2.dvd
    have h4 : (p : ℤ) ∣ ((P.a i : ℤ) - P.a ξ.j) - P.a i * P.cRes ξ :=
      (Int.natCast_dvd_natCast.mpr hpi).trans h3
    have h5 : (p : ℤ) ∣ (P.a i : ℤ) - P.a ξ.j := by
      have := dvd_add h4 (Dvd.dvd.mul_left hpc' (P.a i : ℤ))
      simpa using this
    have hij : i ≠ ξ.j := (Finset.mem_filter.1 hi).2.1
    exact hP.not_dvd_diff hcop hij hp hpi h5

/-! ### The reduced pair `(A_{jℓ}, B_{jℓ})` -/

theorem g_pos (hP : P.WGood) (ξ : Packet P.k) : 0 < P.g ξ :=
  Nat.gcd_pos_of_pos_left _ (hP.a_pos _)

/-- `a_ℓ = g_{jℓ} A_{jℓ}`. -/
theorem al_eq (ξ : Packet P.k) : (P.a ξ.l : ℤ) = P.g ξ * P.A ξ := by
  unfold A g
  exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm

/-- `a_ℓ - a_j = g_{jℓ} B_{jℓ}`. -/
theorem diff_eq (ξ : Packet P.k) : (P.a ξ.l : ℤ) - P.a ξ.j = P.g ξ * P.B ξ := by
  unfold B
  rw [Int.mul_ediv_cancel']
  unfold g
  exact dvd_sub (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _))
    (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _))

/-- **`(A_{jℓ}, B_{jℓ}) = 1`** (proved from the definition; not assumed). -/
theorem AB_coprime (ξ : Packet P.k) (hpos : 0 < P.a ξ.j) :
    Int.gcd (P.A ξ : ℤ) (P.B ξ) = 1 := by
  have hg : 0 < P.g ξ := Nat.gcd_pos_of_pos_left _ hpos
  have h1 : Int.gcd ((P.g ξ : ℤ) * P.A ξ) ((P.g ξ : ℤ) * P.B ξ) =
      P.g ξ * Int.gcd (P.A ξ : ℤ) (P.B ξ) := by
    rw [Int.gcd_mul_left]; simp
  rw [← al_eq, ← diff_eq] at h1
  have h2 : Int.gcd (P.a ξ.l : ℤ) ((P.a ξ.l : ℤ) - P.a ξ.j) = P.g ξ := by
    rw [Int.gcd_self_sub_right]; unfold g; rw [Int.gcd_natCast_natCast, Nat.gcd_comm]
  rw [h2] at h1
  have : P.g ξ * 1 = P.g ξ * Int.gcd (P.A ξ : ℤ) (P.B ξ) := by rw [mul_one]; exact h1
  exact (Nat.eq_of_mul_eq_mul_left hg this).symm

/-- **`(g_{jℓ}, d) = 1`** for a `W`-coprime scalar divisor `d`. -/
theorem g_coprime (hP : P.WGood) (ξ : Packet P.k) {e : ℕ} (he : Nat.Coprime e P.W) :
    Nat.Coprime (P.g ξ) e :=
  Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) (hP.coprime_slope he ξ.j)

theorem A_coprime (hP : P.WGood) (ξ : Packet P.k) {e : ℕ} (he : Nat.Coprime e P.W) :
    Nat.Coprime (P.A ξ) e :=
  Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _))
    (hP.coprime_slope he ξ.l)

/-- **Reduced scalar congruence** (§10): for `(d, W) = 1`,
`a_ℓ x ≡ a_ℓ - a_j (mod d) ↔ A_{jℓ} x ≡ B_{jℓ} (mod d)`. -/
theorem reduce_iff (hP : P.WGood) (ξ : Packet P.k) {e : ℕ} (he : Nat.Coprime e P.W) (x : ℤ) :
    (P.a ξ.l : ℤ) * x ≡ (P.a ξ.l : ℤ) - P.a ξ.j [ZMOD e] ↔
      (P.A ξ : ℤ) * x ≡ P.B ξ [ZMOD e] := by
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd, diff_eq, al_eq]
  have : (P.g ξ : ℤ) * P.B ξ - P.g ξ * P.A ξ * x = P.g ξ * (P.B ξ - P.A ξ * x) := by ring
  rw [this]
  exact dvd_mul_cancel_coprime (g_coprime hP ξ he) _

/-! ### `b_{ξ,d}` -/

/-- **`b_{ξ,d}` is the CRT residue mod `f_ξ d`.** -/
theorem bRes_spec (hP : P.WGood) {ξ : Packet P.k} (hξ : P.Admissible ξ) {e : ℕ} (he0 : 0 < e)
    (heW : Nat.Coprime e P.W) (hfe : Nat.Coprime (P.f ξ) e) :
    P.bRes ξ e < P.f ξ * e ∧ ∀ x : ℤ,
      (x ≡ P.cRes ξ [ZMOD (P.f ξ : ℕ)] ∧ (P.A ξ : ℤ) * x ≡ P.B ξ [ZMOD (e : ℕ)]) ↔
        x ≡ P.bRes ξ e [ZMOD (P.f ξ * e : ℕ)] := by
  classical
  obtain ⟨b0, hb0, hiff0⟩ := crt_two (f_pos hP hξ) he0 hfe (P.cRes ξ)
    (P.B ξ * Nat.gcdA (P.A ξ) e)
  have hiff : ∀ x : ℤ, (x ≡ P.cRes ξ [ZMOD (P.f ξ : ℕ)] ∧
      (P.A ξ : ℤ) * x ≡ P.B ξ [ZMOD (e : ℕ)]) ↔ x ≡ b0 [ZMOD (P.f ξ * e : ℕ)] := by
    intro x
    rw [← hiff0, mul_congr_iff_inv' (A_coprime hP ξ heW)]
  have h : ∃ b, b < P.f ξ * e ∧ (b : ℤ) ≡ P.cRes ξ [ZMOD (P.f ξ : ℕ)] ∧
      (P.A ξ : ℤ) * b ≡ P.B ξ [ZMOD (e : ℕ)] := ⟨b0, hb0, (hiff b0).2 (Int.ModEq.refl _)⟩
  have hdef : P.bRes ξ e = Nat.find h := by unfold bRes; rw [dif_pos h]
  have hs := Nat.find_spec h
  rw [hdef]
  refine ⟨hs.1, fun x => ?_⟩
  have hbb : ((Nat.find h : ℕ) : ℤ) ≡ b0 [ZMOD (P.f ξ * e : ℕ)] := (hiff _).1 hs.2
  rw [hiff x]
  exact ⟨fun hx => hx.trans hbb.symm, fun hx => hx.trans hbb⟩

/-- Uniqueness of `b_{ξ,d}` in `[0, f_ξ d)`. -/
theorem bRes_unique (hP : P.WGood) {ξ : Packet P.k} (hξ : P.Admissible ξ) {e : ℕ}
    (he0 : 0 < e) (heW : Nat.Coprime e P.W) (hfe : Nat.Coprime (P.f ξ) e) {b' : ℕ}
    (hb' : b' < P.f ξ * e) (h1 : (b' : ℤ) ≡ P.cRes ξ [ZMOD (P.f ξ : ℕ)])
    (h2 : (P.A ξ : ℤ) * b' ≡ P.B ξ [ZMOD (e : ℕ)]) : b' = P.bRes ξ e := by
  obtain ⟨hlt, hiff⟩ := bRes_spec hP hξ he0 heW hfe
  exact Nat.ModEq.eq_of_lt_of_lt ((Int.natCast_modEq_iff).mp ((hiff b').1 ⟨h1, h2⟩)) hb' hlt

/-- **`(b_{ξ,d}, f_ξ d) = 1`.** -/
theorem bRes_unit (hP : P.WGood) {ξ : Packet P.k} (hξ : P.Admissible ξ) {e : ℕ} (he0 : 0 < e)
    (heW : Nat.Coprime e P.W) (hfe : Nat.Coprime (P.f ξ) e) :
    Nat.Coprime (P.bRes ξ e) (P.f ξ * e) := by
  obtain ⟨-, hiff⟩ := bRes_spec hP hξ he0 heW hfe
  obtain ⟨h1, h2⟩ := (hiff (P.bRes ξ e)).2 (Int.ModEq.refl _)
  apply Nat.Coprime.mul_right
  · have := ((Int.natCast_modEq_iff).mp h1).gcd_eq
    rw [Nat.Coprime, this]; exact cRes_unit hP hξ
  · apply Nat.coprime_of_dvd
    intro p hp hpb hpe
    have h3 : ((e : ℕ) : ℤ) ∣ P.B ξ - P.A ξ * P.bRes ξ e := h2.dvd
    have h4 : (p : ℤ) ∣ P.B ξ - P.A ξ * P.bRes ξ e :=
      (Int.natCast_dvd_natCast.mpr hpe).trans h3
    have h5 : (p : ℤ) ∣ P.B ξ := by
      have := dvd_add h4 (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hpb) (P.A ξ : ℤ))
      simpa using this
    have h6 : (p : ℤ) ∣ (P.a ξ.l : ℤ) - P.a ξ.j := by
      rw [diff_eq]; exact Dvd.dvd.mul_left h5 _
    exact hP.not_dvd_diff heW (ne_of_gt hξ.1) hp hpe h6

/-! ### The physical prime `p = L_j(t)` and its congruences (§9) -/

/-- The key affine identity `a_i L_j(t) - (a_i - a_j) = a_j L_i(t)`. -/
theorem affine_shift (i j : Fin P.k) (t : ℕ) :
    (P.a i : ℤ) * (P.L j t : ℕ) - ((P.a i : ℤ) - P.a j) = P.a j * (P.L i t : ℕ) := by
  unfold L; push_cast; ring

/-- For a modulus `m` coprime to `a_j`: `m ∣ L_i(t) ↔ a_i L_j(t) ≡ a_i - a_j (mod m)`. -/
theorem dvd_form_iff {m : ℕ} (i j : Fin P.k) (hm : Nat.Coprime (P.a j) m) (t : ℕ) :
    m ∣ P.L i t ↔ (P.a i : ℤ) * (P.L j t : ℕ) ≡ (P.a i : ℤ) - P.a j [ZMOD m] := by
  rw [Int.modEq_comm, Int.modEq_iff_dvd]
  have : (P.a i : ℤ) * (P.L j t : ℕ) - ((P.a i : ℤ) - P.a j) = P.a j * (P.L i t : ℕ) :=
    affine_shift i j t
  rw [this, dvd_mul_cancel_coprime hm]
  exact Int.natCast_dvd_natCast.symm

/-- `W ∣ t ↔ L_j(t) ≡ 1 (mod a_j W)`. -/
theorem base_iff (hP : P.WGood) (j : Fin P.k) (t : ℕ) :
    P.W ∣ t ↔ ((P.L j t : ℕ) : ℤ) ≡ 1 [ZMOD (P.a j * P.W : ℕ)] := by
  rw [Int.modEq_comm, Int.modEq_iff_dvd]
  have : ((P.L j t : ℕ) : ℤ) - 1 = (P.a j : ℤ) * t := by unfold L; push_cast; ring
  rw [this]
  push_cast
  rw [mul_dvd_mul_iff_left (by exact_mod_cast (hP.a_pos j).ne')]
  exact Int.natCast_dvd_natCast.symm

/-- **Spectator congruence**: `q_i ∣ L_i(t) ↔ L_j(t) ≡ 1 - a_j a_i⁻¹ (mod q_i)`. -/
theorem spectator_iff (hP : P.WGood) {ξ : Packet P.k} (hξ : P.Admissible ξ) (i : Fin P.k)
    (t : ℕ) :
    P.q ξ i ∣ P.L i t ↔ ((P.L ξ.j t : ℕ) : ℤ) ≡ P.specRes ξ i [ZMOD (P.q ξ i : ℕ)] := by
  have hcop := q_coprime_W hξ i
  rw [dvd_form_iff i ξ.j (hP.coprime_slope hcop ξ.j) t]
  exact mul_congr_iff_inv (hP.coprime_slope hcop i) _

/-- **Scalar congruence**: for `(d, W) = 1`, `d ∣ L_ℓ(t) ↔ A_{jℓ} L_j(t) ≡ B_{jℓ} (mod d)`. -/
theorem scalar_iff (hP : P.WGood) (ξ : Packet P.k) {e : ℕ} (he : Nat.Coprime e P.W) (t : ℕ) :
    e ∣ P.L ξ.l t ↔ (P.A ξ : ℤ) * ((P.L ξ.j t : ℕ) : ℤ) ≡ P.B ξ [ZMOD (e : ℕ)] := by
  rw [dvd_form_iff ξ.l ξ.j (hP.coprime_slope he ξ.j) t]
  exact reduce_iff hP ξ he _

/-- **Exact packet congruence.**  For an admissible packet and a scalar divisor `d` with
`(d, W) = 1`, `(d, f_ξ) = 1`: the conditions `W ∣ t`, `q_i ∣ L_i(t)` (all spectators) and
`d ∣ L_ℓ(t)` hold together iff `L_j(t) ≡ b_{ξ,d} (mod f_ξ d)`. -/
theorem packet_congruence_iff (hP : P.WGood) {ξ : Packet P.k} (hξ : P.Admissible ξ) {e : ℕ}
    (he0 : 0 < e) (heW : Nat.Coprime e P.W) (hfe : Nat.Coprime (P.f ξ) e) (t : ℕ) :
    (P.W ∣ t ∧ (∀ i ∈ P.spec ξ, P.q ξ i ∣ P.L i t) ∧ e ∣ P.L ξ.l t) ↔
      ((P.L ξ.j t : ℕ) : ℤ) ≡ P.bRes ξ e [ZMOD (P.f ξ * e : ℕ)] := by
  rw [← (bRes_spec hP hξ he0 heW hfe).2, ← (cRes_spec hP hξ).2, System, base_iff hP,
    scalar_iff hP ξ heW]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, fun i hi => (spectator_iff hP hξ i t).1 (h2 i hi)⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, fun i hi => (spectator_iff hP hξ i t).2 (h2 i hi), h3⟩

end PhysData

end Erdos287.Physical
