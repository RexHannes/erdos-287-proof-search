import RequestProject.Erdos287.PostQSigma.HardCore

/-!
# Erdős #287 — post-`Q_Σ` bank, §28 (V63): root-of-unity filter, conductors, Ramanujan blocks

**Status: BANK (proved in Lean).**  Every statement is an exact identity; no absolute values
are taken across conductors.

Abstract setting: a finite family `Ω`, integer masses `B : α → ℤ`, target `T`, modulus `W > 0`,
`X(E) = B(E) - T`, `e_W(x) = exp(2πi x / W)`, `Z(r) = ∑_{E} e_W(r B(E))`.

* `sum_ee` — orthogonality `∑_{r<n} e_n(r x) = n·[n ∣ x]`;
* `fourier_filter` — `W · #{E : W ∣ X(E)} = ∑_{r<W} e_W(-rT) Z(r)`;
* `conductor_decomposition` — `∑_{d ∣ W} A_d(T) = ∑_{r<W} e_W(-rT) Z(r)`, where
  `A_d(T)` sums over the `r` of additive conductor `W/gcd(r,W) = d`;
* `A_one` — `A_1(T) = |Ω|` (the total path-word count `P`);
* `A_eq_sum_c`, `cW_eq_ramanujan` — `A_d(T) = ∑_E c_d(X(E))` with `c_d` the genuine Ramanujan
  sum `∑_{k<d, (k,d)=1} e_d(k m)`;
* `divisor_block_identity` — `∑_{d ∣ Q} A_d(T) = Q · N_Q(T)` for `Q ∣ W`.

Physical instances (`R = ∅`, domain `1 ≤ H < 2`): `root_of_unity_exact_coefficient`
(`W · N_T = ∑_r e_W(-rT) Z(r)`), `physical_conductor_decomposition`
(`W · N_T = ∑_{d∣W} A_d(T)`), `physical_ramanujan_block_identity`.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

open Complex

/-- `e_n(x) = exp(2πi x / n)`. -/
noncomputable def ee (n : ℕ) (x : ℤ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x / n)

lemma ee_add (n : ℕ) (x y : ℤ) : ee n (x + y) = ee n x * ee n y := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma ee_zero (n : ℕ) : ee n 0 = 1 := by simp [ee]

lemma ee_eq_zpow (n : ℕ) (x : ℤ) :
    ee n x = Complex.exp (2 * Real.pi * Complex.I / n) ^ x := by
  unfold ee
  rw [← Complex.exp_int_mul]; congr 1; ring

lemma ee_scale {s d : ℕ} (hs : 0 < s) (x : ℤ) : ee (s * d) (s * x) = ee d x := by
  unfold ee; congr 1
  have : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  push_cast
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp

/-- **Orthogonality**: `∑_{r<n} e_n(r x) = n · [n ∣ x]`. -/
theorem sum_ee {n : ℕ} (hn : 0 < n) (x : ℤ) :
    ∑ r ∈ Finset.range n, ee n ((r : ℤ) * x) = if (n : ℤ) ∣ x then (n : ℂ) else 0 := by
  have hprim := Complex.isPrimitiveRoot_exp n hn.ne'
  set z := Complex.exp (2 * Real.pi * Complex.I / n) with hz
  have hterm : ∀ r : ℕ, ee n ((r : ℤ) * x) = (z ^ x) ^ r := by
    intro r; rw [ee_eq_zpow, ← hz, mul_comm, zpow_mul, zpow_natCast]
  simp_rw [hterm]
  split_ifs with h
  · have : z ^ x = 1 := (hprim.zpow_eq_one_iff_dvd x).2 h
    simp [this]
  · have hne : z ^ x ≠ 1 := fun h' => h ((hprim.zpow_eq_one_iff_dvd x).1 h')
    rw [geom_sum_eq hne]
    have : (z ^ x) ^ n = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hprim.pow_eq_one,
        one_zpow]
    rw [this]; simp

section Abstract

variable {α : Type*} (Ω : Finset α) (Bf : α → ℤ) (T : ℤ) (W : ℕ)

/-- `Z(r) = ∑_{E∈Ω} e_W(r B(E))`. -/
noncomputable def Zsum (r : ℕ) : ℂ := ∑ E ∈ Ω, ee W ((r : ℤ) * Bf E)

/-- The additive conductor of `r` modulo `W`: `W / gcd(r, W)`. -/
def cond (r : ℕ) : ℕ := W / Nat.gcd r W

/-- `A_d(T) = ∑_{r<W, cond(r) = d} e_W(-rT) Z(r)`. -/
noncomputable def Acond (d : ℕ) : ℂ :=
  ∑ r ∈ (Finset.range W).filter (fun r => cond W r = d), ee W (-((r : ℤ) * T)) * Zsum Ω Bf W r

/-- The fibre Ramanujan sum `c_d(m) = ∑_{r<W, cond(r)=d} e_W(r m)`. -/
noncomputable def cW (d : ℕ) (m : ℤ) : ℂ :=
  ∑ r ∈ (Finset.range W).filter (fun r => cond W r = d), ee W ((r : ℤ) * m)

/-- The genuine Ramanujan sum `c_d(m) = ∑_{k<d, gcd(k,d)=1} e_d(k m)`. -/
noncomputable def ramanujan (d : ℕ) (m : ℤ) : ℂ :=
  ∑ k ∈ (Finset.range d).filter (fun k => Nat.Coprime k d), ee d ((k : ℤ) * m)

lemma term_eq (r : ℕ) (E : α) :
    ee W (-((r : ℤ) * T)) * ee W ((r : ℤ) * Bf E) = ee W ((r : ℤ) * (Bf E - T)) := by
  rw [← ee_add]; congr 1; ring

/-- The general unfolding `∑_{r ∈ s} e_W(-rT) Z(r) = ∑_E ∑_{r∈s} e_W(r X(E))`. -/
lemma sum_swap (s : Finset ℕ) :
    ∑ r ∈ s, ee W (-((r : ℤ) * T)) * Zsum Ω Bf W r =
      ∑ E ∈ Ω, ∑ r ∈ s, ee W ((r : ℤ) * (Bf E - T)) := by
  unfold Zsum
  simp_rw [Finset.mul_sum, term_eq]
  rw [Finset.sum_comm]

open Classical in
/-- **Exact root-of-unity filter**: `W · #{E : W ∣ X(E)} = ∑_{r<W} e_W(-rT) Z(r)`. -/
theorem fourier_filter (hW : 0 < W) :
    (W : ℂ) * ((Ω.filter (fun E => (W : ℤ) ∣ Bf E - T)).card : ℂ) =
      ∑ r ∈ Finset.range W, ee W (-((r : ℤ) * T)) * Zsum Ω Bf W r := by
  rw [sum_swap]
  simp_rw [sum_ee hW]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

lemma cond_mem_divisors (hW : 0 < W) (r : ℕ) : cond W r ∈ W.divisors := by
  rw [Nat.mem_divisors]
  exact ⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_right r W), hW.ne'⟩

/-- **Conductor decomposition**: `∑_{d∣W} A_d(T) = ∑_{r<W} e_W(-rT) Z(r)`. -/
theorem conductor_decomposition (hW : 0 < W) :
    ∑ d ∈ W.divisors, Acond Ω Bf T W d =
      ∑ r ∈ Finset.range W, ee W (-((r : ℤ) * T)) * Zsum Ω Bf W r := by
  unfold Acond
  exact Finset.sum_fiberwise_of_maps_to (fun r _ => cond_mem_divisors W hW r) _

/-- `A_1(T) = |Ω|` (the conductor-one block is the total count `P`). -/
theorem A_one (hW : 0 < W) : Acond Ω Bf T W 1 = Ω.card := by
  unfold Acond
  have : (Finset.range W).filter (fun r => cond W r = 1) = {0} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, cond]
    constructor
    · rintro ⟨hr, h1⟩
      have hg : Nat.gcd r W = W := by
        have hgd := Nat.gcd_dvd_right r W
        have hgpos : 0 < Nat.gcd r W := Nat.gcd_pos_of_pos_right r hW
        have := Nat.div_mul_cancel hgd
        rw [h1, one_mul] at this
        exact this
      have : W ∣ r := hg ▸ Nat.gcd_dvd_left r W
      rcases this with ⟨c, rfl⟩
      rcases c with _ | c
      · simp
      · exfalso; nlinarith
    · rintro rfl; exact ⟨hW, by simp [Nat.div_self hW]⟩
  rw [this, Finset.sum_singleton]
  simp [Zsum, ee_zero]

/-- **Ramanujan form**: `A_d(T) = ∑_E c_d(X(E))`. -/
theorem A_eq_sum_c (d : ℕ) : Acond Ω Bf T W d = ∑ E ∈ Ω, cW W d (Bf E - T) := by
  unfold Acond cW
  rw [sum_swap]

/-- The conductor fibre `{r < W : W/gcd(r,W) = d}` is `{(W/d) k : k < d, (k,d) = 1}`. -/
lemma fiber_eq_image {d : ℕ} (hd : d ∣ W) (hW : 0 < W) :
    (Finset.range W).filter (fun r => cond W r = d) =
      ((Finset.range d).filter (fun k => Nat.Coprime k d)).image (fun k => W / d * k) := by
  obtain ⟨s, rfl⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hW)
  have hs0 : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; simp at hW)
  have hWd : d * s / d = s := by rw [Nat.mul_div_cancel_left _ hd0]
  rw [hWd]
  ext r
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, cond]
  constructor
  · rintro ⟨hr, hc⟩
    have hg : Nat.gcd r (d * s) = s := by
      have hgd := Nat.gcd_dvd_right r (d * s)
      have := Nat.div_mul_cancel hgd
      rw [hc] at this
      exact Nat.eq_of_mul_eq_mul_left hd0 this
    have hsr : s ∣ r := hg ▸ Nat.gcd_dvd_left r (d * s)
    obtain ⟨k, rfl⟩ := hsr
    refine ⟨k, ⟨?_, ?_⟩, rfl⟩
    · by_contra h; push_neg at h; nlinarith
    · have : Nat.gcd (s * k) (s * d) = s := by rw [mul_comm s d]; exact hg
      rw [Nat.gcd_mul_left] at this
      have := Nat.eq_of_mul_eq_mul_left hs0 (this.trans (mul_one s).symm)
      exact this
  · rintro ⟨k, ⟨hk, hcop⟩, rfl⟩
    refine ⟨by nlinarith, ?_⟩
    rw [show d * s = s * d by ring, Nat.gcd_mul_left, hcop, mul_one,
      Nat.mul_div_cancel_left d hs0]

/-- **The fibre sum is the classical Ramanujan sum** (`d ∣ W`). -/
theorem cW_eq_ramanujan {d : ℕ} (hd : d ∣ W) (hW : 0 < W) (m : ℤ) :
    cW W d m = ramanujan d m := by
  unfold cW ramanujan
  rw [fiber_eq_image W hd hW]
  obtain ⟨s, rfl⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hW)
  have hs0 : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; simp at hW)
  rw [Nat.mul_div_cancel_left _ hd0]
  rw [Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hs0 h)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show d * s = s * d by ring]
  push_cast
  rw [show (s : ℤ) * k * m = s * (k * m) by ring, ee_scale hs0]

/-- **Ramanujan expansion of a conductor block**: `A_d(T) = ∑_E c_d(X(E))` with the classical
Ramanujan sum (`d ∣ W`). -/
theorem A_eq_sum_ramanujan {d : ℕ} (hd : d ∣ W) (hW : 0 < W) :
    Acond Ω Bf T W d = ∑ E ∈ Ω, ramanujan d (Bf E - T) := by
  rw [A_eq_sum_c]
  exact Finset.sum_congr rfl (fun E _ => cW_eq_ramanujan W hd hW _)

/-- `W/gcd(r,W) ∣ Q ↔ (W/Q) ∣ r` for `Q ∣ W`. -/
lemma cond_dvd_iff {Q : ℕ} (hQ : Q ∣ W) (hW : 0 < W) (r : ℕ) :
    cond W r ∣ Q ↔ W / Q ∣ r := by
  obtain ⟨s, rfl⟩ := hQ
  have hQ0 : 0 < Q := Nat.pos_of_ne_zero (by rintro rfl; simp at hW)
  have hs0 : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; simp at hW)
  rw [Nat.mul_div_cancel_left _ hQ0, cond]
  have hg := Nat.gcd_dvd_right r (Q * s)
  have hgpos : 0 < Nat.gcd r (Q * s) := Nat.gcd_pos_of_pos_right r hW
  rw [Nat.div_dvd_iff_dvd_mul hg hgpos, mul_comm Q s,
    Nat.mul_dvd_mul_iff_right hQ0]
  constructor
  · intro h; exact h.trans (Nat.gcd_dvd_left _ _)
  · intro h; exact Nat.dvd_gcd h (dvd_mul_right s Q)

open Classical in
/-- **Divisor-block identity**: `∑_{d ∣ Q} A_d(T) = Q · N_Q(T)` for `Q ∣ W`, where
`N_Q(T) = #{E : Q ∣ X(E)}`. -/
theorem divisor_block_identity {Q : ℕ} (hQ : Q ∣ W) (hW : 0 < W) :
    ∑ d ∈ Q.divisors, Acond Ω Bf T W d =
      (Q : ℂ) * ((Ω.filter (fun E => (Q : ℤ) ∣ Bf E - T)).card : ℂ) := by
  have hQ0 : 0 < Q := Nat.pos_of_dvd_of_pos hQ hW
  -- regroup the blocks with `d ∣ Q`
  have h1 : ∑ d ∈ Q.divisors, Acond Ω Bf T W d =
      ∑ r ∈ (Finset.range W).filter (fun r => cond W r ∣ Q),
        ee W (-((r : ℤ) * T)) * Zsum Ω Bf W r := by
    unfold Acond
    rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.range W).filter (fun r => cond W r ∣ Q))
      (t := Q.divisors) (g := cond W) (fun r hr => by
        rw [Finset.mem_filter] at hr
        exact Nat.mem_divisors.2 ⟨hr.2, hQ0.ne'⟩)]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdQ : d ∣ Q := Nat.dvd_of_mem_divisors hd
    rw [Finset.filter_filter]
    congr 1
    ext r
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2 ▸ hdQ, h2⟩
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
  rw [h1]
  obtain ⟨s, hs⟩ := hQ
  have hs0 : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; simp [hs] at hW)
  have hWs : W / Q = s := by rw [hs, Nat.mul_div_cancel_left _ hQ0]
  have himg : (Finset.range W).filter (fun r => cond W r ∣ Q) =
      (Finset.range Q).image (fun k => s * k) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    rw [cond_dvd_iff W ⟨s, hs⟩ hW, hWs]
    constructor
    · rintro ⟨hr, ⟨k, rfl⟩⟩
      refine ⟨k, ?_, rfl⟩
      by_contra h; push_neg at h; rw [hs] at hr; nlinarith
    · rintro ⟨k, hk, rfl⟩
      exact ⟨by rw [hs]; nlinarith, dvd_mul_right _ _⟩
  rw [himg, sum_swap]
  have hterm : ∀ E ∈ Ω, ∑ r ∈ (Finset.range Q).image (fun k => s * k),
      ee W ((r : ℤ) * (Bf E - T)) = if (Q : ℤ) ∣ Bf E - T then (Q : ℂ) else 0 := by
    intro E _
    rw [Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hs0 h), ← sum_ee hQ0]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hs, show Q * s = s * Q by ring]
    push_cast
    rw [show (s : ℤ) * k * (Bf E - T) = s * (k * (Bf E - T)) by ring, ee_scale hs0]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    mul_comm]

end Abstract

/-! ## Physical instances -/

open Erdos287.ExactSource

variable {a M : ℕ}

/-- Physical masses `B(E)` as integers. -/
noncomputable def Bz (a M : ℕ) (E : Finset ℕ) : ℤ := (Bm a M E : ℤ)

open Classical in
/-- On the no-wrap domain, `#{E ∈ Ω : W ∣ X(E)} = N_T`. -/
lemma filter_W_dvd_eq (ha : 0 < a) (hH1 : 1 ≤ Hm a M) (hH2 : Hm a M < 2) :
    (Omega a M).filter (fun E => (W a M ∅ : ℤ) ∣ Bz a M E - T a M ∅) =
      (Omega a M).filter (fun E => Xd a M E = 0) := by
  apply Finset.filter_congr
  intro E hE
  exact no_wrap ha hH1 hH2 hE

/-- **Exact root-of-unity coefficient**: `W · N_T = ∑_{r<W} e_W(-rT) Z(r)`. -/
theorem root_of_unity_exact_coefficient (ha : 0 < a) (hH1 : 1 ≤ Hm a M) (hH2 : Hm a M < 2) :
    (W a M ∅ : ℂ) * (NT a M : ℂ) =
      ∑ r ∈ Finset.range (W a M ∅),
        ee (W a M ∅) (-((r : ℤ) * T a M ∅)) * Zsum (Omega a M) (Bz a M) (W a M ∅) r := by
  classical
  rw [← fourier_filter _ _ _ _ (Nat.pos_of_ne_zero (W_ne_zero ha)),
    filter_W_dvd_eq ha hH1 hH2, NT]

/-- **Physical conductor decomposition**: `W · N_T = ∑_{d ∣ W} A_d(T)`, with
`A_1(T) = P = |Ω|`. -/
theorem physical_conductor_decomposition (ha : 0 < a) (hH1 : 1 ≤ Hm a M) (hH2 : Hm a M < 2) :
    (W a M ∅ : ℂ) * (NT a M : ℂ) =
      ∑ d ∈ (W a M ∅).divisors, Acond (Omega a M) (Bz a M) (T a M ∅) (W a M ∅) d ∧
    Acond (Omega a M) (Bz a M) (T a M ∅) (W a M ∅) 1 = Ptot a M := by
  have hW := Nat.pos_of_ne_zero (W_ne_zero (M := M) (R := ∅) ha)
  refine ⟨?_, A_one _ _ _ _ hW⟩
  rw [root_of_unity_exact_coefficient ha hH1 hH2, conductor_decomposition _ _ _ _ hW]

open Classical in
/-- **Physical Ramanujan block identity**: for `Q ∣ W`,
`∑_{d ∣ Q} A_d(T) = Q · N_Q(T)` with `N_Q(T) = #{E ∈ Ω : Q ∣ X(E)}`. -/
theorem physical_ramanujan_block_identity (ha : 0 < a) {Q : ℕ} (hQ : Q ∣ W a M ∅) :
    ∑ d ∈ Q.divisors, Acond (Omega a M) (Bz a M) (T a M ∅) (W a M ∅) d =
      (Q : ℂ) * (((Omega a M).filter (fun E => (Q : ℤ) ∣ Xd a M E)).card : ℂ) := by
  exact divisor_block_identity _ _ _ _ hQ (Nat.pos_of_ne_zero (W_ne_zero ha))

end Erdos287.PostQSigma
