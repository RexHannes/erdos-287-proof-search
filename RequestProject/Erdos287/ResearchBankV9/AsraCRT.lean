import RequestProject.Erdos287.ResearchBankV9.GcdClique

/-!
# Erdős #287 — Research Bank V9 §4A–4C: ASRA finite algebra (CRT, collisions, main modulus)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

**4A. Polynomial-root CRT normalization.**  For slopes `a_k`, base index `i`, spectator set `K`
(the condition `i ∉ K` is not required), the spectator forms `L_k(b) = a_k b + a_i − a_k` have rational roots
`ρ_{ik} = (a_k − a_i)/a_k`, and `Φ_i(b) = ∏_{k∈K} L_k(b)`.  For a squarefree modulus
`D = ∏_{p∈P} p` of **nonexceptional** primes (`p ∤ a_i`, `p ∤ a_k`, `p ∤ a_l − a_k`), kernel-proved
(`crt_root_bijection`): the roots `b mod D` of `Φ_i` are in bijection with the prime-factor-to-
spectator-slot allocations `P → K` (each root has a unique slot at each prime; roots with the same
slots coincide; every allocation is realised).  `roots_distinguish_allocations`: distinct
allocations give distinct roots, so a weight `Γ(D, b)` defined through the allocation must **not**
be collapsed to a function `Γ_D` of `D` alone.

**4B. Within-product collision zero** (`collision_zero`, `spectator_collision_zero`): a prime not
dividing the slope determinant cannot divide two distinct affine forms at the same point; the
corresponding physical term is exactly zero.

**4C. Correct main modulus** (`joint_modulus_iff`, `lcm_ne_product_fixture`,
`clean_main_modulus`): the combined modulus of congruences modulo `B, D, d` is
`lcm(B, D, d)`, not `BDd` in general; under `(B, Dd) = 1`, `(D, d) = 1` it equals `BDd` and
`φ(BDd) = φ(B) φ(D) φ(d)`.
-/

open scoped BigOperators

namespace Erdos287
namespace ResearchBankV9
namespace AsraCRT

/-! ## 4A.  Polynomial-root CRT normalization -/

variable (a : ℕ → ℤ) (i : ℕ) (K : Finset ℕ)

/-- The spectator form `L_k(b) = a_k b + a_i − a_k`. -/
def Lform (k : ℕ) (b : ℤ) : ℤ := a k * b + a i - a k

/-- The splitting polynomial `Φ_i(b) = ∏_{k∈K} (a_k b + a_i − a_k)`. -/
def Phi (b : ℤ) : ℤ := ∏ k ∈ K, Lform a i k b

/-- A nonexceptional prime for the slope system. -/
structure NonExc (p : ℕ) : Prop where
  prime : p.Prime
  base : ¬ (p : ℤ) ∣ a i
  slope : ∀ k ∈ K, ¬ (p : ℤ) ∣ a k
  sep : ∀ k ∈ K, ∀ l ∈ K, k ≠ l → ¬ (p : ℤ) ∣ a l - a k

variable {a i K}

theorem root_iff_slot {p : ℕ} (hp : NonExc a i K p) (b : ℤ) :
    (p : ℤ) ∣ Phi a i K b ↔ ∃ k ∈ K, (p : ℤ) ∣ Lform a i k b :=
  Prime.dvd_finset_prod_iff (Nat.prime_iff_prime_int.mp hp.prime) _

/-- **Uniqueness of the slot** at a nonexceptional prime. -/
theorem slot_unique {p : ℕ} (hp : NonExc a i K p) {b : ℤ} {k l : ℕ} (hk : k ∈ K) (hl : l ∈ K)
    (h1 : (p : ℤ) ∣ Lform a i k b) (h2 : (p : ℤ) ∣ Lform a i l b) : k = l := by
  by_contra hne
  have hpr := Nat.prime_iff_prime_int.mp hp.prime
  have : (p : ℤ) ∣ (a l - a k) * a i := by
    have := dvd_sub (dvd_mul_of_dvd_right h1 (a l)) (dvd_mul_of_dvd_right h2 (a k))
    have e : a l * Lform a i k b - a k * Lform a i l b = (a l - a k) * a i := by
      unfold Lform; ring
    rwa [e] at this
  rcases hpr.dvd_or_dvd this with h | h
  · exact hp.sep k hk l hl hne h
  · exact hp.base h

/-- The squarefree modulus `D = ∏_{p∈P} p`. -/
def Dmod (Ps : Finset ℕ) : ℕ := ∏ p ∈ Ps, p

/-- The roots of `Φ_i` modulo `D`, represented in `[0, D)`. -/
def Roots (Ps : Finset ℕ) : Finset ℤ :=
  (Finset.Ico 0 (Dmod Ps : ℤ)).filter fun b => (Dmod Ps : ℤ) ∣ Phi a i K b

theorem dvd_Dmod_iff {Ps : Finset ℕ} (hPs : ∀ p ∈ Ps, p.Prime) (z : ℤ) :
    (Dmod Ps : ℤ) ∣ z ↔ ∀ p ∈ Ps, (p : ℤ) ∣ z := by
  constructor
  · intro h p hp
    exact (Int.natCast_dvd_natCast.2 (Finset.dvd_prod_of_mem _ hp)).trans h
  · intro h
    unfold Dmod
    push_cast
    apply Finset.prod_dvd_of_coprime _ h
    intro p hp q hq hpq
    exact Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (hPs p hp) (hPs q hq)).2 hpq)

theorem Dmod_pos {Ps : Finset ℕ} (hPs : ∀ p ∈ Ps, p.Prime) : 0 < Dmod Ps :=
  Finset.prod_pos fun p hp => (hPs p hp).pos

/-- A root of a single spectator form modulo a nonexceptional prime. -/
theorem exists_root_mod {p : ℕ} (hp : NonExc a i K p) {k : ℕ} (hk : k ∈ K) :
    ∃ r : ℤ, (p : ℤ) ∣ Lform a i k r := by
  have hcop : IsCoprime (a k) (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have hpr := Nat.prime_iff_prime_int.mp hp.prime
    by_contra h
    have hg : Int.gcd (a k) p ∣ p := by
      have := Int.gcd_dvd_right (a := a k) (b := (p : ℤ)); exact_mod_cast this
    rcases (Nat.dvd_prime hp.prime).1 hg with h1 | h1
    · exact h h1
    · have : (p : ℤ) ∣ a k := by
        have := Int.gcd_dvd_left (a := a k) (b := (p : ℤ)); rw [h1] at this; exact this
      exact hp.slope k hk this
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨(a k - a i) * u, -(a k - a i) * v, ?_⟩
  unfold Lform
  linear_combination (a k - a i) * huv

/-- **Polynomial-root CRT bijection** (relational form). -/
theorem crt_root_bijection {Ps : Finset ℕ} (hPs : ∀ p ∈ Ps, NonExc a i K p) :
    (∀ b ∈ Roots (a := a) (i := i) (K := K) Ps, ∀ p ∈ Ps, ∃ k ∈ K, (p : ℤ) ∣ Lform a i k b ∧
        ∀ l ∈ K, (p : ℤ) ∣ Lform a i l b → l = k) ∧
    (∀ b ∈ Roots (a := a) (i := i) (K := K) Ps, ∀ b' ∈ Roots (a := a) (i := i) (K := K) Ps,
        (∀ p ∈ Ps, ∀ k ∈ K, (p : ℤ) ∣ Lform a i k b → (p : ℤ) ∣ Lform a i k b') → b = b') ∧
    (∀ σ : ℕ → ℕ, (∀ p ∈ Ps, σ p ∈ K) →
        ∃ b ∈ Roots (a := a) (i := i) (K := K) Ps, ∀ p ∈ Ps, (p : ℤ) ∣ Lform a i (σ p) b) := by
  have hprime : ∀ p ∈ Ps, p.Prime := fun p hp => (hPs p hp).prime
  have hD := Dmod_pos hprime
  refine ⟨?_, ?_, ?_⟩
  · -- unique slot at each prime
    intro b hb p hp
    simp only [Roots, Finset.mem_filter] at hb
    have hpd : (p : ℤ) ∣ Phi a i K b := ((dvd_Dmod_iff hprime _).1 hb.2) p hp
    obtain ⟨k, hk, hkd⟩ := (root_iff_slot (hPs p hp) b).1 hpd
    exact ⟨k, hk, hkd, fun l hl hld => slot_unique (hPs p hp) hl hk hld hkd⟩
  · -- injectivity
    intro b hb b' hb' hsame
    simp only [Roots, Finset.mem_filter, Finset.mem_Ico] at hb hb'
    have hdiff : (Dmod Ps : ℤ) ∣ b - b' := by
      rw [dvd_Dmod_iff hprime]
      intro p hp
      have hpd : (p : ℤ) ∣ Phi a i K b := ((dvd_Dmod_iff hprime _).1 hb.2) p hp
      obtain ⟨k, hk, hkd⟩ := (root_iff_slot (hPs p hp) b).1 hpd
      have hkd' := hsame p hp k hk hkd
      have h1 : (p : ℤ) ∣ a k * (b - b') := by
        have := dvd_sub hkd hkd'
        rwa [show Lform a i k b - Lform a i k b' = a k * (b - b') by unfold Lform; ring] at this
      rcases (Nat.prime_iff_prime_int.mp (hprime p hp)).dvd_or_dvd h1 with h | h
      · exact absurd h ((hPs p hp).slope k hk)
      · exact h
    have := Int.eq_zero_of_abs_lt_dvd hdiff (by rw [abs_lt]; constructor <;> linarith)
    linarith
  · -- surjectivity
    intro σ hσ
    have hr : ∀ p ∈ Ps, ∃ r : ℤ, (p : ℤ) ∣ Lform a i (σ p) r :=
      fun p hp => exists_root_mod (hPs p hp) (hσ p hp)
    choose! r hr using hr
    let l : List (ℤ × ℕ) := Ps.toList.map fun p => (r p, p)
    have hl0 : ∀ q ∈ l, q.2 ≠ 0 := by
      intro q hq
      simp only [l, List.mem_map, Finset.mem_toList] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      exact (hprime p hp).ne_zero
    have hlc : ∀ q ∈ l, ∀ s ∈ l, ((Nat.gcd q.2 s.2 : ℕ) : ℤ) ∣ q.1 - s.1 := by
      intro q hq s hs
      simp only [l, List.mem_map, Finset.mem_toList] at hq hs
      obtain ⟨p, hp, rfl⟩ := hq
      obtain ⟨p', hp', rfl⟩ := hs
      by_cases hpp : p = p'
      · subst hpp; simp
      · rw [(Nat.coprime_primes (hprime p hp) (hprime p' hp')).2 hpp]; simp
    obtain ⟨x, hx⟩ := GcdClique.crt_exists l hl0 hlc
    have hxp : ∀ p ∈ Ps, (p : ℤ) ∣ x - r p := fun p hp =>
      hx (r p, p) (by simp only [l, List.mem_map, Finset.mem_toList]; exact ⟨p, hp, rfl⟩)
    set b := x % (Dmod Ps : ℤ)
    have hbx : (Dmod Ps : ℤ) ∣ b - x := by
      refine ⟨-(x / (Dmod Ps : ℤ)), ?_⟩
      have := Int.emod_add_mul_ediv x (Dmod Ps : ℤ)
      linarith
    have hslot : ∀ p ∈ Ps, (p : ℤ) ∣ Lform a i (σ p) b := by
      intro p hp
      have h1 : (p : ℤ) ∣ b - r p := by
        have := dvd_add (((dvd_Dmod_iff hprime _).1 hbx) p hp) (hxp p hp)
        rwa [show b - x + (x - r p) = b - r p by ring] at this
      have := dvd_add (dvd_mul_of_dvd_right h1 (a (σ p))) (hr p hp)
      rwa [show a (σ p) * (b - r p) + Lform a i (σ p) (r p) = Lform a i (σ p) b by
        unfold Lform; ring] at this
    refine ⟨b, ?_, hslot⟩
    simp only [Roots, Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨Int.emod_nonneg _ (by exact_mod_cast hD.ne'), Int.emod_lt_of_pos _
      (by exact_mod_cast hD)⟩, ?_⟩
    rw [dvd_Dmod_iff hprime]
    intro p hp
    exact (root_iff_slot (hPs p hp) b).2 ⟨σ p, hσ p hp, hslot p hp⟩

/-- **Do not collapse `Γ(D, b)` to `Γ_D`**: two distinct spectator slots at one prime are
realised by two distinct roots with different allocations. -/
theorem roots_distinguish_allocations {Ps : Finset ℕ} (hPs : ∀ p ∈ Ps, NonExc a i K p)
    {p : ℕ} (hp : p ∈ Ps) {k l : ℕ} (hk : k ∈ K) (hl : l ∈ K) (hkl : k ≠ l) :
    ∃ b ∈ Roots (a := a) (i := i) (K := K) Ps, ∃ b' ∈ Roots (a := a) (i := i) (K := K) Ps,
      b ≠ b' ∧ (p : ℤ) ∣ Lform a i k b ∧ (p : ℤ) ∣ Lform a i l b' ∧
        ¬ (p : ℤ) ∣ Lform a i l b := by
  obtain ⟨-, -, hsurj⟩ := crt_root_bijection hPs
  obtain ⟨b, hb, hbk⟩ := hsurj (fun _ => k) (fun _ _ => hk)
  obtain ⟨b', hb', hbl⟩ := hsurj (fun _ => l) (fun _ _ => hl)
  have hnot : ¬ (p : ℤ) ∣ Lform a i l b := fun h =>
    hkl (slot_unique (hPs p hp) hk hl (hbk p hp) h)
  refine ⟨b, hb, b', hb', ?_, hbk p hp, hbl p hp, hnot⟩
  rintro rfl
  exact hnot (hbl p hp)

/-! ## 4B.  Within-product collision zero -/

/-- **Collision zero.**  If `p ∤ a_l c_k − a_k c_l`, no `t` has `p ∣ a_k t + c_k` and
`p ∣ a_l t + c_l`; the corresponding physical term vanishes identically. -/
theorem collision_zero {p : ℕ} {ak ck al cl : ℤ}
    (hdet : ¬ (p : ℤ) ∣ al * ck - ak * cl) (T : Finset ℤ) (w : ℤ → ℝ) :
    (T.filter fun t => (p : ℤ) ∣ ak * t + ck ∧ (p : ℤ) ∣ al * t + cl) = ∅ ∧
    ∑ t ∈ T.filter (fun t => (p : ℤ) ∣ ak * t + ck ∧ (p : ℤ) ∣ al * t + cl), w t = 0 := by
  have hempty : (T.filter fun t => (p : ℤ) ∣ ak * t + ck ∧ (p : ℤ) ∣ al * t + cl) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    rintro t - ⟨h1, h2⟩
    apply hdet
    have := dvd_sub (dvd_mul_of_dvd_right h1 al) (dvd_mul_of_dvd_right h2 ak)
    rwa [show al * (ak * t + ck) - ak * (al * t + cl) = al * ck - ak * cl by ring] at this
  exact ⟨hempty, by rw [hempty, Finset.sum_empty]⟩

/-- Spectator specialization: the determinant of `L_k, L_l` is `a_i (a_l − a_k)`, so at a
nonexceptional prime two distinct spectator forms never collide. -/
theorem spectator_collision_zero {p : ℕ} (hp : NonExc a i K p) {k l : ℕ} (hk : k ∈ K)
    (hl : l ∈ K) (hkl : k ≠ l) (T : Finset ℤ) (w : ℤ → ℝ) :
    ∑ t ∈ T.filter (fun t => (p : ℤ) ∣ Lform a i k t ∧ (p : ℤ) ∣ Lform a i l t), w t = 0 := by
  have hT : T.filter (fun t => (p : ℤ) ∣ Lform a i k t ∧ (p : ℤ) ∣ Lform a i l t) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    rintro t - ⟨h1, h2⟩
    exact hkl (slot_unique hp hk hl h1 h2)
  rw [hT, Finset.sum_empty]

/-! ## 4C.  The correct main modulus -/

/-- The joint modulus of congruences modulo `B`, `D`, `d` is `lcm(B, lcm(D, d))`. -/
theorem joint_modulus_iff (B D d x : ℕ) :
    (B ∣ x ∧ D ∣ x ∧ d ∣ x) ↔ Nat.lcm B (Nat.lcm D d) ∣ x := by
  rw [Nat.lcm_dvd_iff, Nat.lcm_dvd_iff]

/-- **Counterfixture**: with overlapping moduli the joint modulus is not the product. -/
theorem lcm_ne_product_fixture : Nat.lcm 2 (Nat.lcm 2 1) = 2 ∧ 2 * 2 * 1 = 4 ∧
    Nat.lcm 2 (Nat.lcm 2 1) ≠ 2 * 2 * 1 := by decide

/-- **Clean main modulus**: under `(B, Dd) = 1` and `(D, d) = 1`, the joint modulus is `BDd` and
the totient factors as `φ(B) φ(D) φ(d)`. -/
theorem clean_main_modulus {B D d : ℕ} (h1 : Nat.Coprime B (D * d)) (h2 : Nat.Coprime D d) :
    Nat.lcm B (Nat.lcm D d) = B * D * d ∧
      Nat.totient (B * D * d) = Nat.totient B * Nat.totient D * Nat.totient d := by
  constructor
  · rw [h2.lcm_eq_mul, h1.lcm_eq_mul, mul_assoc]
  · rw [mul_assoc, Nat.totient_mul h1, Nat.totient_mul h2, mul_assoc]

end AsraCRT
end ResearchBankV9
end Erdos287
