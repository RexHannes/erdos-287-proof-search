import Mathlib

/-!
# Erdős #287 effectivity — the complete-period endpoint covariance (§24)

```
COMPLETE-PERIOD ENDPOINT IDENTITY : KERNEL-PROVED
COPRIME ENDPOINT ORTHOGONALITY    : KERNEL-PROVED
ENDPOINT COVARIANCE NONNEGATIVITY : KERNEL-PROVED
LANE INDEPENDENCE                 : KERNEL-PROVED
```

For a modulus `q ≥ 1` and a lane offset `c`, the *finite sawtooth endpoint function* is the
centred discrete sawtooth

    φ_q^{(c)}(v) = ((v + c) mod q)/q − (q−1)/(2q),

a mean-zero function of `v` with period `q`.  The complete-period covariance of two such
functions is taken over one full period of the joint system, i.e. over `v mod L` with
`L = lcm(q₁,q₂)`:

    Cov(q₁,q₂;c) = (1/L) ∑_{v mod L} φ_{q₁}^{(c)}(v) φ_{q₂}^{(c)}(v).

The main theorem of this file is the **exact** finite-period identity

    Cov(q₁,q₂;c) = (g² − 1)/(12 q₁ q₂),    g = gcd(q₁,q₂),

proved by an exact finite computation (no numerical testing, no analytic input).  The three
corollaries required by the source follow: coprime moduli are exactly orthogonal, the
covariance depends only on the `gcd` stratum, and it is always nonnegative.

The identity needs only `q₁, q₂ ≥ 1`; oddness of the moduli — the case used by the source —
is recorded as a specialisation (`endpointCovariance_odd`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §24.1  Elementary finite sums -/

/-- Gauss's sum, over `ℚ`. -/
theorem sum_range_cast (n : ℕ) : ∑ i ∈ range n, (i : ℚ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The sum of squares, over `ℚ`. -/
theorem sum_range_cast_sq (n : ℕ) :
    ∑ i ∈ range n, (i : ℚ) ^ 2 = n * (n - 1) * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Reduction of a two-scale residue: for `x < g` and `b > 0`,
`(x + g w) mod (g b) = x + g (w mod b)`. -/
theorem mod_two_scale (g b x w : ℕ) (hb : 0 < b) (hx : x < g) :
    (x + g * w) % (g * b) = x + g * (w % b) := by
  have h1 : (g * w) % (g * b) = g * (w % b) := Nat.mul_mod_mul_left g w b
  have hmod : w % b ≤ b - 1 := by have := Nat.mod_lt w hb; omega
  have hle : g * (w % b) ≤ g * (b - 1) := Nat.mul_le_mul_left g hmod
  have hgb : g * (b - 1) + g = g * b := by
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    simp [Nat.mul_succ]
  have h2 : x + g * (w % b) < g * b := by omega
  have hxlt : x < g * b := by
    calc x < g := hx
      _ = g * 1 := (mul_one g).symm
      _ ≤ g * b := Nat.mul_le_mul_left g hb
  conv_lhs => rw [Nat.add_mod, h1, Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt h2]

/-- Splitting a range of length `g·a` along the two-scale decomposition `u = r + g s`. -/
theorem sum_range_two_scale (g a : ℕ) (hg : 0 < g) (f : ℕ → ℚ) :
    ∑ u ∈ range (g * a), f u = ∑ r ∈ range g, ∑ s ∈ range a, f (r + g * s) := by
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (i := fun u => (u % g, u / g)) (j := fun p => p.1 + g * p.2)
  · intro u hu; simp only [mem_range] at hu; simp only [mem_product, mem_range]
    exact ⟨Nat.mod_lt _ hg, Nat.div_lt_of_lt_mul (by linarith [hu])⟩
  · intro p hp; simp only [mem_product, mem_range] at hp; simp only [mem_range]
    nlinarith [Nat.succ_le_of_lt hp.2]
  · intro u _; simp [Nat.mod_add_div]
  · intro p hp; simp only [mem_product, mem_range] at hp
    have h1 : (p.1 + g * p.2) % g = p.1 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp.1]
    have h2 : (p.1 + g * p.2) / g = p.2 := by
      rw [Nat.add_mul_div_left _ _ hg, Nat.div_eq_of_lt hp.1]; omega
    simp [h1, h2]
  · intro u _; simp [Nat.mod_add_div]

/-- An affine map `s ↦ (c + a s) mod b` with `gcd(a,b) = 1` permutes a complete residue
system mod `b`. -/
theorem sum_range_affine_perm (a b c : ℕ) (hb : 0 < b) (hab : Nat.Coprime a b) (f : ℕ → ℚ) :
    ∑ s ∈ range b, f ((c + a * s) % b) = ∑ t ∈ range b, f t := by
  classical
  have hinj : Set.InjOn (fun s => (c + a * s) % b) (range b) := by
    intro s hs s' hs' h
    simp only [mem_coe, mem_range] at hs hs'
    have h2 : a * s ≡ a * s' [MOD b] := Nat.ModEq.add_left_cancel' c h
    have h3 : s ≡ s' [MOD b] :=
      Nat.ModEq.cancel_left_of_coprime (by simpa [Nat.Coprime] using hab.symm) h2
    unfold Nat.ModEq at h3
    rwa [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hs'] at h3
  have himg : (range b).image (fun s => (c + a * s) % b) = range b := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [mem_image, mem_range] at hx ⊢
      obtain ⟨s, _, rfl⟩ := hx
      exact Nat.mod_lt _ hb
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ s ∈ range b, f ((c + a * s) % b)
      = ∑ x ∈ (range b).image (fun s => (c + a * s) % b), f x :=
        (Finset.sum_image (by intro x hx y hy h; exact hinj hx hy h)).symm
    _ = ∑ t ∈ range b, f t := by rw [himg]

/-- The complete-period first moment: `∑_{v < q k} (v mod q) = k · q(q−1)/2`. -/
theorem sum_range_mod_cast (q k : ℕ) (hq : 0 < q) :
    ∑ v ∈ range (q * k), ((v % q : ℕ) : ℚ) = (k : ℚ) * ((q : ℚ) * ((q : ℚ) - 1) / 2) := by
  rw [sum_range_two_scale q k hq (fun v => ((v % q : ℕ) : ℚ))]
  have hcong : ∀ r ∈ range q, ∑ _s ∈ range k, (((r + q * _s) % q : ℕ) : ℚ) = (k : ℚ) * (r : ℚ) := by
    intro r hr
    simp only [mem_range] at hr
    have hmod : ∀ s : ℕ, (r + q * s) % q = r := by
      intro s; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    calc ∑ _s ∈ range k, (((r + q * _s) % q : ℕ) : ℚ)
        = ∑ _s ∈ range k, ((r : ℕ) : ℚ) := Finset.sum_congr rfl fun s _ => by rw [hmod s]
      _ = (k : ℚ) * (r : ℚ) := by rw [Finset.sum_const]; simp [nsmul_eq_mul]
  rw [Finset.sum_congr rfl hcong, ← Finset.mul_sum, sum_range_cast]

/-- The mixed second moment over a complete period, in two-scale coordinates. -/
theorem sum_range_mod_mul_mod_aux (g a : ℕ) (hg : 0 < g) :
    ∑ u ∈ range (g * a), (u : ℚ) * ((u % g : ℕ) : ℚ)
      = (a : ℚ) * ((g : ℚ) * ((g : ℚ) - 1) * (2 * (g : ℚ) - 1) / 6)
        + (g : ℚ) * ((a : ℚ) * ((a : ℚ) - 1) / 2) * ((g : ℚ) * ((g : ℚ) - 1) / 2) := by
  rw [sum_range_two_scale g a hg (fun u => (u : ℚ) * ((u % g : ℕ) : ℚ))]
  have hcong : ∀ r ∈ range g, ∑ s ∈ range a, ((r + g * s : ℕ) : ℚ) * (((r + g * s) % g : ℕ) : ℚ)
      = (a : ℚ) * (r : ℚ) ^ 2 + (g : ℚ) * (r : ℚ) * ((a : ℚ) * ((a : ℚ) - 1) / 2) := by
    intro r hr
    simp only [mem_range] at hr
    have hmod : ∀ s : ℕ, (r + g * s) % g = r := by
      intro s; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    calc ∑ s ∈ range a, ((r + g * s : ℕ) : ℚ) * (((r + g * s) % g : ℕ) : ℚ)
        = ∑ s ∈ range a, ((r : ℚ) ^ 2 + ((g : ℚ) * (r : ℚ)) * (s : ℚ)) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [hmod s]; push_cast; ring
      _ = (a : ℚ) * (r : ℚ) ^ 2 + ((g : ℚ) * (r : ℚ)) * ∑ s ∈ range a, (s : ℚ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum]
          simp [nsmul_eq_mul]
      _ = (a : ℚ) * (r : ℚ) ^ 2 + (g : ℚ) * (r : ℚ) * ((a : ℚ) * ((a : ℚ) - 1) / 2) := by
          rw [sum_range_cast]
  rw [Finset.sum_congr rfl hcong, Finset.sum_add_distrib, ← Finset.mul_sum, sum_range_cast_sq]
  rw [show ∑ r ∈ range g, (g : ℚ) * (r : ℚ) * ((a : ℚ) * ((a : ℚ) - 1) / 2)
        = ((g : ℚ) * ((a : ℚ) * ((a : ℚ) - 1) / 2)) * ∑ r ∈ range g, (r : ℚ) from by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring]
  rw [sum_range_cast]

/-- **The complete-period mixed second moment.**  `KERNEL-PROVED`.  With `q₁ = g a`,
`q₂ = g b`, `gcd(a,b) = 1` and `L = g a b = lcm(q₁,q₂)`,

    ∑_{v < L} (v mod q₁)(v mod q₂) = L · [ (q₁−1)(q₂−1)/4 + (g²−1)/12 ]. -/
theorem sum_range_mod_mul_mod (g a b : ℕ) (hg : 0 < g) (hb : 0 < b) (hab : Nat.Coprime a b) :
    ∑ v ∈ range (g * a * b), ((v % (g * a) : ℕ) : ℚ) * ((v % (g * b) : ℕ) : ℚ)
      = ((g * a * b : ℕ) : ℚ)
        * ((((g * a : ℕ) : ℚ) - 1) * (((g * b : ℕ) : ℚ) - 1) / 4 + ((g : ℚ) ^ 2 - 1) / 12) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  have hga : 0 < g * a := Nat.mul_pos hg ha
  rw [sum_range_two_scale (g * a) b hga
    (fun v => ((v % (g * a) : ℕ) : ℚ) * ((v % (g * b) : ℕ) : ℚ))]
  have hinner : ∀ u ∈ range (g * a),
      ∑ s ∈ range b, (((u + (g * a) * s) % (g * a) : ℕ) : ℚ) * (((u + (g * a) * s) % (g * b) : ℕ) : ℚ)
        = (u : ℚ) * ((b : ℚ) * ((u % g : ℕ) : ℚ) + (g : ℚ) * ((b : ℚ) * ((b : ℚ) - 1) / 2)) := by
    intro u hu
    simp only [mem_range] at hu
    have h1 : ∀ s : ℕ, (u + (g * a) * s) % (g * a) = u := by
      intro s; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]
    have h2 : ∀ s : ℕ, (u + (g * a) * s) % (g * b) = u % g + g * ((u / g + a * s) % b) := by
      intro s
      have hrw : u + (g * a) * s = u % g + g * (u / g + a * s) := by
        have := Nat.div_add_mod u g
        ring_nf
        omega
      rw [hrw, mod_two_scale g b (u % g) (u / g + a * s) hb (Nat.mod_lt _ hg)]
    calc ∑ s ∈ range b,
            (((u + (g * a) * s) % (g * a) : ℕ) : ℚ) * (((u + (g * a) * s) % (g * b) : ℕ) : ℚ)
        = ∑ s ∈ range b, ((u : ℚ) * ((u % g : ℕ) : ℚ)
            + ((u : ℚ) * (g : ℚ)) * ((((u / g + a * s) % b : ℕ)) : ℚ)) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [h1 s, h2 s]; push_cast; ring
      _ = (b : ℚ) * ((u : ℚ) * ((u % g : ℕ) : ℚ))
            + ((u : ℚ) * (g : ℚ)) * ∑ s ∈ range b, ((((u / g + a * s) % b : ℕ)) : ℚ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum]
          simp [nsmul_eq_mul]
      _ = (b : ℚ) * ((u : ℚ) * ((u % g : ℕ) : ℚ))
            + ((u : ℚ) * (g : ℚ)) * ((b : ℚ) * ((b : ℚ) - 1) / 2) := by
          rw [sum_range_affine_perm a b (u / g) hb hab (fun t => (t : ℚ)), sum_range_cast]
      _ = (u : ℚ) * ((b : ℚ) * ((u % g : ℕ) : ℚ) + (g : ℚ) * ((b : ℚ) * ((b : ℚ) - 1) / 2)) := by
          ring
  rw [Finset.sum_congr rfl hinner]
  have hsplit : ∑ u ∈ range (g * a),
        (u : ℚ) * ((b : ℚ) * ((u % g : ℕ) : ℚ) + (g : ℚ) * ((b : ℚ) * ((b : ℚ) - 1) / 2))
      = (b : ℚ) * ∑ u ∈ range (g * a), (u : ℚ) * ((u % g : ℕ) : ℚ)
        + ((g : ℚ) * ((b : ℚ) * ((b : ℚ) - 1) / 2)) * ∑ u ∈ range (g * a), (u : ℚ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [hsplit, sum_range_mod_mul_mod_aux g a hg, sum_range_cast]
  push_cast
  ring

/-! ## §24.2  Complete-period shift invariance -/

/-- A one-step shift of a complete-period sum. -/
theorem sum_range_shift_one (L : ℕ) (f : ℕ → ℚ) (hf : ∀ n, f (n + L) = f n) :
    ∑ v ∈ range L, f (v + 1) = ∑ v ∈ range L, f v := by
  have h1 : ∑ v ∈ range (L + 1), f v = ∑ v ∈ range L, f (v + 1) + f 0 :=
    Finset.sum_range_succ' f L
  have h2 : ∑ v ∈ range (L + 1), f v = ∑ v ∈ range L, f v + f L := Finset.sum_range_succ f L
  have h3 : f L = f 0 := by simpa using hf 0
  rw [h3] at h2
  linarith [h1, h2]

/-- **Complete-period shift invariance.**  `KERNEL-PROVED`.  A sum of an `L`-periodic
function over one complete period does not depend on the lane offset. -/
theorem sum_range_shift (L c : ℕ) :
    ∀ f : ℕ → ℚ, (∀ n, f (n + L) = f n) → ∑ v ∈ range L, f (v + c) = ∑ v ∈ range L, f v := by
  induction c with
  | zero => intro f _; simp
  | succ k ih =>
      intro f hf
      have hf' : ∀ n, (fun m => f (m + 1)) (n + L) = (fun m => f (m + 1)) n := by
        intro n; simpa [add_right_comm] using hf (n + 1)
      calc ∑ v ∈ range L, f (v + (k + 1))
          = ∑ v ∈ range L, (fun m => f (m + 1)) (v + k) := by
            refine Finset.sum_congr rfl fun v _ => ?_
            simp [add_assoc, add_comm, add_left_comm]
        _ = ∑ v ∈ range L, (fun m => f (m + 1)) v := ih (fun m => f (m + 1)) hf'
        _ = ∑ v ∈ range L, f v := sum_range_shift_one L f hf

/-! ## §24.3  The endpoint function and its complete-period covariance -/

/-- The finite sawtooth endpoint function `φ_q^{(c)}(v) = ((v+c) mod q)/q − (q−1)/(2q)`:
the centred discrete sawtooth in lane `c`. -/
def endpointPhi (q c v : ℕ) : ℚ := (((v + c) % q : ℕ) : ℚ) / q - ((q : ℚ) - 1) / (2 * q)

/-- The complete-period covariance of two endpoint functions, averaged over one full joint
period `L = lcm(q₁,q₂)`. -/
def endpointCovariance (q1 q2 c : ℕ) : ℚ :=
  (1 / ((Nat.lcm q1 q2 : ℕ) : ℚ))
    * ∑ v ∈ range (Nat.lcm q1 q2), endpointPhi q1 c v * endpointPhi q2 c v

/-- `φ_q^{(c)}` has mean zero over a complete period. -/
theorem endpointPhi_sum_period (q c : ℕ) (hq : 0 < q) :
    ∑ v ∈ range q, endpointPhi q c v = 0 := by
  have hper : ∀ n : ℕ, (fun v => (((v : ℕ) % q : ℕ) : ℚ)) (n + q) = (fun v => (((v : ℕ) % q : ℕ) : ℚ)) n := by
    intro n; simp
  have hshift : ∑ v ∈ range q, (((v + c) % q : ℕ) : ℚ) = ∑ v ∈ range q, ((v % q : ℕ) : ℚ) :=
    sum_range_shift q c (fun v => ((v % q : ℕ) : ℚ)) hper
  have hbase : ∑ v ∈ range q, ((v % q : ℕ) : ℚ) = (q : ℚ) * ((q : ℚ) - 1) / 2 := by
    have := sum_range_mod_cast q 1 hq
    simpa using this
  have hq' : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  unfold endpointPhi
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, hshift, hbase, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

/-- **`endpointCovariance_exact`.**  `KERNEL-PROVED`.  The exact complete-period endpoint
covariance identity: for `q₁, q₂ ≥ 1`, in any lane `c`,

    (1/L) ∑_{v mod L} φ_{q₁}^{(c)}(v) φ_{q₂}^{(c)}(v) = (g² − 1)/(12 q₁ q₂),

with `g = gcd(q₁,q₂)`, `L = lcm(q₁,q₂)`. -/
theorem endpointCovariance_exact {q1 q2 : ℕ} (h1 : 0 < q1) (h2 : 0 < q2) (c : ℕ) :
    endpointCovariance q1 q2 c
      = ((Nat.gcd q1 q2 : ℚ) ^ 2 - 1) / (12 * (q1 : ℚ) * (q2 : ℚ)) := by
  classical
  obtain ⟨g, a, b, hgdef, hg, ha, hb, hq1, hq2, hab⟩ :
      ∃ g a b : ℕ, g = Nat.gcd q1 q2 ∧ 0 < g ∧ 0 < a ∧ 0 < b ∧ q1 = g * a ∧ q2 = g * b ∧
        Nat.Coprime a b := by
    refine ⟨Nat.gcd q1 q2, q1 / Nat.gcd q1 q2, q2 / Nat.gcd q1 q2, rfl,
      Nat.gcd_pos_of_pos_left _ h1, ?_, ?_,
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left q1 q2)).symm,
      (Nat.mul_div_cancel' (Nat.gcd_dvd_right q1 q2)).symm,
      Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ h1)⟩
    · rcases Nat.eq_zero_or_pos (q1 / Nat.gcd q1 q2) with hz | hz
      · have := (Nat.mul_div_cancel' (Nat.gcd_dvd_left q1 q2)).symm
        rw [hz, mul_zero] at this; omega
      · exact hz
    · rcases Nat.eq_zero_or_pos (q2 / Nat.gcd q1 q2) with hz | hz
      · have := (Nat.mul_div_cancel' (Nat.gcd_dvd_right q1 q2)).symm
        rw [hz, mul_zero] at this; omega
      · exact hz
  have hL : Nat.lcm q1 q2 = g * a * b := by
    have hkey : g * Nat.lcm q1 q2 = g * (g * a * b) := by
      rw [hgdef, Nat.gcd_mul_lcm]
      conv_lhs => rw [hq1, hq2]
      rw [← hgdef]; ring
    exact Nat.eq_of_mul_eq_mul_left hg hkey
  have hLpos : 0 < g * a * b := by positivity
  have hq1L : q1 ∣ g * a * b := ⟨b, by rw [hq1]⟩
  have hq2L : q2 ∣ g * a * b := ⟨a, by rw [hq2]; ring⟩
  obtain ⟨k1, hk1⟩ := hq1L
  obtain ⟨k2, hk2⟩ := hq2L
  have hm1 : ∀ n : ℕ, (n + g * a * b) % q1 = n % q1 := by
    intro n; rw [hk1, Nat.add_mul_mod_self_left]
  have hm2 : ∀ n : ℕ, (n + g * a * b) % q2 = n % q2 := by
    intro n; rw [hk2, Nat.add_mul_mod_self_left]
  have hper1 : ∀ n : ℕ,
      (fun v => ((v % q1 : ℕ) : ℚ)) (n + g * a * b) = (fun v => ((v % q1 : ℕ) : ℚ)) n := by
    intro n; simp only []; rw [hm1 n]
  have hper2 : ∀ n : ℕ,
      (fun v => ((v % q2 : ℕ) : ℚ)) (n + g * a * b) = (fun v => ((v % q2 : ℕ) : ℚ)) n := by
    intro n; simp only []; rw [hm2 n]
  have hper : ∀ n : ℕ,
      (fun v => ((v % q1 : ℕ) : ℚ) * ((v % q2 : ℕ) : ℚ)) (n + g * a * b)
        = (fun v => ((v % q1 : ℕ) : ℚ) * ((v % q2 : ℕ) : ℚ)) n := by
    intro n; simp only []; rw [hm1 n, hm2 n]
  -- the three complete-period moments, in lane 0
  have hS12 : ∑ v ∈ range (g * a * b), ((v % q1 : ℕ) : ℚ) * ((v % q2 : ℕ) : ℚ)
      = ((g * a * b : ℕ) : ℚ)
        * (((q1 : ℚ) - 1) * ((q2 : ℚ) - 1) / 4 + ((g : ℚ) ^ 2 - 1) / 12) := by
    have hraw := sum_range_mod_mul_mod g a b hg hb hab
    rw [← hq1, ← hq2] at hraw
    have hrange : g * a * b = q1 * b := by rw [hq1]
    rw [hrange]
    exact hraw
  have hS1 : ∑ v ∈ range (g * a * b), ((v % q1 : ℕ) : ℚ)
      = ((g * a * b : ℕ) : ℚ) * ((q1 : ℚ) - 1) / 2 := by
    have hrange : g * a * b = q1 * b := by rw [hq1]
    rw [hrange, sum_range_mod_cast q1 b h1]
    push_cast
    ring
  have hS2 : ∑ v ∈ range (g * a * b), ((v % q2 : ℕ) : ℚ)
      = ((g * a * b : ℕ) : ℚ) * ((q2 : ℚ) - 1) / 2 := by
    have hrange : g * a * b = q2 * a := by rw [hq2]; ring
    rw [hrange, sum_range_mod_cast q2 a h2]
    push_cast
    ring
  have hq1' : (q1 : ℚ) ≠ 0 := Nat.cast_ne_zero.2 h1.ne'
  have hq2' : (q2 : ℚ) ≠ 0 := Nat.cast_ne_zero.2 h2.ne'
  have hLne : ((g * a * b : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hLpos.ne'
  -- pointwise expansion of the product of the two endpoint functions
  have hpt : ∀ v : ℕ, endpointPhi q1 c v * endpointPhi q2 c v
      = (1 / ((q1 : ℚ) * (q2 : ℚ)))
        * ((((v + c) % q1 : ℕ) : ℚ) * (((v + c) % q2 : ℕ) : ℚ)
            - ((q2 : ℚ) - 1) / 2 * (((v + c) % q1 : ℕ) : ℚ)
            - ((q1 : ℚ) - 1) / 2 * (((v + c) % q2 : ℕ) : ℚ)
            + ((q1 : ℚ) - 1) * ((q2 : ℚ) - 1) / 4) := by
    intro v
    unfold endpointPhi
    field_simp
    ring
  have hshift12 : ∑ v ∈ range (g * a * b), (((v + c) % q1 : ℕ) : ℚ) * (((v + c) % q2 : ℕ) : ℚ)
      = ∑ v ∈ range (g * a * b), ((v % q1 : ℕ) : ℚ) * ((v % q2 : ℕ) : ℚ) :=
    sum_range_shift (g * a * b) c (fun v => ((v % q1 : ℕ) : ℚ) * ((v % q2 : ℕ) : ℚ)) hper
  have hshift1 : ∑ v ∈ range (g * a * b), (((v + c) % q1 : ℕ) : ℚ)
      = ∑ v ∈ range (g * a * b), ((v % q1 : ℕ) : ℚ) :=
    sum_range_shift (g * a * b) c (fun v => ((v % q1 : ℕ) : ℚ)) hper1
  have hshift2 : ∑ v ∈ range (g * a * b), (((v + c) % q2 : ℕ) : ℚ)
      = ∑ v ∈ range (g * a * b), ((v % q2 : ℕ) : ℚ) :=
    sum_range_shift (g * a * b) c (fun v => ((v % q2 : ℕ) : ℚ)) hper2
  have hsum : ∑ v ∈ range (g * a * b), endpointPhi q1 c v * endpointPhi q2 c v
      = (1 / ((q1 : ℚ) * (q2 : ℚ)))
        * (((g * a * b : ℕ) : ℚ) * (((q1 : ℚ) - 1) * ((q2 : ℚ) - 1) / 4 + ((g : ℚ) ^ 2 - 1) / 12)
            - ((q2 : ℚ) - 1) / 2 * (((g * a * b : ℕ) : ℚ) * ((q1 : ℚ) - 1) / 2)
            - ((q1 : ℚ) - 1) / 2 * (((g * a * b : ℕ) : ℚ) * ((q2 : ℚ) - 1) / 2)
            + ((g * a * b : ℕ) : ℚ) * (((q1 : ℚ) - 1) * ((q2 : ℚ) - 1) / 4)) := by
    rw [Finset.sum_congr rfl (fun v _ => hpt v), ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      hshift12, hshift1, hshift2, hS12, hS1, hS2]
  unfold endpointCovariance
  rw [hL, hsum, ← hgdef]
  field_simp
  ring

/-- **`endpointCovariance_coprime_zero`.**  `KERNEL-PROVED`.  Coprime moduli have exactly
orthogonal endpoint functions. -/
theorem endpointCovariance_coprime_zero {q1 q2 : ℕ} (h1 : 0 < q1) (h2 : 0 < q2)
    (hcop : Nat.Coprime q1 q2) (c : ℕ) : endpointCovariance q1 q2 c = 0 := by
  rw [endpointCovariance_exact h1 h2 c]
  have : Nat.gcd q1 q2 = 1 := hcop
  rw [this]
  norm_num

/-- **`endpointCovariance_nonneg`.**  `KERNEL-PROVED`.  The complete-period endpoint
covariance is nonnegative. -/
theorem endpointCovariance_nonneg {q1 q2 : ℕ} (h1 : 0 < q1) (h2 : 0 < q2) (c : ℕ) :
    0 ≤ endpointCovariance q1 q2 c := by
  rw [endpointCovariance_exact h1 h2 c]
  have hg : 1 ≤ Nat.gcd q1 q2 := Nat.gcd_pos_of_pos_left _ h1
  have hg' : (1 : ℚ) ≤ (Nat.gcd q1 q2 : ℚ) := by exact_mod_cast hg
  have hnum : 0 ≤ ((Nat.gcd q1 q2 : ℚ)) ^ 2 - 1 := by nlinarith
  have hden : 0 < 12 * (q1 : ℚ) * (q2 : ℚ) := by
    have : (0 : ℚ) < q1 := by exact_mod_cast h1
    have : (0 : ℚ) < q2 := by exact_mod_cast h2
    positivity
  positivity

/-- **`endpointCovariance_gcd_stratum`.**  `KERNEL-PROVED`.  The covariance depends on the
pair only through the `gcd` stratum and the product `q₁q₂`: two pairs with the same `gcd`
and the same product have the same covariance, in every lane. -/
theorem endpointCovariance_gcd_stratum {q1 q2 r1 r2 : ℕ} (h1 : 0 < q1) (h2 : 0 < q2)
    (k1 : 0 < r1) (k2 : 0 < r2) (hgcd : Nat.gcd q1 q2 = Nat.gcd r1 r2)
    (hprod : q1 * q2 = r1 * r2) (c d : ℕ) :
    endpointCovariance q1 q2 c = endpointCovariance r1 r2 d := by
  rw [endpointCovariance_exact h1 h2 c, endpointCovariance_exact k1 k2 d, hgcd]
  have hq : (q1 : ℚ) * (q2 : ℚ) = (r1 : ℚ) * (r2 : ℚ) := by exact_mod_cast hprod
  rw [mul_assoc, mul_assoc, hq]

/-- **`endpointCovariance_lane_independent`.**  `KERNEL-PROVED`.  The complete-period
covariance is the same in every permitted lane. -/
theorem endpointCovariance_lane_independent {q1 q2 : ℕ} (h1 : 0 < q1) (h2 : 0 < q2) (c d : ℕ) :
    endpointCovariance q1 q2 c = endpointCovariance q1 q2 d := by
  rw [endpointCovariance_exact h1 h2 c, endpointCovariance_exact h1 h2 d]

/-- **`endpointCovariance_odd`.**  `KERNEL-PROVED`.  The specialisation used by the source:
odd moduli `q₁, q₂` in a permitted lane `c`. -/
theorem endpointCovariance_odd {q1 q2 : ℕ} (h1 : Odd q1) (h2 : Odd q2) (c : ℕ) :
    endpointCovariance q1 q2 c = ((Nat.gcd q1 q2 : ℚ) ^ 2 - 1) / (12 * (q1 : ℚ) * (q2 : ℚ)) :=
  endpointCovariance_exact h1.pos h2.pos c

/-- **`endpointCovariance_odd_coprime_or_stratum`.**  `KERNEL-PROVED`.  For odd moduli the
covariance vanishes exactly on the coprime stratum: if `gcd(q₁,q₂) > 1` the covariance is
strictly positive. -/
theorem endpointCovariance_pos_of_gcd_gt_one {q1 q2 : ℕ} (h1 : 0 < q1) (h2 : 0 < q2)
    (hgcd : 1 < Nat.gcd q1 q2) (c : ℕ) : 0 < endpointCovariance q1 q2 c := by
  rw [endpointCovariance_exact h1 h2 c]
  have hg' : (1 : ℚ) < (Nat.gcd q1 q2 : ℚ) := by exact_mod_cast hgcd
  have hnum : 0 < ((Nat.gcd q1 q2 : ℚ)) ^ 2 - 1 := by nlinarith
  have hq1 : (0 : ℚ) < q1 := by exact_mod_cast h1
  have hq2 : (0 : ℚ) < q2 := by exact_mod_cast h2
  positivity

end Effectivity
end Erdos287
