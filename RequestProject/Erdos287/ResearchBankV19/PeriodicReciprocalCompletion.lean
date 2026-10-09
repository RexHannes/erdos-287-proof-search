import Mathlib

/-!
# Erdős #287 — Research Bank V19 §5: periodic reciprocal completion (E1 repair)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Input: modulus `n`, period `V` with `gcd(n, V) = 1`, a `V`-periodic coefficient `ω` (a function on
`ZMod V`), a finite set `I` of integers (e.g. a consecutive interval), and the reciprocal phase
`e_n(A ū)` on units.  Put `N = nV` and let `ψ = ZMod.stdAddChar` (the primitive additive character
`x ↦ e(x/N)` of Mathlib).

Kernel-proved (LEAN BANK):
* **`completion`** — the exact finite completion identity for every `F : ZMod N → ℂ`:
  `∑_{u∈I} F(u) = N⁻¹ ∑_{k mod N} F̂(k) G_I(k)` with `F̂(k) = ∑_x F(x) ψ(−kx)` (complete sum)
  and `G_I(k) = ∑_{u∈I} ψ(ku)` (geometric-sum factor);
* `completion_bound` — `‖∑_{u∈I} F(u)‖ ≤ N⁻¹ ∑_k ‖F̂(k)‖ ‖G_I(k)‖`;
* `Fper_apply` — the incomplete periodic reciprocal sum is `∑_{u∈I} F(u)` for the explicit
  `F = Fper n V ω A` on `ZMod (nV)`.

LEAN CONDITIONAL:
* `periodic_completion_bound` — from `CompleteKloostermanProvider` (the complete-sum bound
  `‖F̂(k)‖ ≤ B`, i.e. the Weil/Ramanujan input for the complete Kloosterman data, which is NOT in
  Mathlib and is never stated as an axiom): `‖∑_{u∈I} ω(u) e_n(A ū)‖ ≤ (B/N) ∑_k ‖G_I(k)‖`.

The CRT factorization of `F̂(k)` into a Kloosterman sum mod `n` times `ω̂` mod `V` is not
formalized here; the provider contract bounds `F̂` directly.
-/

namespace Erdos287
namespace ResearchBankV19
namespace PeriodicReciprocalCompletion

section Completion

variable {N : ℕ} [NeZero N]

/-- The complete sum `F̂(k) = ∑_x F(x) ψ(−k x)`. -/
noncomputable def hat (F : ZMod N → ℂ) (k : ZMod N) : ℂ :=
  ∑ x : ZMod N, F x * ZMod.stdAddChar (-(k * x))

/-- The geometric-sum factor `G_I(k) = ∑_{u∈I} ψ(k u)`. -/
noncomputable def geom (I : Finset ℤ) (k : ZMod N) : ℂ :=
  ∑ u ∈ I, ZMod.stdAddChar (k * (u : ZMod N))

theorem orth (b : ZMod N) :
    ∑ k : ZMod N, (ZMod.stdAddChar (k * b) : ℂ) = if b = 0 then (N : ℂ) else 0 := by
  rw [AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar N)]
  split_ifs <;> simp [ZMod.card]

theorem completion_key (F : ZMod N → ℂ) (I : Finset ℤ) :
    ∑ k : ZMod N, hat F k * geom I k = (N : ℂ) * ∑ u ∈ I, F u := by
  unfold hat geom
  calc ∑ k : ZMod N, (∑ x : ZMod N, F x * ZMod.stdAddChar (-(k * x))) *
        ∑ u ∈ I, (ZMod.stdAddChar (k * (u : ZMod N)) : ℂ)
      = ∑ k : ZMod N, ∑ x : ZMod N, ∑ u ∈ I,
          F x * (ZMod.stdAddChar (k * ((u : ZMod N) - x)) : ℂ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun u _ => ?_
        rw [mul_assoc, ← AddChar.map_add_eq_mul]
        congr 2; ring
    _ = ∑ x : ZMod N, ∑ u ∈ I, ∑ k : ZMod N,
          F x * (ZMod.stdAddChar (k * ((u : ZMod N) - x)) : ℂ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ x : ZMod N, ∑ u ∈ I, F x * (if (u : ZMod N) = x then (N : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun u _ => ?_
        rw [← Finset.mul_sum, orth]
        simp only [sub_eq_zero]
    _ = ∑ u ∈ I, ∑ x : ZMod N, F x * (if (u : ZMod N) = x then (N : ℂ) else 0) :=
        Finset.sum_comm
    _ = (N : ℂ) * ∑ u ∈ I, F u := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        simp_rw [mul_ite, mul_zero]
        rw [Finset.sum_ite_eq]
        simp [mul_comm]

/-- **The exact completion identity.** -/
theorem completion (F : ZMod N → ℂ) (I : Finset ℤ) :
    ∑ u ∈ I, F u = (N : ℂ)⁻¹ * ∑ k : ZMod N, hat F k * geom I k := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [completion_key, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-- **Completion bound.** -/
theorem completion_bound (F : ZMod N → ℂ) (I : Finset ℤ) :
    ‖∑ u ∈ I, F u‖ ≤ (N : ℝ)⁻¹ * ∑ k : ZMod N, ‖hat F k‖ * ‖geom I k‖ := by
  rw [completion, norm_mul, norm_inv, Complex.norm_natCast]
  gcongr
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp_rw [norm_mul]

end Completion

section Periodic

variable {n V : ℕ} [NeZero n] [NeZero (n * V)]

/-- The reciprocal phase on `ZMod n`: `y ↦ e_n(A y⁻¹)` on units, `0` off units. -/
noncomputable def recip (A : ZMod n) (y : ZMod n) : ℂ :=
  if IsUnit y then (ZMod.stdAddChar (A * y⁻¹) : ℂ) else 0

/-- The completed function `F(x) = ω(x mod V) · recip(x mod n)` on `ZMod (nV)`. -/
noncomputable def Fper (n V : ℕ) [NeZero n] (ω : ZMod V → ℂ) (A : ZMod n) (x : ZMod (n * V)) : ℂ :=
  ω (ZMod.cast x) * recip A (ZMod.cast x)

omit [NeZero (n * V)] in
theorem Fper_apply (ω : ZMod V → ℂ) (A : ZMod n) (u : ℤ) :
    Fper n V ω A (u : ZMod (n * V)) = ω (u : ZMod V) * recip A (u : ZMod n) := by
  unfold Fper
  rw [ZMod.cast_intCast (Dvd.intro_left n rfl), ZMod.cast_intCast (Dvd.intro V rfl)]

/-- **The complete Kloosterman provider** (EXTERNAL PROVIDER; Weil / Ramanujan complete-sum
bound for the completed periodic reciprocal function; never an axiom, never constructed). -/
structure CompleteKloostermanProvider (n V : ℕ) [NeZero n] [NeZero (n * V)] (ω : ZMod V → ℂ)
    (A : ZMod n) (B : ℝ) : Prop where
  complete_bound : ∀ k : ZMod (n * V), ‖hat (Fper n V ω A) k‖ ≤ B

/-- **Periodic completion bound** (LEAN CONDITIONAL on the complete-sum provider). -/
theorem periodic_completion_bound (ω : ZMod V → ℂ) (A : ZMod n) {B : ℝ}
    (P : CompleteKloostermanProvider n V ω A B) (I : Finset ℤ) :
    ‖∑ u ∈ I, ω (u : ZMod V) * recip A (u : ZMod n)‖ ≤
      (B / (n * V : ℕ)) * ∑ k : ZMod (n * V), ‖geom I k‖ := by
  have h := completion_bound (Fper n V ω A) I
  simp_rw [Fper_apply] at h
  refine h.trans ?_
  rw [div_eq_inv_mul, mul_assoc]
  gcongr
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (P.complete_bound k) (norm_nonneg _)

end Periodic

end PeriodicReciprocalCompletion
end ResearchBankV19
end Erdos287
