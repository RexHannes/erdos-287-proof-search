import RequestProject.Erdos287.ResearchBankV14.BalancedBlowup
import RequestProject.Erdos287.ResearchBankV14.EdgeOnlyCompilerInterface
import RequestProject.Erdos287.ResearchBankV14.ConditionalAsymptoticImplication

/-!
# Erdős #287 — Research Bank V14 §A4 (application): the compiler on the fixed blow-up

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The edge-only compiler (`EdgeOnlyCompilerInterface.edgeOnly_compiler`) is instantiated
symbolically on the balanced 11-cell blow-up of `G(11,2)` on `K = 2^4170` coordinates, with the
macro boxes `(r + 1 − 1/100, r + 1 + 1/100)` of the contact annulus.

* `compiler_exists` — **compiler existence**: there is a `CompilerOutput` (scale `T`, offsets
  `b`, translation `A ≥ 1000 · max b`) with every blow-up edge satisfying
  `gcd(a_u, a_v) = |a_u − a_v|`, `a_v = A + b_v`;
* `fixedOutput` — the fixed output (chosen once, `Classical.choice`); `compilerTuple` — the fixed
  tuple packaged as a `FixedTuple (Fin K)`: the edge identity, `a_v ≥ 1000`, the contact-ratio
  bound `≤ R*` and an edge are all *proved* from the boxes (`edge_oriented_bounds`,
  `tuple_ratio`);
* `compilerTuple_conditional` — the V14 conditional implication for this fixed tuple.

**Firewall.**  Existence only.  The construction is computable in principle, but no
quantitatively useful height bound on `T` or `A` is claimed (OPEN).
-/

namespace Erdos287
namespace ResearchBankV14
namespace CompilerApplication

open BalancedKernelParameters MacroGraph11 BalancedBlowup EdgeOnlyCompilerInterface
open ContactAnnulus ConditionalAsymptoticImplication

/-- Lower end of the box of coordinate `i` (its macro cell's box). -/
def lo (i : Fin K) : ℚ := boxLo (cell i).val

/-- Upper end of the box of coordinate `i`. -/
def hi (i : Fin K) : ℚ := boxHi (cell i).val

theorem lo_lt_hi (i : Fin K) : lo i < hi i := by
  unfold lo hi boxLo boxHi eps; linarith

theorem lo_pos (i : Fin K) : 0 < lo i := by
  unfold lo boxLo eps
  have : (0 : ℚ) ≤ (cell i).val := by positivity
  linarith

/-- A compiler output on the blow-up. -/
structure CompilerOutput where
  T : ℕ
  b : Fin K → ℤ
  A : ℤ
  T_pos : 0 < T
  box : ∀ v, lo v * T < b v ∧ (b v : ℚ) < hi v * T
  distinct : ∀ u v, u ≠ v → b u ≠ b v
  A_large : ∀ v, 1000 * b v ≤ A
  edge : ∀ u v, blowup.Adj u v → Int.gcd (A + b u) (A + b v) = (b u - b v).natAbs

/-- **Compiler existence** (from the edge-only compiler theorem). -/
theorem compiler_exists : Nonempty CompilerOutput := by
  obtain ⟨T, b, hT, -, hbox, hdist, hA⟩ := edgeOnly_compiler blowup lo hi lo_lt_hi 1
  obtain ⟨A, hA0, hedge⟩ := hA (1000 * ∑ v, |b v|)
  refine ⟨⟨T, b, A, hT, hbox, hdist, fun v => le_trans ?_ hA0, hedge⟩⟩
  have h1 : b v ≤ |b v| := le_abs_self _
  have h2 : |b v| ≤ ∑ w, |b w| :=
    Finset.single_le_sum (f := fun w => |b w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ v)
  linarith

/-- The fixed compiler output. -/
noncomputable def fixedOutput : CompilerOutput := Classical.choice compiler_exists

namespace CompilerOutput

variable (O : CompilerOutput)

theorem b_pos (v : Fin K) : 0 < O.b v := by
  have h := (O.box v).1
  have hT : (0 : ℚ) < O.T := by exact_mod_cast O.T_pos
  have : (0 : ℚ) < O.b v := lt_trans (mul_pos (lo_pos v) hT) h
  exact_mod_cast this

theorem A_pos : 1000 ≤ O.A := by
  obtain ⟨v⟩ : Nonempty (Fin K) := ⟨⟨0, K_pos⟩⟩
  have := O.b_pos v; have := O.A_large v; omega

/-- The tuple `a_v = A + b_v` (as naturals). -/
def a (v : Fin K) : ℕ := (O.A + O.b v).toNat

theorem a_cast (v : Fin K) : ((O.a v : ℕ) : ℤ) = O.A + O.b v := by
  unfold a; have := O.b_pos v; have := O.A_pos; omega

theorem a_ge (v : Fin K) : 1000 ≤ O.a v := by
  have h := O.a_cast v; have := O.b_pos v; have := O.A_pos; omega

theorem a_lt_iff (u v : Fin K) : O.a u < O.a v ↔ O.b u < O.b v := by
  have h1 := O.a_cast u; have h2 := O.a_cast v; omega

/-- **Oriented edge bounds**: on a blow-up edge with `a_u < a_v`, the cells are ordered and
`149/50 T < b_v − b_u < 401/50 T`. -/
theorem edge_oriented_bounds {u v : Fin K} (h : blowup.Adj u v) (hlt : O.b u < O.b v) :
    149 / 50 * (O.T : ℚ) < O.b v - O.b u ∧ ((O.b v - O.b u : ℤ) : ℚ) < 401 / 50 * O.T := by
  have hT : (0 : ℚ) < O.T := by exact_mod_cast O.T_pos
  have hadj : G11.Adj (cell u) (cell v) := h
  have hlt' : (O.b u : ℚ) < O.b v := by exact_mod_cast hlt
  rcases lt_or_gt_of_ne (G11.ne_of_adj hadj) with hc | hc
  · obtain ⟨h1, h2⟩ := adj_oriented hadj hc
    obtain ⟨e1, e2⟩ := scaled_edge_difference h1 h2 hT (O.box u) (O.box v)
    push_cast; exact ⟨e1, e2⟩
  · obtain ⟨h1, h2⟩ := adj_oriented (G11.symm hadj) hc
    obtain ⟨e1, -⟩ := scaled_edge_difference h1 h2 hT (O.box v) (O.box u)
    exfalso; nlinarith

theorem edge_gcd {u v : Fin K} (h : blowup.Adj u v) (hlt : O.a u < O.a v) :
    Nat.gcd (O.a u) (O.a v) = O.a v - O.a u := by
  have he := O.edge u v h
  rw [← O.a_cast u, ← O.a_cast v, Int.gcd_natCast_natCast] at he
  rw [he]
  have h1 := O.a_cast u; have h2 := O.a_cast v
  omega

theorem coeff_cast {u v : Fin K} (h : blowup.Adj u v) (hlt : O.a u < O.a v) :
    (coeff O.a u v : ℚ) = (O.a u : ℚ) / ((O.a v : ℚ) - O.a u) := by
  unfold coeff
  have hd : (O.a v - O.a u) ∣ O.a u := by rw [← O.edge_gcd h hlt]; exact Nat.gcd_dvd_left _ _
  rw [Nat.cast_div hd (by exact_mod_cast (show O.a v - O.a u ≠ 0 by omega))]
  rw [Nat.cast_sub hlt.le]

/-- **The contact-ratio bound `≤ R*`** for the compiler tuple. -/
theorem tuple_ratio {u v u' v' : Fin K} (h : blowup.Adj u v) (hlt : O.a u < O.a v)
    (h' : blowup.Adj u' v') (hlt' : O.a u' < O.a v') :
    (coeff O.a u v : ℚ) * O.a v ≤ Rstar * ((coeff O.a u' v' : ℚ) * O.a v') := by
  rw [O.coeff_cast h hlt, O.coeff_cast h' hlt']
  have hb := (O.a_lt_iff u v).1 hlt
  have hb' := (O.a_lt_iff u' v').1 hlt'
  obtain ⟨d1, -⟩ := O.edge_oriented_bounds h hb
  obtain ⟨-, d2'⟩ := O.edge_oriented_bounds h' hb'
  have cast : ∀ w, ((O.a w : ℕ) : ℚ) = O.A + O.b w := fun w => by
    have := O.a_cast w; exact_mod_cast this
  have hbw : ∀ w, (0 : ℚ) < O.b w := fun w => by exact_mod_cast O.b_pos w
  have hAw : ∀ w, 1000 * (O.b w : ℚ) ≤ O.A := fun w => by exact_mod_cast O.A_large w
  have hT : (0 : ℚ) < O.T := by exact_mod_cast O.T_pos
  apply contact_coeff_ratio
  · rw [cast]; linarith [hbw u', hAw u']
  · rw [cast]; linarith [hbw v', hAw v']
  · rw [cast, cast]; linarith
  · have hb'q : (O.b u' : ℚ) < O.b v' := by exact_mod_cast hb'
    rw [cast, cast]; linarith
  · rw [cast, cast]; exact ratio_of_translation (hbw u') (hAw u)
  · rw [cast, cast]; exact ratio_of_translation (hbw v') (hAw v)
  · rw [cast, cast, cast, cast]; push_cast at d1 d2'; nlinarith
  · positivity

theorem has_edge : ∃ u v, OE O.a cell u v := by
  have h11 := eleven_le_K
  have hij : G11.Adj (cell ⟨0, by omega⟩) (cell ⟨3, by omega⟩) := by
    have hi : cell ⟨0, by omega⟩ = 0 := Fin.ext rfl
    have hj : cell ⟨3, by omega⟩ = 3 := Fin.ext rfl
    rw [hi, hj]; decide
  have hne : O.a ⟨0, by omega⟩ ≠ O.a ⟨3, by omega⟩ := by
    intro h
    have := O.distinct ⟨0, by omega⟩ ⟨3, by omega⟩
      (fun e => absurd (congrArg Fin.val e) (show ¬ (0 = 3) by decide))
    have h1 := O.a_cast ⟨0, by omega⟩; have h2 := O.a_cast ⟨3, by omega⟩
    omega
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨_, _, hij, hlt⟩
  · exact ⟨_, _, G11.symm hij, hlt⟩

/-- A compiler output as a `FixedTuple`. -/
noncomputable def toFixedTuple : FixedTuple (Fin K) where
  a := O.a
  cell := cell
  a_ge := O.a_ge
  adj_ne u v h := by
    intro e
    have := O.distinct u v (blowup.ne_of_adj h)
    have h1 := O.a_cast u; have h2 := O.a_cast v
    omega
  edge_gcd u v h hlt := O.edge_gcd h hlt
  ratio u v u' v' h h' := O.tuple_ratio h.1 h.2 h'.1 h'.2
  has_edge := O.has_edge

end CompilerOutput

/-- **The fixed compiler tuple** (the fixed affine system `L_v(t) = a_v t + 1` of V15). -/
noncomputable def compilerTuple : FixedTuple (Fin K) := fixedOutput.toFixedTuple

/-- **The conditional implication for the fixed compiler tuple.** -/
theorem compilerTuple_conditional (W : WeightSystem compilerTuple) (N : ℕ → ℝ)
    (B : CertifiedFunctionalBounds) (h0 : S0Contract (S0 compilerTuple W) N)
    (h1 : S1Contract (S1 compilerTuple W) N B.muF)
    (hP : ActualWeightedColouredPairProvider compilerTuple W N B.WF) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ResearchBankV13.FiniteRepresentationModel.NoCounterexampleAt M :=
  eventually_no_counterexample compilerTuple W N B h0 h1 hP

end CompilerApplication
end ResearchBankV14
end Erdos287
