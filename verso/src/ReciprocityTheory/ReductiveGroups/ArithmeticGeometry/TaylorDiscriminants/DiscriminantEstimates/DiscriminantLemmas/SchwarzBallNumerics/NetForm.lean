import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ScaledBoundInequalityHypothesesOne

namespace PI.UnitaryGroupMassFormula.TBNum

open ComplexConjugate

/- English proof (translation)
Introduce `V _ _ ι _ ev`. Establish `hF : ∀ F, ReciprocityTheory.ChartRestriction.G.TB.netForm ev F F = (((Fintype.card ι : ℝ)⁻¹ * ∑ y, Complex.normSq (ev y F) : ℝ) : ℂ)`. Introduce `F`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.TB.netForm, Complex.mul_conj]`. Use `push_cast`.

Both sides reduce to the same expression. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `F G`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.TB.netForm, map_mul, map_sum, map_inv₀, map_natCast, Complex.conj_conj]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Introduce `F`. Rewrite using `[hF, Complex.ofReal_im, Complex.ofReal_re]`. Conclude with `⟨rfl, mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun y _ => Complex.normSq_nonneg _)⟩`.

Introduce `hinj F h0`. Apply `hinj F` to reduce the goal to its premises. Introduce `y`. Rewrite `h0` using `[hF, Complex.ofReal_eq_zero]`. Establish `hne : (Fintype.card ι : ℝ) ≠ 0`.

Establish `: 0 < Fintype.card ι` using `Fintype.card_pos_iff.2 ⟨y⟩`. Conclude with `this.ne'` after adjusting the coercions. Establish `hs : ∑ y, Complex.normSq (ev y F) = 0`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `absurd (inv_eq_zero.1 h) hne`.

Conclude with `h`. Use `(Finset.sum_eq_zero_iff_of_nonneg (fun y _ => Complex.normSq_nonneg (ev y F))).1 hs y (Finset.mem_univ y)` as an intermediate fact. Conclude with `Complex.normSq_eq_zero.1 this`.
-/
theorem netHerm : ReciprocityTheory.ChartRestriction.G.TB.NetHermSt := by
  intro V _ _ ι _ ev
  have hF : ∀ F, ReciprocityTheory.ChartRestriction.G.TB.netForm ev F F
      = (((Fintype.card ι : ℝ)⁻¹ * ∑ y, Complex.normSq (ev y F) : ℝ) : ℂ) := by
    intro F
    simp only [ReciprocityTheory.ChartRestriction.G.TB.netForm, Complex.mul_conj]
    push_cast
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro F G
    simp only [ReciprocityTheory.ChartRestriction.G.TB.netForm, map_mul, map_sum, map_inv₀, map_natCast,
      Complex.conj_conj]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  · intro F
    rw [hF, Complex.ofReal_im, Complex.ofReal_re]
    exact ⟨rfl, mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun y _ => Complex.normSq_nonneg _)⟩
  · intro hinj F h0
    apply hinj F
    intro y
    rw [hF, Complex.ofReal_eq_zero] at h0
    have hne : (Fintype.card ι : ℝ) ≠ 0 := by
      have : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨y⟩
      exact_mod_cast this.ne'
    have hs : ∑ y, Complex.normSq (ev y F) = 0 := by
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd (inv_eq_zero.1 h) hne
      · exact h
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => Complex.normSq_nonneg (ev y F))).1 hs y
      (Finset.mem_univ y)
    exact Complex.normSq_eq_zero.1 this

end PI.UnitaryGroupMassFormula.TBNum
