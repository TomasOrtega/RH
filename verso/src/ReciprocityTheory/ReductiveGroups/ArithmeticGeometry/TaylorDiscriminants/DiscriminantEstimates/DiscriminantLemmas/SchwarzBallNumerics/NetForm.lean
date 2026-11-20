import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ScaledBoundInequalityHypothesesOne

namespace PI.UnitaryGroupMassFormula.TBNum

open ComplexConjugate

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations.

Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments.

Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. A detailed English derivation is pending.
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
