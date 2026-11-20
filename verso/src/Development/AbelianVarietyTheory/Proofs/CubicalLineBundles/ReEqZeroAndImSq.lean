import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

namespace GlobalTheory.SquareEqNegReIm

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem re_im_of_sq_eq_neg {z : ℂ} {c : ℝ} (hc : 0 ≤ c) (hz : z ^ 2 = -(c : ℂ)) :
    z.re = 0 ∧ z.im ^ 2 = c := by
  have hs : ((Real.sqrt c : ℝ) : ℂ) ^ 2 = (c : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hc]
  have h : z ^ 2 = (((Real.sqrt c : ℝ) : ℂ) * Complex.I) ^ 2 := by
    rw [mul_pow, hs, Complex.I_sq, hz]; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · rw [h]; simp [Real.sq_sqrt hc]
  · rw [h]; simp [Real.sq_sqrt hc]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem re_eq_zero_and_im_sq {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    H.rt0.re = (0 : ℝ) ∧ H.rt0.im ^ (2 : ℕ) = (H.d : ℝ) := by
  refine re_im_of_sq_eq_neg (by positivity) ?_
  rw [H.sqrt_neg_disc_sq]; simp

end GlobalTheory.SquareEqNegReIm
