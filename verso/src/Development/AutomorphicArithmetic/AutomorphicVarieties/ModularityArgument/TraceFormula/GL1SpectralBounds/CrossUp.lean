import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.IntegralityGoodReduction
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsRigClosed

open PositivityTheory.RgJS UpperTheory.V.Z.Tf.GOne
open scoped ComplexConjugate

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.V.Z.Tf.GOne.crossUp :
    ExtId → CrossUp := by
  intro hE W q X d A hS x y hxy
  obtain ⟨F, hFa, hFe⟩ := hE W q X d A hS x y
  have hc : ContinuousOn (fun t : ℝ => F t) (Set.Icc 1 2) := fun t ht =>
    ((hFa t (by linarith [ht.1])).continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨M, fun σ h1 h2 => ?_⟩
  have h3 := hM σ ⟨h1.le, h2⟩
  rw [hFe σ h1, if_neg hxy, one_mul, Complex.norm_exp] at h3
  linarith [Real.add_one_le_exp (∑' p, lterm q (A x) (A y) σ p).re]
