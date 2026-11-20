import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyFractionalIdealRealLatticeImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
import Formalism.LatticeTheta.Statement
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDiscreteTopologyFractionalIdealRealLatticeImage.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.discreteTopology_fractionalIdealRealLatticeImage : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F), DiscreteTopology (latOf N) := by
  first | exact @GlobalTheory.LipschitzTR.discrete_latOf | exact GlobalTheory.LipschitzTR.discrete_latOf | (intros; apply GlobalTheory.LipschitzTR.discrete_latOf <;> assumption)
