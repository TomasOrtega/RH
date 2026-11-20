import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarAdditionFormulaPadicModelParameter
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SigmaAdd.sigma_add_param` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSigmaStarAdditionFormulaPadicModelParameter.lean&line=172#L172)
-/
theorem _root_.GlobalTheory.T.sigmaStar_addition_formula_padic_modelParameter : ∀ D : D7, Formalism.MainNotions.Ext.CutA.PAdicSigmaAdditionFormula D := by
  first | exact @GlobalTheory.SigmaAdd.sigma_add_param | exact GlobalTheory.SigmaAdd.sigma_add_param | (intros; apply GlobalTheory.SigmaAdd.sigma_add_param <;> assumption)
