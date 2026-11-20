import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProductModulesTypeUniformisersEqPower
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FProductModulesTypeUniformisersEqPower.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.product_modules_type_uniformisers_eq_power : Formalism.L2.SG.NGHTie.HTTheta := by
  first | exact @GlobalTheory.HTThetaLeaf.main | exact GlobalTheory.HTThetaLeaf.main | (intros; apply GlobalTheory.HTThetaLeaf.main <;> assumption)
