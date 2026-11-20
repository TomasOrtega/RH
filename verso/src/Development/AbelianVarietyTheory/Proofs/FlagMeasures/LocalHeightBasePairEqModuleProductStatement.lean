import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHeightBasePairEqModuleProduct
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HTPlaceLeaf.htPlace` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLocalHeightBasePairEqModuleProduct.lean&line=231#L231)
-/
theorem _root_.GlobalTheory.T.local_height_base_pair_eq_module_product : Formalism.L2.SG.NGHTie.HTPlace := by
  first | exact @GlobalTheory.HTPlaceLeaf.htPlace | exact GlobalTheory.HTPlaceLeaf.htPlace | (intros; apply GlobalTheory.HTPlaceLeaf.htPlace <;> assumption)
