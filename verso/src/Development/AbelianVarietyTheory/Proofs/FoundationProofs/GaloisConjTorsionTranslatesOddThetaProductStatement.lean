import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisConjTorsionTranslatesOddThetaProduct
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ProdThetaConj.galB_all` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FGaloisConjTorsionTranslatesOddThetaProduct.lean&line=408#L408)
-/
theorem _root_.GlobalTheory.T.galois_conj_torsionTranslates_oddThetaProduct : ∀ D : D7, galB D := by
  first | exact @GlobalTheory.ProdThetaConj.galB_all | exact GlobalTheory.ProdThetaConj.galB_all | (intros; apply GlobalTheory.ProdThetaConj.galB_all <;> assumption)
