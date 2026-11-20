import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisConjTaylorThetaTranslate
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FGaloisConjTaylorThetaTranslate.lean&line=181#L181)
-/
theorem _root_.GlobalTheory.T.galois_conj_taylor_thetaTranslate : ∀ D : D7, gal1 D := by
  first | exact @GlobalTheory.JetConj.galois_translate_sgStar | exact GlobalTheory.JetConj.galois_translate_sgStar | (intros; apply GlobalTheory.JetConj.galois_translate_sgStar <;> assumption)
