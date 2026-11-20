import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSquareEvenThetaConjugateLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FMeanSquareEvenThetaConjugateLattice.lean&line=107#L107)
-/
theorem _root_.GlobalTheory.T.meanSquare_evenTheta_conjugateLattice : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → ∀ t : ℂ, nrm1Sq (Λ.map (starRingEnd ℂ).toAddMonoidHom) (GL3Theta.th0 (Λ.map (starRingEnd ℂ).toAddMonoidHom) ((starRingEnd ℂ) t)) = nrm1Sq Λ (GL3Theta.th0 Λ t) := by
  first | exact @GlobalTheory.MeanSquareConj.nrm1Sq_th0_map_conj_eq | exact GlobalTheory.MeanSquareConj.nrm1Sq_th0_map_conj_eq | (intros; apply GlobalTheory.MeanSquareConj.nrm1Sq_th0_map_conj_eq <;> assumption)
