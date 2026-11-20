import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalBasisGaloisMap
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NormSum.onB_map_aut` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FOrthonormalBasisGaloisMap.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.orthonormalBasis_galois_map : ∀ (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E), (∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E)) → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → OnB D (fun j => (b j).map σ) := by
  first | exact @GlobalTheory.NormSum.onB_map_aut | exact GlobalTheory.NormSum.onB_map_aut | (intros; apply GlobalTheory.NormSum.onB_map_aut <;> assumption)
