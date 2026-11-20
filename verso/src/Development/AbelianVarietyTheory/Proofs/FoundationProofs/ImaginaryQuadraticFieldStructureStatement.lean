import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImaginaryQuadraticFieldStructure
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FourCopies.exists_onB_four` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FImaginaryQuadraticFieldStructure.lean&line=139#L139)
-/
theorem _root_.GlobalTheory.T.exists_orthonormal_frame_var : ∀ (D : D7) (N N' : ℕ), ∃ (m r : ℕ) (b : Fin r → Matrix (Fin N') (Fin (N + m)) D.host.E), OnB D b := by
  first | exact @GlobalTheory.FourCopies.exists_onB_four | exact GlobalTheory.FourCopies.exists_onB_four | (intros; apply GlobalTheory.FourCopies.exists_onB_four <;> assumption)
