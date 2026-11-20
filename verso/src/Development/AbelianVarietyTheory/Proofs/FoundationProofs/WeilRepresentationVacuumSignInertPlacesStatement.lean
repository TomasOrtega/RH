import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlaces
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FWeilRepresentationVacuumSignInertPlaces.lean&line=254#L254)
-/
theorem _root_.GlobalTheory.T.weilRepresentation_vacuum_sign_inert_places : ∀ D : D7, odd3 D := by
  first | exact @GlobalTheory.InertSign.vacuum_inert | exact GlobalTheory.InertSign.vacuum_inert | (intros; apply GlobalTheory.InertSign.vacuum_inert <;> assumption)
