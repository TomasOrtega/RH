import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagonalComplementSecondProjectionIsFiniteEtale
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | (exact @GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale) | (exact GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale) | (intros; apply GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.diagonalComplementSecondProjection_isFinite_etale : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f], IsFinite (GlobalTheory.EtC.Tr.diagComplHom f) ∧ Etale (GlobalTheory.EtC.Tr.diagComplHom f) := by
  first | (exact @GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale) | (exact GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale) | (intros; apply GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale  <;> assumption)
