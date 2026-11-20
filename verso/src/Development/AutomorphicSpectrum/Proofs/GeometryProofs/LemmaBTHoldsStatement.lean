import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LemmaBTHolds
import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.Ar.BT.lemmaBT_holds | exact GlobalTheory.CompanionTheory.Ar.BT.lemmaBT_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.lemmaBT_holds <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.LemmaBT_holds : GlobalTheory.CompanionTheory.Ar.BT.LemmaBT := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.lemmaBT_holds | exact GlobalTheory.CompanionTheory.Ar.BT.lemmaBT_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.lemmaBT_holds <;> assumption)
