import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistAutHolds
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut | exact GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut | (intros; apply GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.TwistAut_holds : GlobalTheory.CompanionTheory.Ar.TwistAut := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut | exact GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut | (intros; apply GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut <;> assumption)
