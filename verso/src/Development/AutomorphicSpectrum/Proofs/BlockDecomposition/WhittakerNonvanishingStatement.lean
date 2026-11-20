import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerNonvanishing
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.WhNe.sNe | exact GlobalTheory.CompanionTheory.WhNe.sNe | (intros; apply GlobalTheory.CompanionTheory.WhNe.sNe <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.whittaker_nonvanishing : Ad3.SchwartzSpaceL2.SNe := by
  first | exact @GlobalTheory.CompanionTheory.WhNe.sNe | exact GlobalTheory.CompanionTheory.WhNe.sNe | (intros; apply GlobalTheory.CompanionTheory.WhNe.sNe <;> assumption)
