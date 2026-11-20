import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightFunctionsExist
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.height_functions_exist : HtExist := by
  first | exact @GlobalTheory.CompanionTheory.HtEx.htExist | exact GlobalTheory.CompanionTheory.HtEx.htExist | (intros; apply GlobalTheory.CompanionTheory.HtEx.htExist <;> assumption)
