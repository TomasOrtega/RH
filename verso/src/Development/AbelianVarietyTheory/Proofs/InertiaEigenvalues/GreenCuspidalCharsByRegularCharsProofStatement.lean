import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenCuspidalCharsByRegularCharsProof
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.greenCuspidalCharsByRegularChars_proof : GlobalTheory.Published.GreenRegularCharacters := by
  first | exact @GlobalTheory.greenRegularCharacters_holds | exact GlobalTheory.greenRegularCharacters_holds | (intros; apply GlobalTheory.greenRegularCharacters_holds <;> assumption)
