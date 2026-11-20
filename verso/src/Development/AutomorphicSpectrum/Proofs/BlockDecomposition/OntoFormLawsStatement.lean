import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OntoFormLaws
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
open CrystallineSemistableComparison.Onto
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.onto_form_laws : CrystallineSemistableComparison.Onto.FormLaws := by
  first | exact @GlobalTheory.CompanionTheory.OntoForms.formLaws | exact GlobalTheory.CompanionTheory.OntoForms.formLaws | (intros; apply GlobalTheory.CompanionTheory.OntoForms.formLaws <;> assumption)
