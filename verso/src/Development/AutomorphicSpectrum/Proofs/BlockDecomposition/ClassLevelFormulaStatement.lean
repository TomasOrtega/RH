import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClassLevelFormula
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.class_level_formula : PositivityTheory.SiegelWeilFormula.Gunr.ClassLev := by
  first | exact @GlobalTheory.CompanionTheory.GunrClassLev.classLev | exact GlobalTheory.CompanionTheory.GunrClassLev.classLev | (intros; apply GlobalTheory.CompanionTheory.GunrClassLev.classLev <;> assumption)
