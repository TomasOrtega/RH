import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedLocalFormula
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.UnrDens.unrFormula | exact GlobalTheory.CompanionTheory.UnrDens.unrFormula | (intros; apply GlobalTheory.CompanionTheory.UnrDens.unrFormula <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.unramified_local_formula : PositivityTheory.PfSWUS.Loc.UnrFormula := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.unrFormula | exact GlobalTheory.CompanionTheory.UnrDens.unrFormula | (intros; apply GlobalTheory.CompanionTheory.UnrDens.unrFormula <;> assumption)
