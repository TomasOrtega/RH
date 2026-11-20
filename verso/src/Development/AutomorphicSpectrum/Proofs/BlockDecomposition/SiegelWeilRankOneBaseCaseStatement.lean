import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilRankOneBaseCase
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.Base1.baseOne_of_parts | exact GlobalTheory.CompanionTheory.Base1.baseOne_of_parts | (intros; apply GlobalTheory.CompanionTheory.Base1.baseOne_of_parts <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.siegel_weil_rank_one_base_case : Prop1 → Simil → Hasse → Cnt → PositivityTheory.SiegelWeilFormula.Densx.BaseOne := by
  first | exact @GlobalTheory.CompanionTheory.Base1.baseOne_of_parts | exact GlobalTheory.CompanionTheory.Base1.baseOne_of_parts | (intros; apply GlobalTheory.CompanionTheory.Base1.baseOne_of_parts <;> assumption)
