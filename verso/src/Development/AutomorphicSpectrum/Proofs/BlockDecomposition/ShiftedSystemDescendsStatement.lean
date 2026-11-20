import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedSystemDescends
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.KunGlue.ShDesc.sh_desc` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FShiftedSystemDescends.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.shifted_system_descends : ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] (ς : ℤˣ) (k : ℕ) (A : Sy.{1} K ι), A.Desc → (shSy ς k A).Desc := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.ShDesc.sh_desc | exact GlobalTheory.CompanionTheory.KunGlue.ShDesc.sh_desc | (intros; apply GlobalTheory.CompanionTheory.KunGlue.ShDesc.sh_desc <;> assumption)
