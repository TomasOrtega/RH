import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltAdicComplete
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUntiltAdicComplete.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.untilt_adic_complete : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), IsAdicComplete (Ideal.span {(l : A.U)}) A.U := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U | exact GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U | (intros; apply GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U <;> assumption)
