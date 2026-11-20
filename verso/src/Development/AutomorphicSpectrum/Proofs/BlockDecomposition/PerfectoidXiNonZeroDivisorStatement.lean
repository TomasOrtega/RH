import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectoidXiNonZeroDivisor
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPerfectoidXiNonZeroDivisor.lean&line=96#L96)
-/
theorem _root_.GlobalTheory.T.perfectoid_xi_nonZeroDivisor : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), (l : A.U) ∈ nonZeroDivisors A.U ∧ A.xi ∈ nonZeroDivisors A.W ∧ ∀ (n : ℕ) (x : A.W), A.xi * x ∈ Ideal.span {(l : A.W) ^ n} → x ∈ Ideal.span {(l : A.W) ^ n} := by
  first | exact @GlobalTheory.CompanionTheory.UntiltRegular.untilt_regular | exact GlobalTheory.CompanionTheory.UntiltRegular.untilt_regular | (intros; apply GlobalTheory.CompanionTheory.UntiltRegular.untilt_regular <;> assumption)
