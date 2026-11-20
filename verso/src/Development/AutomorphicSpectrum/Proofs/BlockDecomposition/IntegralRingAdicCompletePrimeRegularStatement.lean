import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRingAdicCompletePrimeRegular
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TiltCompl.complete_tf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIntegralRingAdicCompletePrimeRegular.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.integral_ring_adic_complete_prime_regular : ∀ {l : ℕ} [Fact l.Prime], IsAdicComplete (Ideal.span {pFlat l}) (Ob l) ∧ pFlat l ∈ nonZeroDivisors (Ob l) := by
  first | exact @GlobalTheory.CompanionTheory.TiltCompl.complete_tf | exact GlobalTheory.CompanionTheory.TiltCompl.complete_tf | (intros; apply GlobalTheory.CompanionTheory.TiltCompl.complete_tf <;> assumption)
