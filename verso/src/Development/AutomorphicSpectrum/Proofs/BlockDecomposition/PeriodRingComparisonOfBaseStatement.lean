import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingComparisonOfBase
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BaseAcris.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPeriodRingComparisonOfBase.lean&line=123#L123)
-/
theorem _root_.GlobalTheory.T.period_ring_comparison_of_base : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), IsBase l A → (Function.Bijective A.cris0 ∧ Function.Bijective A.oC) ∧ ∀ n, Function.Surjective (A.cris n) ∧ RingHom.ker (A.cris n) = Ideal.span {(l : Acris l) ^ n} := by
  first | exact @GlobalTheory.CompanionTheory.BaseAcris.main | exact GlobalTheory.CompanionTheory.BaseAcris.main | (intros; apply GlobalTheory.CompanionTheory.BaseAcris.main <;> assumption)
