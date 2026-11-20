import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionSurjectiveAdditiveLinear
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PerfFil.Expand.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExpansionSurjectiveAdditiveLinear.lean&line=129#L129)
-/
theorem _root_.GlobalTheory.T.expansion_surjective_additive_linear : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), Function.Surjective A.expand ∧ (∀ c c' : ℕ →₀ A.A, A.expand (c + c') = A.expand c + A.expand c') ∧ (∀ (a : A.A) (c : ℕ →₀ A.A), A.expand (a • c) = A.aTo1 a * A.expand c) ∧ ∀ k, A.aTo1 (A.pi ^ l) * A.dxi 1 k = 0 := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.Expand.main | exact GlobalTheory.CompanionTheory.PerfFil.Expand.main | (intros; apply GlobalTheory.CompanionTheory.PerfFil.Expand.main <;> assumption)
