import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapsSurjectiveWithKernels
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FQuotientMapsSurjectiveWithKernels.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.quotient_maps_surjective_with_kernels : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), Function.Surjective (A.uToQ n) ∧ RingHom.ker (A.uToQ n) = Ideal.span {(l : A.U) ^ n} ∧ Function.Surjective (A.uToPQ n) ∧ (n ≠ 0 → RingHom.ker (A.uToPQ n) = Ideal.span {(l : A.U)}) := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.uToQ_main | exact GlobalTheory.CompanionTheory.Untilt.uToQ_main | (intros; apply GlobalTheory.CompanionTheory.Untilt.uToQ_main <;> assumption)
