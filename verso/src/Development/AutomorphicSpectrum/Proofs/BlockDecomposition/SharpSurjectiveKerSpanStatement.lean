import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpSurjectiveKerSpan
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSharpSurjectiveKerSpan.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.sharp_surjective_ker_span : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), Function.Surjective A.aToU1 ∧ RingHom.ker A.aToU1 = Ideal.span {A.pi} := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker | exact GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker | (intros; apply GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker <;> assumption)
