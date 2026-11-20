import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueIdempotentLiftTilt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Untilt.existsUnique_idempotent_sharp` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsUniqueIdempotentLiftTilt.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.existsUnique_idempotent_lift_tilt : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (e : A.U), IsIdempotentElem e → ∃! e₀ : A.A, IsIdempotentElem e₀ ∧ A.sharp e₀ = e := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.existsUnique_idempotent_sharp | exact GlobalTheory.CompanionTheory.Untilt.existsUnique_idempotent_sharp | (intros; apply GlobalTheory.CompanionTheory.Untilt.existsUnique_idempotent_sharp <;> assumption)
