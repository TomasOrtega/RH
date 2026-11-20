import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorLiftKernelModPrime
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TensOne.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTensorLiftKernelModPrime.lean&line=183#L183)
-/
theorem _root_.GlobalTheory.T.tensor_lift_kernel_mod_prime : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (z : TensorProduct (Ainf l) (Acris l) A.W), Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr 1)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr 1)) (fun _ _ => Commute.all _ _) z = 0 → z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W)} := by
  first | exact @GlobalTheory.CompanionTheory.TensOne.main | exact GlobalTheory.CompanionTheory.TensOne.main | (intros; apply GlobalTheory.CompanionTheory.TensOne.main <;> assumption)
