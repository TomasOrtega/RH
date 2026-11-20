import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorLiftSurjectiveKernelLevel
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PerfFil.tens_base_change` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTensorLiftSurjectiveKernelLevel.lean&line=115#L115)
-/
theorem _root_.GlobalTheory.T.tensor_lift_surjective_kernel_level : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), Function.Surjective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr n)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr n)) (fun _ _ => Commute.all _ _)) ∧ ∀ z : TensorProduct (Ainf l) (Acris l) A.W, Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr n)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr n)) (fun _ _ => Commute.all _ _) z = 0 ↔ z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W) ^ n} := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.tens_base_change | exact GlobalTheory.CompanionTheory.PerfFil.tens_base_change | (intros; apply GlobalTheory.CompanionTheory.PerfFil.tens_base_change <;> assumption)
