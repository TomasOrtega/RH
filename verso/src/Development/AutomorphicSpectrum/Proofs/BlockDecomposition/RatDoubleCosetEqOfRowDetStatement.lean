import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatDoubleCosetEqOfRowDet
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GAMajInj.maj_inj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRatDoubleCosetEqOfRowDet.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.rat_double_coset_eq_of_row_det : ∀ q q' : Ad3.GA.NQ, (q.out : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (q'.out : Matrix (Fin 2) (Fin 2) ℚ) 1 0 → (q.out : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = (q'.out : Matrix (Fin 2) (Fin 2) ℚ) 1 1 → (q.out : Matrix (Fin 2) (Fin 2) ℚ).det = (q'.out : Matrix (Fin 2) (Fin 2) ℚ).det → q = q' := by
  first | exact @GlobalTheory.CompanionTheory.GAMajInj.maj_inj | exact GlobalTheory.CompanionTheory.GAMajInj.maj_inj | (intros; apply GlobalTheory.CompanionTheory.GAMajInj.maj_inj <;> assumption)
