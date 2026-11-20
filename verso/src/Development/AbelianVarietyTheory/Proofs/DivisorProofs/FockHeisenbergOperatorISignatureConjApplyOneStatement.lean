import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorISignatureConjApplyOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFockHeisenbergOperatorISignatureConjApplyOne.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.fockHeisenbergOperator_I_signatureConj_apply_one : ∀ {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ), heisOp (Complex.I • (Jm P Q * c * Jm R S)) 1 = Complex.I • heisOp c 1 := by
  first | exact @GlobalTheory.RealLift.heisOp_twist_one | exact GlobalTheory.RealLift.heisOp_twist_one | (intros; apply GlobalTheory.RealLift.heisOp_twist_one <;> assumption)
