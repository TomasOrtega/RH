import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsMinNormTensorOfIsClosedTensorSLOrbit
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FExistsMinNormTensorOfIsClosedTensorSLOrbit.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.exists_minNormTensor_of_isClosed_tensorSLOrbit : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (v : TIdx ι d → ℂ), IsClosed (orb d v) → ∃ w ∈ orb d v, IsMinVec d w := by
  first | exact @GlobalTheory.ClassFin.MinVec.exists_isMinVec_of_isClosed | exact GlobalTheory.ClassFin.MinVec.exists_isMinVec_of_isClosed | (intros; apply GlobalTheory.ClassFin.MinVec.exists_isMinVec_of_isClosed <;> assumption)
