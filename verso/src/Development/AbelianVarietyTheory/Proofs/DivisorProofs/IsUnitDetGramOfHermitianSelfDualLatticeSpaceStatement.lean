import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isUnit_det_of_isHerm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsUnitDetGramOfHermitianSelfDualLatticeSpace.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.isUnit_det_gram_of_hermitianSelfDualLatticeSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (X : Spc F E n) (r s : ℕ), X.IsHerm σ B r s → IsUnit X.J.det := by
  first | exact @GlobalTheory.isUnit_det_of_isHerm | exact GlobalTheory.isUnit_det_of_isHerm | (intros; apply GlobalTheory.isUnit_det_of_isHerm <;> assumption)
