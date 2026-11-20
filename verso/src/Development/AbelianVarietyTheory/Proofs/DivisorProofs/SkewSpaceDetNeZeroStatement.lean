import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewSpaceDetNeZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombineApply
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSkewSpaceDetNeZero.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.skew_space_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (d r s : ℕ) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d), W.IsSkew σ B r s → W.J.det ≠ 0 := by
  first | exact @GlobalTheory.SkewGram.det_ne_zero_of_isSkew | exact GlobalTheory.SkewGram.det_ne_zero_of_isSkew | (intros; apply GlobalTheory.SkewGram.det_ne_zero_of_isSkew <;> assumption)
