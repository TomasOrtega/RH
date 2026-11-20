import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldAdicCompletionTensorOfInert
import Mathlib
open scoped TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InertField.isField_of_inert` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FIsFieldAdicCompletionTensorOfInert.lean&line=226#L226)
-/
theorem _root_.GlobalTheory.T.isField_adicCompletion_tensor_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ v : HeightOneSpectrum (𝓞 F), (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime → IsField (v.adicCompletion F ⊗[F] E) := by
  first | exact @GlobalTheory.InertField.isField_of_inert | exact GlobalTheory.InertField.isField_of_inert | (intros; apply GlobalTheory.InertField.isField_of_inert <;> assumption)
