import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotIsFieldAdicCompletionTensorOfSplit
import Mathlib
open scoped TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FNotIsFieldAdicCompletionTensorOfSplit.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.not_isField_adicCompletion_tensor_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ v : HeightOneSpectrum (𝓞 F), (v.asIdeal.primesOver (𝓞 E)).ncard = 2 → ¬ IsField (v.adicCompletion F ⊗[F] E) := by
  first | exact @GlobalTheory.SplitPlace.not_isField_of_split | exact GlobalTheory.SplitPlace.not_isField_of_split | (intros; apply GlobalTheory.SplitPlace.not_isField_of_split <;> assumption)
