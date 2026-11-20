import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleTensorLocalizationAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.preirreducibleSpace_primeSpectrum_tensor_localizationAway` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPreirreducibleTensorLocalizationAway.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.preirreducible_tensor_localization_away : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (b : B) (k : Type) [Field k] [Algebra A k], PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) → PreirreducibleSpace (PrimeSpectrum (k ⊗[A] Localization.Away b)) := by
  first | exact @GlobalTheory.preirreducibleSpace_primeSpectrum_tensor_localizationAway | exact GlobalTheory.preirreducibleSpace_primeSpectrum_tensor_localizationAway | (intros; apply GlobalTheory.preirreducibleSpace_primeSpectrum_tensor_localizationAway <;> assumption)
