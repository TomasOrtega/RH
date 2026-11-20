import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfComponentZeroUnderPrime
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Col
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.VanishAwayInt.intAtA_of_prV_eq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FIntegralAtOfComponentZeroUnderPrime.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.integralAt_of_component_zero_under_prime : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (P : HeightOneSpectrum (𝓞 E)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F), (∀ v : HeightOneSpectrum (𝓞 F), IsOver v P → prV (E := E) v z = 0) → IntAtA (F := F) P z := by
  first | exact @GlobalTheory.VanishAwayInt.intAtA_of_prV_eq_zero | exact GlobalTheory.VanishAwayInt.intAtA_of_prV_eq_zero | (intros; apply GlobalTheory.VanishAwayInt.intAtA_of_prV_eq_zero <;> assumption)
