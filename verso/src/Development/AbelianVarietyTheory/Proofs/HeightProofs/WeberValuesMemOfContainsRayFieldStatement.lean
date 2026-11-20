import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesMemOfContainsRayField
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FieldSize.WeberTransport.weberIn_of_containsRayField` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FWeberValuesMemOfContainsRayField.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.weberValues_mem_of_containsRayField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L) (ψ : L →+* ℂ), Module.finrank ℚ K = 2 → (∃ a : K, a ^ 2 = -(H.d : K)) → ∀ n : ℕ, 3 ≤ n → GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ n → GlobalTheory.FinalJoin.WeberIn H ψ.toRatAlgHom.fieldRange n ∧ H.rt0 ∈ ψ.toRatAlgHom.fieldRange := by
  first | exact @GlobalTheory.FieldSize.WeberTransport.weberIn_of_containsRayField | exact GlobalTheory.FieldSize.WeberTransport.weberIn_of_containsRayField | (intros; apply GlobalTheory.FieldSize.WeberTransport.weberIn_of_containsRayField <;> assumption)
