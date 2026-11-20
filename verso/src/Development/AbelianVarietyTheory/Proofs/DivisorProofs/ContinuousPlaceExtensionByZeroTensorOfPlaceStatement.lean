import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPlaceExtensionByZeroTensorOfPlace
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PlaneStrongApproxGeneratorImports
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureDivMem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContinuousPlaceExtensionByZeroTensorOfPlace.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.continuous_placeExtensionByZero_tensor_of_place : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E] [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalRing K] (P : GlobalTheory.CompanionTheory.SaGen.PlaceMap F K), Continuous (GlobalTheory.CompanionTheory.SaGen.iB (E := E) P) := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place | exact GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place | (intros; apply GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place <;> assumption)
