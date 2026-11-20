import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsFiniteAdeleHaarNormalized
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FExistsFiniteAdeleHaarNormalized.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_finite_adele_haar_normalized : ∀ (F : Type) [Field F] [NumberField F], ∃ lf : Measure (Af F), lf.IsAddHaarMeasure ∧ lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 := by
  first | exact @GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one | exact GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one | (intros; apply GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one <;> assumption)
