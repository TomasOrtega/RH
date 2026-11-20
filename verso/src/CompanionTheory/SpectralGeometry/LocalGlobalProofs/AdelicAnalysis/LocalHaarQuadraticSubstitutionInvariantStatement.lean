import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalHaarQuadraticSubstitutionInvariant
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.QuadIso.measure_quad_Fv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FLocalHaarQuadraticSubstitutionInvariant.lean&line=226#L226)
-/
theorem _root_.GlobalTheory.T.local_haar_quadratic_substitution_invariant : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → Valued.v (2 : Fv F v) = 1 → ∀ a c : Fv F v, Valued.v a = 1 → c ∈ v.adicCompletionIntegers F → ∀ A : Set (Fv F v), MeasurableSet A → lam {t | Valued.v t < 1 ∧ a * t + c * t ^ 2 ∈ A} = lam (A ∩ {s | Valued.v s < 1}) := by
  first | exact @GlobalTheory.CompanionTheory.SW.QuadIso.measure_quad_Fv | exact GlobalTheory.CompanionTheory.SW.QuadIso.measure_quad_Fv | (intros; apply GlobalTheory.CompanionTheory.SW.QuadIso.measure_quad_Fv <;> assumption)
