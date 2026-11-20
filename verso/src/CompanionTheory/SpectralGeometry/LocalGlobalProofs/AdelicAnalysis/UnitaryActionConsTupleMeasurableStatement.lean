import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionConsTupleMeasurable
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FUnitaryActionConsTupleMeasurable.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.unitary_action_cons_tuple_measurable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (g : HA R σ J), Measurable (fun X : Fin n → Fin M → R ⊗[F] E => actW R σ J g (consTup X)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Fact.measurable_actW_consTup | exact GlobalTheory.CompanionTheory.SW.Fact.measurable_actW_consTup | (intros; apply GlobalTheory.CompanionTheory.SW.Fact.measurable_actW_consTup <;> assumption)
