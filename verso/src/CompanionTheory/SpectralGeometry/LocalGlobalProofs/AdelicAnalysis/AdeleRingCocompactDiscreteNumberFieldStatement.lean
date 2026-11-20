import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdeleRingCocompactDiscreteNumberField
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Adelic.FieldCocompact.discrete_cocompact` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FAdeleRingCocompactDiscreteNumberField.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.adele_ring_cocompact_discrete_number_field : ∀ (F : Type) [Field F] [NumberField F], (∃ C : Set (AdeleRing (𝓞 F) F), IsCompact C ∧ ∀ y, ∃ l : F, y - algebraMap F (AdeleRing (𝓞 F) F) l ∈ C) ∧ (∀ C : Set (AdeleRing (𝓞 F) F), IsCompact C → {l : F | algebraMap F (AdeleRing (𝓞 F) F) l ∈ C}.Finite) ∧ NoncompactSpace (AdeleRing (𝓞 F) F) := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.FieldCocompact.discrete_cocompact | exact GlobalTheory.CompanionTheory.Adelic.FieldCocompact.discrete_cocompact | (intros; apply GlobalTheory.CompanionTheory.Adelic.FieldCocompact.discrete_cocompact <;> assumption)
