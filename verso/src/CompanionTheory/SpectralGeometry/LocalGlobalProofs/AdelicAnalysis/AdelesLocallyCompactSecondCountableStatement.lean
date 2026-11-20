import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FAdelesLocallyCompactSecondCountable.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.adeles_locally_compact_second_countable : ∀ (F : Type) [Field F] [NumberField F], (LocallyCompactSpace (AF F) ∧ SecondCountableTopology (AF F) ∧ T2Space (AF F)) ∧ (LocallyCompactSpace (Af F) ∧ SecondCountableTopology (Af F) ∧ T2Space (Af F)) := by
  first | exact @GlobalTheory.CompanionTheory.AdeleTop.adele_top | exact GlobalTheory.CompanionTheory.AdeleTop.adele_top | (intros; apply GlobalTheory.CompanionTheory.AdeleTop.adele_top <;> assumption)
