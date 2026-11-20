import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FInfiniteAdelesLocalRingTotallyReal.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.infinite_adeles_local_ring_totally_real : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → IsLocR (Ainf F) := by
  first | exact @GlobalTheory.CompanionTheory.SW.isLocR_Ainf | exact GlobalTheory.CompanionTheory.SW.isLocR_Ainf | (intros; apply GlobalTheory.CompanionTheory.SW.isLocR_Ainf <;> assumption)
