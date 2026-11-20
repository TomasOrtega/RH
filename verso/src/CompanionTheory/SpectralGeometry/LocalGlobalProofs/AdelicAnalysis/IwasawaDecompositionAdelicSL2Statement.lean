import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IwasawaDecompositionAdelicSL2
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FIwasawaDecompositionAdelicSL2.lean&line=157#L157)
-/
theorem _root_.GlobalTheory.T.iwasawa_decomposition_adelic_SL2 : ∀ (F : Type) [Field F] [NumberField F], ∀ b : F, ∃ (y : A F) (a : (A F)ˣ) (k : SL(2, A F)), (∀ i j, k i j ∈ Oh F) ∧ wMat * nMat (algebraMap F (A F) b) = nMat y * mMat a * k ∧ (fun x => (a : A F) * x) '' Oh F = {x | x ∈ Oh F ∧ algebraMap F (A F) b * x ∈ Oh F} := by
  first | exact @GlobalTheory.CompanionTheory.SW.Iwasawa.iwasawa_w_n | exact GlobalTheory.CompanionTheory.SW.Iwasawa.iwasawa_w_n | (intros; apply GlobalTheory.CompanionTheory.SW.Iwasawa.iwasawa_w_n <;> assumption)
