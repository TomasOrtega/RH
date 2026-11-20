import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilRepresentationQuadraticDatum
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FWeilRepresentationQuadraticDatum.lean&line=295#L295)
-/
theorem _root_.GlobalTheory.T.weil_representation_quadratic_datum : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F), B.IsSymm → B.det ≠ 0 → NAQuad ψ (hf F) (Bf B) (muF B lf) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.SelfDual.naQuad | exact GlobalTheory.CompanionTheory.SW.Core.SelfDual.naQuad | (intros; apply GlobalTheory.CompanionTheory.SW.Core.SelfDual.naQuad <;> assumption)
