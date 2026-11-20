import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerRightUnipotentFormula
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import GroundTheory.AutomorphicForms.MacdonaldWhittaker
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWeilWhittakerRightUnipotentFormula.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.weil_whittaker_right_unipotent_formula : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → ∀ (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) (Φ : E → ℂ) (x : F) (g : GL (Fin 2) F), GL2LocalData.Wc χ σ μ lam c Φ (g * uni2 x) = GL2LocalData.Wc χ σ μ lam c (fun z => (χ (x * Algebra.norm F z) : ℂ) * Φ z) g := by
  first | exact @GlobalTheory.CompanionTheory.WinertRn.main | exact GlobalTheory.CompanionTheory.WinertRn.main | (intros; apply GlobalTheory.CompanionTheory.WinertRn.main <;> assumption)
