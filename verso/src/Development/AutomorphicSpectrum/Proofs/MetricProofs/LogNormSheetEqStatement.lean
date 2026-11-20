import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormSheetEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PairingExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.BaseZ.logNorm_sheet` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FLogNormSheetEq.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.logNorm_sheet_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → ∀ (r : B.ι → X.functionFieldˣ) (hr : IsRatSec B r) (σ : k →+* ℂ) (y : CxPts p σ), y ∈ offSupp p σ (divOfRatSec ψ.isLB hr) → logNorm ψ r (sheet t τ y) = logNorm (φ σ) r y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.logNorm_sheet | exact GlobalTheory.CompanionTheory.Ar.BaseZ.logNorm_sheet | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.logNorm_sheet <;> assumption)
