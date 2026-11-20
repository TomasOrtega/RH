import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelTransformSymplecticImaginary
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Cusp.Univ.im_tz_form'` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FSiegelTransformSymplecticImaginary.lean&line=90#L90)
-/
theorem _root_.GlobalTheory.T.siegel_transform_symplectic_imaginary : ∀ {I : Type} [Fintype I] [DecidableEq I] (Z : Matrix I I ℂ), Zᵀ = Z → (1 - Zᴴ * Z).PosDef → ∀ z w : I → ℂ, (tz Z z ⬝ᵥ (1 - Zᴴ * Z)⁻¹ *ᵥ star (tz Z w)).im = (z ⬝ᵥ star w).im := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.im_tz_form' | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.im_tz_form' | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.im_tz_form' <;> assumption)
