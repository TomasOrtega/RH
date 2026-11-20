import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralClopenDecompositionOfSmooth
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

/- English proof (citation)
Apply `GlobalTheory.SmoothComponents.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsIntegralClopenDecompositionOfSmooth.lean&line=45#L45)
-/
theorem UpperTheory.Cb.exists_integral_clopen_decomposition_of_smooth :
    ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s] [CompactSpace Z], ∃ (J : Type) (_ : Fintype J) (V : J → Z.Opens), (∀ i j, i ≠ j → V i ⊓ V j = ⊥) ∧ iSup V = ⊤ ∧ ∀ j, IsIntegral (V j).toScheme := by
  first | exact @GlobalTheory.SmoothComponents.main | exact GlobalTheory.SmoothComponents.main
