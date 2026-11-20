import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsLiftModel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.model_cxPts_from_generic_fibre` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FComplexPointsLiftModel.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.complex_points_lift_model : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (τ : 𝓞 F →+* ℂ) (y' : CxPts M.p τ), ∃ σ : F →+* ℂ, σ.comp (algebraMap (𝓞 F) F) = τ ∧ ∃ y : Pts Y σ, y'.1 = y.1 ≫ M.j := by
  first | exact @GlobalTheory.model_cxPts_from_generic_fibre | exact GlobalTheory.model_cxPts_from_generic_fibre | (intros; apply GlobalTheory.model_cxPts_from_generic_fibre <;> assumption)
