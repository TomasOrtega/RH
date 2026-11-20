import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunctionFieldIntegralModelExistsIsHomOfMapLocalR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFunctionFieldIntegralModelExistsIsHomOfMapLocalR.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.functionFieldIntegralModel_exists_isHom_of_map_localRing : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (M' : RatModel o Ω') (φ : Ω →ₐ[o] Ω'), (∀ z' : M'.Z, ∃ z : M.Z, ∀ a ∈ M.O z, φ a ∈ M'.O z') → ∃ f : M'.Z ⟶ M.Z, M.IsHom M' φ f := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isHom_of_map_O | exact GlobalTheory.ZH.RatModel.exists_isHom_of_map_O | (intros; apply GlobalTheory.ZH.RatModel.exists_isHom_of_map_O <;> assumption)
