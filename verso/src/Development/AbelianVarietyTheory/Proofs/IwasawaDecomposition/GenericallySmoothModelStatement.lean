import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericallySmoothModel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ModelCharts.genSmooth_model` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FGenericallySmoothModel.lean&line=93#L93)
-/
theorem _root_.GlobalTheory.T.generically_smooth_model : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : Model Y), GenSmooth M.p Y.dim := by
  first | exact @GlobalTheory.ModelCharts.genSmooth_model | exact GlobalTheory.ModelCharts.genSmooth_model | (intros; apply GlobalTheory.ModelCharts.genSmooth_model <;> assumption)
