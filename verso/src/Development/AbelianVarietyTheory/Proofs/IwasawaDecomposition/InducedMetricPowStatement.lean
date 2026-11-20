import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TrueGeo.InducedPow.induced_pow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FInducedMetricPow.lean&line=90#L90)
-/
theorem _root_.GlobalTheory.T.induced_metric_pow : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k m : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → A.Induced M (L.pow m) (k * m) cf := by
  first | exact @GlobalTheory.TrueGeo.InducedPow.induced_pow | exact GlobalTheory.TrueGeo.InducedPow.induced_pow | (intros; apply GlobalTheory.TrueGeo.InducedPow.induced_pow <;> assumption)
