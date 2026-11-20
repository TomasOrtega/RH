import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TrueGeo.InducedPull.induced_pull` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FInducedMetricPullback.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.induced_metric_pullback : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M N : TrueGeo.Model Y) (π : N.X ⟶ M.X) (hπ : π ≫ M.p = N.p), N.j ≫ π = M.j → ∀ (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → A.Induced N (L.pull π hπ) k cf := by
  first | exact @GlobalTheory.TrueGeo.InducedPull.induced_pull | exact GlobalTheory.TrueGeo.InducedPull.induced_pull | (intros; apply GlobalTheory.TrueGeo.InducedPull.induced_pull <;> assumption)
