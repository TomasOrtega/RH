import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne
import Development.WeilBound.CoreStatements.HodgeTatePoints.QacInt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FHodgeTatePoints%2FQacInt.lean&line=151#L151)
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.key_over_lie_basis_degree : KeyBadSt → ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.UnitSp κ → GlobalTheory.KeyCl.ThetaOne κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp (𝓞 L))) (th : t.PP.L.Sec) (x : KeyIn L) (v : Fin x.P.g → (epsR (𝓞 L) ⟶ t.G)), KeyOver (algebraMap (𝓞 L) L) t th x v → IsLieBasis v → KeyDeg.NonVan t.G.hom th → IsIntegral ℤ (κ L x : L) := by
  first | exact @PositivityTheory.HtPt.Qac.keydeg_integral | exact PositivityTheory.HtPt.Qac.keydeg_integral
