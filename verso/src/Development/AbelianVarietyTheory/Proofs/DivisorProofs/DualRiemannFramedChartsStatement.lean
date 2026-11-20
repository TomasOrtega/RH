import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRiemannFramedCharts
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DoublingFrame.framedCharts_of_double` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDualRiemannFramedCharts.lean&line=406#L406)
-/
theorem _root_.GlobalTheory.T.dual_riemann_framed_charts : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (P : PPAS S) (h : VMetric p (omega P.A) P.g), P.IsDualRiemann (1 / 2) h → ∀ L : HermLB (P.A.hom ≫ p), ∀ (w : LB.Iso (L.pull (dbl P) (dbl_comp P p)).B (L.pow 4).B), w.IsGen → FramedCharts P h L := by
  first | exact @GlobalTheory.DoublingFrame.framedCharts_of_double | exact GlobalTheory.DoublingFrame.framedCharts_of_double | (intros; apply GlobalTheory.DoublingFrame.framedCharts_of_double <;> assumption)
