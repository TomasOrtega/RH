import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormConj
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0 dflat herm)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas IsType IsReal Alt delAt dbarAt)
open GlobalTheory.ConjChart (conjCoord conjPts conjChart)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlatFormConj.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.flat_form_conj : ∀ (D g : ℕ) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (P u u' : Pt (V D) g), om0 (fun v => -(τ (conjCoord D v)).map (starRingEnd ℂ)) (conjCoord D P.1, star P.2) ![(conjCoord D u.1, star u.2), (conjCoord D u'.1, star u'.2)] = -om0 τ P ![u, u'] := by
  first | exact @GlobalTheory.FlatFormConj.om0_conj | exact GlobalTheory.FlatFormConj.om0_conj | (intros; apply GlobalTheory.FlatFormConj.om0_conj <;> assumption)
