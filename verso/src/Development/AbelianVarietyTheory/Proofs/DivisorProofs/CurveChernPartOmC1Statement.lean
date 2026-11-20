import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveChernPartOmC1
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar BottChern ArRing ArChow HolAtlas Alt IsType IsReal dens chPart tdPart hermMat eval₂ bas relCot dRel IsRelAcyclic IsGenSmooth)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCurveChernPartOmC1.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.curve_chern_part_om_c1 : ∀ (B : BottChern) (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (h : IsRegVar p 1) (R : ArRing B h) (N : HermLB p) (σ : k →+* ℂ) (ε : ℤˣ), (h.atlas σ).part (h.coeFld (R.om (R.c1 N)) σ) ε = (N.φ σ).chernPart 1 ε := by
  first | exact @GlobalTheory.CurveChernPart.part_om_c1 | exact GlobalTheory.CurveChernPart.part_om_c1 | (intros; apply GlobalTheory.CurveChernPart.part_om_c1 <;> assumption)
