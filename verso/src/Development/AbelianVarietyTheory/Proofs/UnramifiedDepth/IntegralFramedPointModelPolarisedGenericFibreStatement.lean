import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralFramedPointModelPolarisedGenericFibre
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AlphaPair.polAt_of_intData` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnramifiedDepth%2FIntegralFramedPointModelPolarisedGenericFibre.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.integralFramedPoint_model_polarised_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y), GlobalTheory.LN.PolAt I.G (Out.jK T.V) := by
  first | exact @GlobalTheory.AlphaPair.polAt_of_intData | exact GlobalTheory.AlphaPair.polAt_of_intData | (intros; apply GlobalTheory.AlphaPair.polAt_of_intData <;> assumption)
