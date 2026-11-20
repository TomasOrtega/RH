import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralValuesAlgebraicPointsIffValueNonneg
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.NX (ExpSet CoefLat)
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.Tow
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIntegralValuesAlgebraicPointsIffValueNonneg.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.integral_values_algebraic_points_iff_value_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (la : HeightOneSpectrum (𝓞 c.F)) (f : Rul Xo c), GlobalTheory.GoodPts.BddAll Xo c la 1 f ↔ ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f := by
  first | exact @GlobalTheory.TowVal.bddAll_one_iff_valSet_nonneg | exact GlobalTheory.TowVal.bddAll_one_iff_valSet_nonneg | (intros; apply GlobalTheory.TowVal.bddAll_one_iff_valSet_nonneg <;> assumption)
