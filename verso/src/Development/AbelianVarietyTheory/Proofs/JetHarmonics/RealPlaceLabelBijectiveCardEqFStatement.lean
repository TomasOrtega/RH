import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceLabelBijectiveCardEqF
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RunDepth.plOf_bijective_card` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FRealPlaceLabelBijectiveCardEqF.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.realPlaceLabel_bijective_card_eq_f : ∀ (D : D7), Function.Bijective (plOf D) ∧ Fintype.card D.what₂.Tau = D.R.f := by
  first | exact @GlobalTheory.RunDepth.plOf_bijective_card | exact GlobalTheory.RunDepth.plOf_bijective_card | (intros; apply GlobalTheory.RunDepth.plOf_bijective_card <;> assumption)
