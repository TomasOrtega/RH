import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlacesMatchCmTypeFrobeniusOfParameters
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GoodDepth.placeTie_of_pins` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FRealPlacesMatchCmTypeFrobeniusOfParameters.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.realPlaces_match_cmTypeFrobenius : ∀ (D : D7) (L : SizeData₂ D) (T : Core D), T.Q.Pins → PlaceTie (numOf D L) T.Q.c (fun z => DV.tauEmb D (plOf D z)) := by
  first | exact @GlobalTheory.GoodDepth.placeTie_of_pins | exact GlobalTheory.GoodDepth.placeTie_of_pins | (intros; apply GlobalTheory.GoodDepth.placeTie_of_pins <;> assumption)
