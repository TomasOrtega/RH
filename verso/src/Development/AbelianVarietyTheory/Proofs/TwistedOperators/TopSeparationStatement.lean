import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopSeparation
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SepRows.SepProof.topSep_of_classicalTheorems` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FTopSeparation.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.top_separation : GlobalTheory.FunPr.Hypotheses₂ → TopSep := by
  first | exact @GlobalTheory.SepRows.SepProof.topSep_of_classicalTheorems | exact GlobalTheory.SepRows.SepProof.topSep_of_classicalTheorems | (intros; apply GlobalTheory.SepRows.SepProof.topSep_of_classicalTheorems <;> assumption)
