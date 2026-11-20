import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockConjugatesSpanDepthData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConjDataTotal.fockTot` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFockConjugatesSpanDepthData.lean&line=190#L190)
-/
theorem _root_.GlobalTheory.T.fockConjugates_span_depth_data : FockTot := by
  first | exact @GlobalTheory.ConjDataTotal.fockTot | exact GlobalTheory.ConjDataTotal.fockTot | (intros; apply GlobalTheory.ConjDataTotal.fockTot <;> assumption)
