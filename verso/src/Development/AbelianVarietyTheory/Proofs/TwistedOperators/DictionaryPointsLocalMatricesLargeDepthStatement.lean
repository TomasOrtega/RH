import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DictionaryPointsLocalMatricesLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatPlaceLoc.localization₂` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FDictionaryPointsLocalMatricesLargeDepth.lean&line=121#L121)
-/
theorem _root_.GlobalTheory.T.dictionaryPoints_localMatrices_largeDepth : Big fun ch => LocP ch := by
  first | exact @GlobalTheory.FlatPlaceLoc.localization₂ | exact GlobalTheory.FlatPlaceLoc.localization₂ | (intros; apply GlobalTheory.FlatPlaceLoc.localization₂ <;> assumption)
