import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFrameOfGridLatticeLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatPlace.Big₂` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FBesselFrameOfGridLatticeLargeDepth.lean&line=231#L231)
-/
theorem _root_.GlobalTheory.T.besselFrameOfGridLattice_largeDepth : Big fun ch => BesP ch := by
  first | exact @GlobalTheory.FlatPlace.Big₂ | exact GlobalTheory.FlatPlace.Big₂ | (intros; apply GlobalTheory.FlatPlace.Big₂ <;> assumption)
