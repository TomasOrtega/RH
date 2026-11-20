import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumDatumTrivialCombinationLargeDepth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.VacComb.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FVacuumDatumTrivialCombinationLargeDepth.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.vacuumDatum_trivialCombination_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (j : Fin D.R.m), IsCombOf ch.W (FinDatum.vacuum ch.G t (.top t j)) (Finsupp.single 0 1) := by
  first | exact @GlobalTheory.VacComb.main | exact GlobalTheory.VacComb.main | (intros; apply GlobalTheory.VacComb.main <;> assumption)
