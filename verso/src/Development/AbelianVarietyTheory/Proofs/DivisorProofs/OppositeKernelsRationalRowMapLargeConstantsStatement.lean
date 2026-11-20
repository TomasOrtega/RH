import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OppositeKernelsRationalRowMapLargeConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NrmOneNonneg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FOppositeKernelsRationalRowMapLargeConstants.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.oppositeKernelsRationalRowMap_largeConstants : BigC fun _ ch _ _ => RatRowAt ch := by
  first | exact @GlobalTheory.KerConjMean.ratRowAt_big | exact GlobalTheory.KerConjMean.ratRowAt_big | (intros; apply GlobalTheory.KerConjMean.ratRowAt_big <;> assumption)
