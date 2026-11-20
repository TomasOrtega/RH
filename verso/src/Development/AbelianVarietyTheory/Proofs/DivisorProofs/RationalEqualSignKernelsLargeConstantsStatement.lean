import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalEqualSignKernelsLargeConstants
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KerConjMean.ratTopAt_big` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRationalEqualSignKernelsLargeConstants.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.rationalEqualSignKernels_largeConstants : BigC fun _ ch _ _ => RatTopAt ch := by
  first | exact @GlobalTheory.KerConjMean.ratTopAt_big | exact GlobalTheory.KerConjMean.ratTopAt_big | (intros; apply GlobalTheory.KerConjMean.ratTopAt_big <;> assumption)
