import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSumWordCombinationCoefficientsLe
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ArchRec.IoPhase.ioUniq_of_discreteSeriesCover` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FNormSumWordCombinationCoefficientsLe.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.lowestKTypeFockMap_unique_of_discreteSeries : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, IoUniq D := by
  first | exact @GlobalTheory.ArchRec.IoPhase.ioUniq_of_discreteSeriesCover | exact GlobalTheory.ArchRec.IoPhase.ioUniq_of_discreteSeriesCover | (intros; apply GlobalTheory.ArchRec.IoPhase.ioUniq_of_discreteSeriesCover <;> assumption)
