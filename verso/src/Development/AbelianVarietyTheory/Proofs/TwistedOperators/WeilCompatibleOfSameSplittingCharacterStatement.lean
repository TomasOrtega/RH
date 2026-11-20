import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompatibleOfSameSplittingCharacter
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SameCharCompat.compatibleOfSameChar` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FWeilCompatibleOfSameSplittingCharacter.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.weilCompatible_of_sameSplittingCharacter : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.CompatibleOfSameChar D := by
  first | exact @GlobalTheory.SameCharCompat.compatibleOfSameChar | exact GlobalTheory.SameCharCompat.compatibleOfSameChar | (intros; apply GlobalTheory.SameCharCompat.compatibleOfSameChar <;> assumption)
