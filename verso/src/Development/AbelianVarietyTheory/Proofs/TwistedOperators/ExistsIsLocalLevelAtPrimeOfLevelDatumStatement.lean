import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsLocalLevelAtPrimeOfLevelDatum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRedMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StepVec.exists_isLocLevel` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsIsLocalLevelAtPrimeOfLevelDatum.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.exists_isLocalLevelAtPrimeOfLevelDatum : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a : ℕ) (L : Formalism.L2.DIV.LevDat D.host.E ℂ a) (H : Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP))) (c : H →* ℂˣ),
    ∃ (J : Subgroup (GL (Fin a) (v.adicCompletionIntegers D.host.F))) (lam : J →* ℂˣ), IsLocLevel φ PP L H c J lam := by
  first | exact @GlobalTheory.StepVec.exists_isLocLevel | exact GlobalTheory.StepVec.exists_isLocLevel | (intros; apply GlobalTheory.StepVec.exists_isLocLevel <;> assumption)
