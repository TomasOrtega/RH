import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsReducedOfLieReg
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsReducedOfLieReg.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.isReduced_of_lieReg' : ∀ (K : UQ) (B : InvAlg K), B.LieReg → IsReduced B.A := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg | exact GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg | (intros; apply GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg <;> assumption)
