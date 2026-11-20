import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StageParameterPairingShift
import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrOfNotMem
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FStageParameterPairingShift.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.stage_parameter_pairing_shift : ∀ {a b : ℕ} (n : ℕ) (j : Fin a → ℕ) (β : Fin b → Fin a) (s : Fin a → ℂ) (y : Fin b → ℝ), (∀ i, 1 ≤ j i) → (∀ i, #{l | β l = i} = j i) → (∀ i, ∑ l with β l = i, rho n (fun _ => 1) l = (j i : ℂ) * rho n j i) → (∀ x : Fin a → ℝ, pairing (fun _ => 1) (stageS j β s y + rho n fun _ => 1) (x ∘ β) = pairing j (s + rho n j) x) ∧ ∀ x : Fin b → ℝ, (∀ i, ∑ l with β l = i, x l = 0) → pairing (fun _ => 1) (stageS j β s y) x = pairing (fun _ => 1) (fun l => Complex.I * y l) x := by
  first | exact @GlobalTheory.RealInd.Stages.stageS_pairings | exact GlobalTheory.RealInd.Stages.stageS_pairings | (intros; apply GlobalTheory.RealInd.Stages.stageS_pairings <;> assumption)
