import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryFactorEquivalence
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FUnitaryFactorEquivalence.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.unitary_factor_equivalence : GlobalTheory.Published.HarishChandraAnalyticity → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsIrrAdm ε ρ → IsURepOn (UJset ε) ρ → IsIrrAdm ε π → IsURepOn (UJset ε) π → ∀ Z, IsFactor ε ρ Z (kFinVec ε ρ) π → UEquiv ε π ρ := by
  first | exact @GlobalTheory.UnitaryFromModules.uEquiv_of_isFactor | exact GlobalTheory.UnitaryFromModules.uEquiv_of_isFactor | (intros; apply GlobalTheory.UnitaryFromModules.uEquiv_of_isFactor <;> assumption)
