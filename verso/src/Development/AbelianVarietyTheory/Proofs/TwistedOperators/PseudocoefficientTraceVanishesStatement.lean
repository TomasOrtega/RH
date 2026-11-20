import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PseudocoefficientTraceVanishes
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
Apply `GlobalTheory.IndTraceZero.hasTrace_indModule_eq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FPseudocoefficientTraceVanishes.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.pseudocoefficient_trace_vanishes : GlobalTheory.Published.HarishChandraCharacters → ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (δ : UJ ε →* (X →L[ℂ] X)) (f : UJ ε → ℂ), IsPseudoCoeff (ujMat ε) μ δ f → ∀ I : IndModule ε, I.a ≠ 0 → HasTrace (repOp I.rep μ f) 0 := by
  first | exact @GlobalTheory.IndTraceZero.hasTrace_indModule_eq_zero | exact GlobalTheory.IndTraceZero.hasTrace_indModule_eq_zero | (intros; apply GlobalTheory.IndTraceZero.hasTrace_indModule_eq_zero <;> assumption)
