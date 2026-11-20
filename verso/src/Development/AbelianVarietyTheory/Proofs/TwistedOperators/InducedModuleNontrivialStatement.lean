import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedModuleNontrivial
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FInducedModuleNontrivial.lean&line=115#L115)
-/
theorem _root_.GlobalTheory.T.induced_module_nontrivial : ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε), Nontrivial I.H := by
  first | exact @GlobalTheory.IndNonzero.indModule_nontrivial | exact GlobalTheory.IndNonzero.indModule_nontrivial | (intros; apply GlobalTheory.IndNonzero.indModule_nontrivial <;> assumption)
