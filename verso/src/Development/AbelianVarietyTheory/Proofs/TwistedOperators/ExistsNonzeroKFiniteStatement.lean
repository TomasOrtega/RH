import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNonzeroKFinite
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactUnitaryFiniteInvariantSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalar
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KFinExists.exists_kfin` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsNonzeroKFinite.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.exists_nonzero_k_finite : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] [Nontrivial V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (UJset ε) π → ∃ v, IsKFin ε π v ∧ v ≠ 0 := by
  first | exact @GlobalTheory.KFinExists.exists_kfin | exact GlobalTheory.KFinExists.exists_kfin | (intros; apply GlobalTheory.KFinExists.exists_kfin <;> assumption)
