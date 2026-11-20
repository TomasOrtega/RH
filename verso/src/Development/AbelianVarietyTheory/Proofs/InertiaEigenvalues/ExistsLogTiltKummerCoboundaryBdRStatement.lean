import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogTiltKummerCoboundaryBdR
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.exists_log_tilt_BdR` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsLogTiltKummerCoboundaryBdR.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.exists_log_tilt_kummerCoboundary_BdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), ∃ u : P.R.BdR, ∀ g : GQ l, P.actQdR g u = u + P.ιB ((kummer P g : ℚ_[l]) • P.tB) := by
  first | exact @GlobalTheory.PMon.exists_log_tilt_BdR | exact GlobalTheory.PMon.exists_log_tilt_BdR | (intros; apply GlobalTheory.PMon.exists_log_tilt_BdR <;> assumption)
