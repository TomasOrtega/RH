import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusTensorCrisToSemistableComm
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.phiV_crisIncl_comm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFrobeniusTensorCrisToSemistableComm.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.frobeniusTensor_crisToSemistable_comm : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (w : V ⊗[ℚ_[l]] P.R.B), phiV P ℚ_[l] V (crisIncl P ℚ_[l] V w) = crisIncl P ℚ_[l] V (φVB (P.PD K) (LL := ℚ_[l]) (V := V) w) := by
  first | exact @GlobalTheory.PMon.phiV_crisIncl_comm | exact GlobalTheory.PMon.phiV_crisIncl_comm | (intros; apply GlobalTheory.PMon.phiV_crisIncl_comm <;> assumption)
