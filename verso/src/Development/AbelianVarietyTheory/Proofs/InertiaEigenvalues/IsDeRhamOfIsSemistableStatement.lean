import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.sst_isDR` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsDeRhamOfIsSemistable.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.isDeRham_of_isSemistable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → IsDR (P.PD K) ρ := by
  first | exact @GlobalTheory.sst_isDR | exact GlobalTheory.sst_isDR | (intros; apply GlobalTheory.sst_isDR <;> assumption)
