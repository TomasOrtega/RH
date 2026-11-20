import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalDstOfIsSst
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteDimensionalDstOfIsSst.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.finiteDimensional_Dst_of_isSst' : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → FiniteDimensional ℚ_[l] ↥(Dst P ρ) := by
  first | exact @GlobalTheory.Pst.finiteDimensional_Dst_of_isSst | exact GlobalTheory.Pst.finiteDimensional_Dst_of_isSst | (intros; apply GlobalTheory.Pst.finiteDimensional_Dst_of_isSst <;> assumption)
