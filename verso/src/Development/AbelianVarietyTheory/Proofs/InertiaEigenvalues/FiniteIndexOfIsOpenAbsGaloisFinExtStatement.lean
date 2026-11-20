import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIndexOfIsOpenAbsGaloisFinExt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OpenFiniteIndex.finiteIndex_of_isOpen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteIndexOfIsOpenAbsGaloisFinExt.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.finiteIndex_of_isOpen_absGalois_finExt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (H : Subgroup ↥(GK K)), IsOpen (H : Set ↥(GK K)) → H.FiniteIndex := by
  first | exact @GlobalTheory.OpenFiniteIndex.finiteIndex_of_isOpen | exact GlobalTheory.OpenFiniteIndex.finiteIndex_of_isOpen | (intros; apply GlobalTheory.OpenFiniteIndex.finiteIndex_of_isOpen <;> assumption)
