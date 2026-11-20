import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedClassFunctionFromSubgroupTrans
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndApplyOne
open GlobalTheory.BI GlobalTheory.BrauerZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BrauerZero.ind_ind_of_le` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FInducedClassFunctionFromSubgroupTrans.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.inducedClassFunctionFromSubgroup_trans : ∀ {G : Type} [Group G] [Finite G] (K A : Subgroup G), K ≤ A → ∀ (ψ : K → ℂ), ind A (ind (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩)) = ind K ψ := by
  first | exact @GlobalTheory.BrauerZero.ind_ind_of_le | exact GlobalTheory.BrauerZero.ind_ind_of_le | (intros; apply GlobalTheory.BrauerZero.ind_ind_of_le <;> assumption)
