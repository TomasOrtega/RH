import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedOneSubIndexMemDegreeOneCharacterDiff
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndApplyOne
open GlobalTheory.BI GlobalTheory.BrauerZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BrauerZero.ind_one_sub_index_mem_D0` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FInducedOneSubIndexMemDegreeOneCharacterDiff.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.induced_one_sub_index_mem_degreeOneCharacterDiff : ∀ {G : Type} [Group G] [Finite G] (K : Subgroup G), (∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ K) → ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) ∈ D0 G := by
  first | exact @GlobalTheory.BrauerZero.ind_one_sub_index_mem_D0 | exact GlobalTheory.BrauerZero.ind_one_sub_index_mem_D0 | (intros; apply GlobalTheory.BrauerZero.ind_one_sub_index_mem_D0 <;> assumption)
