import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ClosedRankTiesFC2S
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.Ext.Lw
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.Forms Formalism.BasicNotions
open scoped TensorProduct
/- English proof (translation)
Take `⟨x0, h⟩` from `h`. Use `rank_conditions_of_lowest_space Fm ⟨max x0 (Fm.x1 + 1), fun x hx i u => ?_⟩` and prove the remaining obligations. Establish `e1 : Fm.x1 < x`. Use `(le_max_right x0 (Fm.x1 + 1)).trans hx` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨T⟩` from `h x e1 ((le_max_left _ _).trans hx) i`. Conclude with `mu0Tie_of_sym T.cols u`.
-/
theorem rankTiesF_of_C2S_alt {eps : ℝ} (Fm : FamP eps) (h : _root_.Formalism.L2.SecondChernLinkedClass Fm) : RankTiesF Fm := by
  obtain ⟨x0, h⟩ := h
  refine rank_conditions_of_lowest_space Fm ⟨max x0 (Fm.x1 + 1), fun x hx i u => ?_⟩
  have e1 : Fm.x1 < x := by
    have := (le_max_right x0 (Fm.x1 + 1)).trans hx
    linarith
  obtain ⟨T⟩ := h x e1 ((le_max_left _ _).trans hx) i
  exact mu0Tie_of_sym T.cols u
/- English proof (translation)
Assemble the required witnesses or components as `⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ hC _ => _root_.Formalism.MainNotions.Ext.Lw.rankTiesF_of_C2S_alt Fm hC⟩⟩`.
-/
theorem second_chern_linked_closed_rank_ties : Closed _root_.Formalism.L2.SecondChernLinkedClass fun Fm _ => RankTiesF Fm :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ hC _ => _root_.Formalism.MainNotions.Ext.Lw.rankTiesF_of_C2S_alt Fm hC⟩⟩
end Formalism.MainNotions.Ext.Lw
end
end
