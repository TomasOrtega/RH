import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivLOneBoundFamilyStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
namespace GlobalTheory
/- English proof (translation)
Introduce `_`. Use `⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩` and prove the remaining obligations. Conclude with `⟨0, fun x hx _ i _ _ => (Fm.params x hx i).logDerivative_le_power⟩`.
-/
theorem logDeriv_LFunction_at_one_le_along_family_alt :
    _root_.GlobalTheory.FunPr.ThetaLocalInputs → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ =>
      |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) := by
  intro _
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  exact ⟨0, fun x hx _ i _ _ => (Fm.params x hx i).logDerivative_le_power⟩
end GlobalTheory
end
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.logDeriv_LFunction_at_one_le_along_family_alt | exact _root_.GlobalTheory.logDeriv_LFunction_at_one_le_along_family_alt | (intros; apply _root_.GlobalTheory.logDeriv_LFunction_at_one_le_along_family_alt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.abs_logDerivativeAtOne_le_x_rpow_eps : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) := by
  first | exact @_root_.GlobalTheory.logDeriv_LFunction_at_one_le_along_family_alt | exact _root_.GlobalTheory.logDeriv_LFunction_at_one_le_along_family_alt | (intros; apply _root_.GlobalTheory.logDeriv_LFunction_at_one_le_along_family_alt <;> assumption)
end
end
