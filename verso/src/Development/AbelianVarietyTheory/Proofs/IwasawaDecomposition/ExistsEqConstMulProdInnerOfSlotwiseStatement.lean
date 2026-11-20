import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqConstMulProdInnerOfSlotwise
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_eq_const_mul_prod_inner_of_positionwise` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsEqConstMulProdInnerOfSlotwise.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_eq_const_mul_prod_inner_of_slotwise' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] (B : (∀ i, Hs i) → (∀ i, Hs i) → ℂ), (∀ i v v', ∃ c : ℂ, ∀ w w' : Hs i, B (Function.update v i w) (Function.update v' i w') = c * ⟪w, w'⟫_ℂ) → ∃ c : ℂ, ∀ v v', B v v' = c * ∏ i, ⟪v i, v' i⟫_ℂ := by
  first | exact @GlobalTheory.exists_eq_const_mul_prod_inner_of_positionwise | exact GlobalTheory.exists_eq_const_mul_prod_inner_of_positionwise | (intros; apply GlobalTheory.exists_eq_const_mul_prod_inner_of_positionwise <;> assumption)
