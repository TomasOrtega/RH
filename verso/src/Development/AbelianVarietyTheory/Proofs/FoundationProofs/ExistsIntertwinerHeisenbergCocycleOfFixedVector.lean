import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearIndependentOfJointEigenvectors

noncomputable section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors`. Consider the case `exact _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors`. Consider the case `(apply _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors ..)`.
-/
theorem linearIndependent_of_simultaneous_eigen {ι α M : Type} [AddCommGroup M] [Module ℂ M] (f : ι → M) (χ : ι → α → ℂ)
    (op : α → M →ₗ[ℂ] M) (hχ : Function.Injective χ) (hop : ∀ a i, op a (f i) = χ i a • f i) (hf : ∀ i, f i ≠ 0) :
    LinearIndependent ℂ f := by
  first
  | exact @_root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors
  | exact _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors
  | (apply _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors <;> assumption)
  | (intros; apply _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors <;> assumption)
  | (intros; apply @_root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors ..)

end GlobalTheory.FinWeil
