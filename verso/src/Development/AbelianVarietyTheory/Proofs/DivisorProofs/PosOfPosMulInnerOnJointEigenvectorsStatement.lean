import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosOfPosMulInnerOnJointEigenvectors

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPosOfPosMulInnerOnJointEigenvectors.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.inner_pos_of_pos_on_joint_eigenvectors : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι → ∀ (W : Submodule ℂ V), FiniteDimensional ℂ W → ∀ (I : Type) (T : I → Module.End ℂ V), (∀ i, ∀ w ∈ W, T i w ∈ W) → (∀ i x y, inner ℂ (ι (T i x)) (ι y) = inner ℂ (ι x) (ι (T i y))) → (∀ i j, T i * T j = T j * T i) → ∀ (u : V →ₗ[ℂ] H), (∀ (m : I → ℝ), ∀ y ∈ W, (∀ i, T i y = (m i : ℂ) • y) → ∃ c : ℝ, 0 < c ∧ ∀ x ∈ W, inner ℂ (ι x) (u y) = (c : ℂ) * inner ℂ (ι x) (ι y)) → ∀ x ∈ W, x ≠ 0 → (inner ℂ (ι x) (u x)).im = 0 ∧ 0 < (inner ℂ (ι x) (u x)).re := by
  first | exact @GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors | exact GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors | (intros; apply GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors <;> assumption)
