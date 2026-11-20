import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineInterFiniteBasicOpenCover
open AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.affine_inter_finite_basicOpen_cover` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAffineInterFiniteBasicOpenCover.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_finset_basicOpen_cover_inf_of_isAffineOpen : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (W V : X.Opens), IsAffineOpen W → IsAffineOpen V → ∃ s : Finset Γ(X, W), (∀ h ∈ s, ∃ r : Γ(X, V), X.basicOpen h = X.basicOpen r) ∧ ((W ⊓ V : X.Opens) : Set X) ⊆ ⋃ h ∈ s, (X.basicOpen h : Set X) := by
  first | exact @GlobalTheory.affine_inter_finite_basicOpen_cover | exact GlobalTheory.affine_inter_finite_basicOpen_cover | (intros; apply GlobalTheory.affine_inter_finite_basicOpen_cover <;> assumption)
