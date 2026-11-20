import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialNumeratorLinearExtension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
open GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPolynomialNumeratorLinearExtension.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.polynomial_numerator_linear_extension : ∀ {A ι : Type} (num : Multiset A → ℝ) (d : ℕ) (w : ι → A) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (c : ℝ), (∀ μ : Multiset ι, Multiset.card μ = d → num (μ.map w) = Ψ ((μ.map MvPolynomial.X).prod) / c) → ∀ P : MvPolynomial ι ℝ, P.IsHomogeneous d → numL num d (MvPolynomial.rename w P) = Ψ P / c := by
  first | exact @GlobalTheory.NumLRename.numL_rename_of_agree | exact GlobalTheory.NumLRename.numL_rename_of_agree | (intros; apply GlobalTheory.NumLRename.numL_rename_of_agree <;> assumption)
