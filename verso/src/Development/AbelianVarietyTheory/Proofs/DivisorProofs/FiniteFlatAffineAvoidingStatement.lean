import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatAffineAvoiding
import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_basicOpen_free_avoiding_finite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteFlatAffineAvoiding.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.finite_flat_affine_avoiding : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (n : ℕ) (V : X.Opens), IsAffineOpen V → IsAffineOpen (f ⁻¹ᵁ V) → (letI := (f.app V).hom.toAlgebra; Module.Free Γ(X, V) Γ(Y, f ⁻¹ᵁ V) ∧ Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V) ∧ Module.finrank Γ(X, V) Γ(Y, f ⁻¹ᵁ V) = n) → ∀ (x : X), x ∈ V → ∀ (T : Set X), T.Finite → (∀ y ∈ T, IsClosed ({y} : Set X)) → x ∉ T → ∃ W : X.Opens, x ∈ W ∧ W ≤ V ∧ (∀ y ∈ T, y ∉ W) ∧ IsAffineOpen W ∧ IsAffineOpen (f ⁻¹ᵁ W) ∧ (letI := (f.app W).hom.toAlgebra; Module.Free Γ(X, W) Γ(Y, f ⁻¹ᵁ W) ∧ Module.Finite Γ(X, W) Γ(Y, f ⁻¹ᵁ W) ∧ Module.finrank Γ(X, W) Γ(Y, f ⁻¹ᵁ W) = n) := by
  first | exact @GlobalTheory.exists_basicOpen_free_avoiding_finite | exact GlobalTheory.exists_basicOpen_free_avoiding_finite | (intros; apply GlobalTheory.exists_basicOpen_free_avoiding_finite <;> assumption)
