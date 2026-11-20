import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorNoetherianAffineOpen
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GE.krull_noeth_chart` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTensorNoetherianAffineOpen.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.tensor_noetherian_affine_open : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens), IsAffineOpen V → ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V, letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [Algebra Γ(X, V) R], IsNoetherianRing (R ⊗[Γ(X, V)] Γ(Z, U)) := by
  first | exact @GlobalTheory.CompanionTheory.GE.krull_noeth_chart | exact GlobalTheory.CompanionTheory.GE.krull_noeth_chart | (intros; apply GlobalTheory.CompanionTheory.GE.krull_noeth_chart <;> assumption)
