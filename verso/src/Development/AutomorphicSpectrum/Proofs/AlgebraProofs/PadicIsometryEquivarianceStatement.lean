import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicIsometryEquivariance
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ProIsoAt
open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.proIsoAt_of_padic_isometry` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FPadicIsometryEquivariance.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.padic_isometry_equivariance : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L') [Module.Projective O L] [Module.Finite ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L'] [Module.Free ℤ L'] (φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] L')), (∀ (a : O) (x : L), φ (1 ⊗ₜ (a • x)) = LinearMap.baseChange ℤ_[p] (LinearMap.lsmul O L' a).toAddMonoidHom.toIntLinearMap (φ (1 ⊗ₜ x))) → (∀ u v, B'.baseChange ℤ_[p] (φ u) (φ v) = B.baseChange ℤ_[p] u v) → Nonempty (ProIsoAt p O B B') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.proIsoAt_of_padic_isometry | exact GlobalTheory.CompanionTheory.Ar.proIsoAt_of_padic_isometry | (intros; apply GlobalTheory.CompanionTheory.Ar.proIsoAt_of_padic_isometry <;> assumption)
