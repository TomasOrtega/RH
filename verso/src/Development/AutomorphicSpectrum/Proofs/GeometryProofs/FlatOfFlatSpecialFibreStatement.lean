import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatOfFlatSpecialFibre
import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModuleFlatOfFlatAndFibreFlatStatement
open TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FFlatOfFlatSpecialFibre.lean&line=145#L145)
-/
theorem _root_.GlobalTheory.T.flat_of_flat_special_fibre : ∀ (R P Q : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q] [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q] (φ : P →ₐ[R] Q), (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom.Flat → φ.toRingHom.Flat := by
  first | exact @GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat | exact GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat | (intros; apply GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat <;> assumption)
