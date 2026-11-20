import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceBasisExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumEmbeddingDualInt
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.HT.LatMult.nonempty_basis_eigenHom` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FEigenspaceBasisExists.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.eigenspace_basis_exists : ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Module (𝓞 E) X] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (τ : 𝓞 E →+* k), Nonempty (Module.Basis (Fin (Module.finrank ℤ X / Module.finrank ℚ E)) k (GlobalTheory.Diag.eigenHom X τ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.LatMult.nonempty_basis_eigenHom | exact GlobalTheory.CompanionTheory.Ar.HT.LatMult.nonempty_basis_eigenHom | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.LatMult.nonempty_basis_eigenHom <;> assumption)
