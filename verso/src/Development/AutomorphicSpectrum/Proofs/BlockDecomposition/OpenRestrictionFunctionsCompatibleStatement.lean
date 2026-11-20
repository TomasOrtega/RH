import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenRestrictionFunctionsCompatible
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSections
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct Opposite
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FOpenRestrictionFunctionsCompatible.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.open_restriction_functions_compatible : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X), φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)], letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩; ∀ (W : (φ ⁻¹ᵁ V).toScheme.Opens) (a : A), ((φ ⁻¹ᵁ V).ι.appIso W).hom (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ W) a) = toFunctions (A := Γ(X, V)) W (toFunctions (A := A) V a) := by
  first | exact @GlobalTheory.CompanionTheory.GE.RingCompat.toFunctions_preimage | exact GlobalTheory.CompanionTheory.GE.RingCompat.toFunctions_preimage | (intros; apply GlobalTheory.CompanionTheory.GE.RingCompat.toFunctions_preimage <;> assumption)
