import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeTheoreticallyDominantOfGermInjective
import Mathlib
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchemeTheoreticallyDominantOfGermInjective.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.schemeTheoreticallyDominant_of_germ_injective : ∀ (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens),
    (∀ (U : X.Opens) (V : T.Opens), IsAffineOpen U → IsAffineOpen V → U ≤ p ⁻¹ᵁ V →
      ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) → b = 0) →
    IsSchemeTheoreticallyDominant W.ι := by
  first | exact @GlobalTheory.isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine | exact GlobalTheory.isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine | (intros; apply GlobalTheory.isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine <;> assumption)
