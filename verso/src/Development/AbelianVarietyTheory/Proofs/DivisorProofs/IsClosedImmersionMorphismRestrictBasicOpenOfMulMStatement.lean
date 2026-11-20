import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionMorphismRestrictBasicOpenOfMulM
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsClosedImmersionMorphismRestrictBasicOpenOfMulM.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.isClosedImmersion_restrict_basicOpen_of_mul_mem_range : ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsAffineOpen (φ ⁻¹ᵁ V) → ∀ r : Γ(Z, V), (∀ c : Γ(X, φ ⁻¹ᵁ V), ∃ b : Γ(Z, V), (φ.app V).hom r * c = (φ.app V).hom b) → IsClosedImmersion (φ ∣_ Z.basicOpen r) := by
  first | exact @GlobalTheory.isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range | exact GlobalTheory.isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range | (intros; apply GlobalTheory.isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range <;> assumption)
