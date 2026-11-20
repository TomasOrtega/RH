import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubquotientSemisimpleRestriction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
open GlobalTheory.PRep GlobalTheory.SmGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IrrSubImage.exists_irreducible_le_range` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSubquotientSemisimpleRestriction.lean&line=200#L200)
-/
theorem _root_.GlobalTheory.T.subquotient_semisimple_restriction : ∀ (L H : Type) [Group L] [Group H] (s : H →* L) (X : Type) [AddCommGroup X]
    [Module ℂ X] (σ : Representation ℂ L X), GlobalTheory.SmGL.HasFiniteLength σ →
    (∀ (Z : Type) [AddCommGroup Z] [Module ℂ Z] (τ : Representation ℂ L Z), GlobalTheory.SmGL.IsSubquotient τ σ →
      τ.IsIrreducible → Representation.IsSemisimpleRepresentation (τ.comp s)) →
    ∀ (S : Subrepresentation (σ.comp s)) (Y : Type) [AddCommGroup Y] [Module ℂ Y]
      (η : Representation ℂ H Y) (F : S.toRepresentation.IntertwiningMap η), F ≠ 0 →
      ∃ R : Subrepresentation η, R.toRepresentation.IsIrreducible ∧
        R.toSubmodule ≤ LinearMap.range F.toLinearMap := by
  first | exact @GlobalTheory.IrrSubImage.exists_irreducible_le_range | exact GlobalTheory.IrrSubImage.exists_irreducible_le_range | (intros; apply GlobalTheory.IrrSubImage.exists_irreducible_le_range <;> assumption)
