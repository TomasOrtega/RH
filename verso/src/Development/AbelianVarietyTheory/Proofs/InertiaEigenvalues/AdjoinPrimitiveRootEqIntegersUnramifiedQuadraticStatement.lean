import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinPrimitiveRootEqIntegersUnramifiedQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLemma.Unr.adjoin_rootOfUnity_eq_integers` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAdjoinPrimitiveRootEqIntegersUnramifiedQuadratic.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.adjoin_primitiveRoot_eq_integers_unramifiedQuadratic : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) → @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤ → ∀ y : K'.E, @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra y → y ∈ @Algebra.adjoin K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra {z} := by
  first | exact @GlobalTheory.UnitLemma.Unr.adjoin_rootOfUnity_eq_integers | exact GlobalTheory.UnitLemma.Unr.adjoin_rootOfUnity_eq_integers | (intros; apply GlobalTheory.UnitLemma.Unr.adjoin_rootOfUnity_eq_integers <;> assumption)
