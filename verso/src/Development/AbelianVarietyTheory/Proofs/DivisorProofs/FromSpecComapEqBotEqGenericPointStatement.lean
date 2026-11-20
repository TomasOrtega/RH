import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecComapEqBotEqGenericPoint
import Mathlib
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFromSpecComapEqBotEqGenericPoint.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.fromSpec_comap_eq_bot_eq_genericPoint : ∀ (X Y : Scheme.{0}) [IsIntegral X] (π : Y ⟶ X) (V : X.Opens), IsAffineOpen V → ∀ (hW : IsAffineOpen (π ⁻¹ᵁ V)) (P : Ideal Γ(Y, π ⁻¹ᵁ V)) (hP : P.IsPrime), P.comap (π.app V).hom = ⊥ → π (hW.fromSpec ⟨P, hP⟩) = genericPoint X := by
  first | exact @GlobalTheory.fromSpec_prime_comap_bot_lies_over_genericPoint | exact GlobalTheory.fromSpec_prime_comap_bot_lies_over_genericPoint | (intros; apply GlobalTheory.fromSpec_prime_comap_bot_lies_over_genericPoint <;> assumption)
