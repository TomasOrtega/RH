import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroDeformationFactorsThroughLinear
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FirstOrderPoints.exists_linearCombination_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSquareZeroDeformationFactorsThroughLinear.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.square_zero_deformation_factors_through_linear : ∀ (R₀ B K : Type) [CommRing R₀] [CommRing B] [Algebra R₀ B] [Field K] (n : ℕ),
    Algebra.IsStandardSmoothOfRelativeDimension n R₀ B → ∀ (ι : Type) [Fintype ι], Fintype.card ι = n →
    ∀ R : B →+* TrivSqZeroExt K (ι → K), (∀ a : R₀, R (algebraMap R₀ B a) = TrivSqZeroExt.inl (R (algebraMap R₀ B a)).fst) →
    (∀ M M' : ι → K, (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom.comp R =
      (TrivSqZeroExt.map (Fintype.linearCombination K M')).toRingHom.comp R → M = M') →
    ∀ g : B →+* DualNumber K, (∀ b, (g b).fst = (R b).fst) →
    (∀ a : R₀, g (algebraMap R₀ B a) = TrivSqZeroExt.inl (g (algebraMap R₀ B a)).fst) →
    ∃ M : ι → K, g = (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom.comp R := by
  first | exact @GlobalTheory.FirstOrderPoints.exists_linearCombination_eq | exact GlobalTheory.FirstOrderPoints.exists_linearCombination_eq | (intros; apply GlobalTheory.FirstOrderPoints.exists_linearCombination_eq <;> assumption)
