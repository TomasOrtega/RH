import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafLeOfLeOnReductionsJacobson
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIdealSheafLeOfLeOnReductionsJacobson.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (V : Scheme.{0}) [IsLocallyNoetherian V] (p : V ⟶ Spec (CommRingCat.of R)) (a a' : V.IdealSheafData), UniversallyClosed (a'.subschemeι ≫ p) → (∀ e : ℕ, a ≤ a' ⊔ baseIdeal p (I ^ (e + 1))) → a ≤ a' := by
  first | exact @GlobalTheory.FormalAlg.le_of_le_reductions | exact GlobalTheory.FormalAlg.le_of_le_reductions | (intros; apply GlobalTheory.FormalAlg.le_of_le_reductions <;> assumption)
