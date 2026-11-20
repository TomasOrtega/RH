import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraCoefficientsRestrictionBijective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh GlobalTheory.CatCoh
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CxCoh.single_algebra_restriction_bijective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAlgebraCoefficientsRestrictionBijective.lean&line=114#L114)
-/
theorem _root_.GlobalTheory.T.algebra_coefficients_restriction_bijective : ∀ (R : Type) [CommRing R] (C C' : Type 1) [Category.{0} C] [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Bijective (CoefMap.restrict F G).pull1 → Function.Bijective (CoefMap.restrict F G).pull2 → ((Cx.single (Coef.ofAlg F)).resMap G).PullbackBijectiveDegreesOneTwo := by
  first | exact @GlobalTheory.CxCoh.single_algebra_restriction_bijective | exact GlobalTheory.CxCoh.single_algebra_restriction_bijective | (intros; apply GlobalTheory.CxCoh.single_algebra_restriction_bijective <;> assumption)
