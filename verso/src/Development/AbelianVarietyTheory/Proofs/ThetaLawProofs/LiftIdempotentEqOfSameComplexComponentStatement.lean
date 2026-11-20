import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LiftIdempotentEqOfSameComplexComponent
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FThetaLawProofs%2FLiftIdempotentEqOfSameComplexComponent.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.lift_idempotent_eq_of_sameComplexComponent : ∀ (K : Type) [Field K] [Algebra K ℂ] (X : Scheme.{0}) (s : X ⟶ Sp K) (R : Type) [CommRing R] [Algebra K R] (i : Sp R ⟶ X) (p q : R →ₐ[K] ℂ), Smooth s → IsOpenImmersion i → i ≫ s = spMap (algebraMap K R) → SameComp s (algebraMap K ℂ) (spMap p.toRingHom ≫ i) (spMap q.toRingHom ≫ i) → ∀ e : ℂ ⊗[K] R, IsIdempotentElem e → Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) p (fun _ _ => Commute.all _ _) e = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) q (fun _ _ => Commute.all _ _) e := by
  first | exact @GlobalTheory.KeyFam.lift_eq_of_sameComp_of_isIdempotentElem | exact GlobalTheory.KeyFam.lift_eq_of_sameComp_of_isIdempotentElem | (intros; apply GlobalTheory.KeyFam.lift_eq_of_sameComp_of_isIdempotentElem <;> assumption)
