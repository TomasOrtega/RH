import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusEndomorphism
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFrobeniusEndomorphism.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.exists_frobenius_endomorphism : ∀ (K : Type) [Field K] [Fintype K] (A : AbVar K), ∃ π : End A, IsFrob π ∧ (∀ x : A.X.left, (Hom.hom (A := A) (B := A) π).left x = x) ∧ ∀ (U : A.X.left.Opens) (h : U ≤ (Hom.hom (A := A) (B := A) π).left ⁻¹ᵁ U) (s : Γ(A.X.left, U)), ((Hom.hom (A := A) (B := A) π).left.appLE U U h).hom s = s ^ Fintype.card K := by
  first | exact @GlobalTheory.AV.FrobPow.exists_isFrob_pow | exact GlobalTheory.AV.FrobPow.exists_isFrob_pow | (intros; apply GlobalTheory.AV.FrobPow.exists_isFrob_pow; all_goals assumption)
