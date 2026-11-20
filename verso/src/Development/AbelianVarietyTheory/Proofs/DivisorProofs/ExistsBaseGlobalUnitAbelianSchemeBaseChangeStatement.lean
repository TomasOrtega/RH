import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseGlobalUnitAbelianSchemeBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulIncl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TwoTors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsBaseGlobalUnitAbelianSchemeBaseChange.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_base_globalUnit_abelianScheme_baseChange : ∀ {S X : Scheme.{0}} (A Z : Over S) [GrpObj A], IsAbelianScheme A → ∀ (p : X ⟶ A.left) (q : X ⟶ Z.left), IsPullback p q A.hom Z.hom → ∀ D : Γ(X, ⊤)ˣ, ∃ c : Γ(Z.left, ⊤)ˣ, GlobalTheory.CharKer.pullTop q c = D := by
  first | exact @GlobalTheory.CharKer.exists_pullTop_of_isPullback | exact GlobalTheory.CharKer.exists_pullTop_of_isPullback | (intros; apply GlobalTheory.CharKer.exists_pullTop_of_isPullback <;> assumption)
