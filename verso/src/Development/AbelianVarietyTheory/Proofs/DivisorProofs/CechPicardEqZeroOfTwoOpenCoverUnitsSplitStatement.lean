import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardEqZeroOfTwoOpenCoverUnitsSplit
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CechPic.eq_zero_of_pull_eq_zero_of_units_split` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCechPicardEqZeroOfTwoOpenCoverUnitsSplit.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.cechPicard_eq_zero_of_twoOpen_cover_units_split : ∀ (Z : Scheme.{0}) (O O' : Z.Opens), O ⊔ O' = ⊤ → (∀ F : Γ(Z, O ⊓ O')ˣ, ∃ (u : Γ(Z, O)ˣ) (u' : Γ(Z, O')ˣ), F = res (inf_le_left : O ⊓ O' ≤ O) u * res (inf_le_right : O ⊓ O' ≤ O') u') → ∀ c : Pic Z, GlobalTheory.CechPic.pull O.ι c = 0 → GlobalTheory.CechPic.pull O'.ι c = 0 → c = 0 := by
  first | exact @GlobalTheory.CechPic.eq_zero_of_pull_eq_zero_of_units_split | exact GlobalTheory.CechPic.eq_zero_of_pull_eq_zero_of_units_split | (intros; apply GlobalTheory.CechPic.eq_zero_of_pull_eq_zero_of_units_split <;> assumption)
