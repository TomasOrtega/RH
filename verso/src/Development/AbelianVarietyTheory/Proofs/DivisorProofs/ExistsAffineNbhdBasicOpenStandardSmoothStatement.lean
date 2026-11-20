import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdBasicOpenStandardSmooth
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsAffineNbhdBasicOpenStandardSmooth.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.exists_affine_nbhd_basicOpen_standardSmooth : ∀ (g : ℕ) (C Z : Scheme.{0}) [IsAffine Z] (e : C ⟶ Z), SmoothOfRelativeDimension g e → ∀ x : C, ∃ O : C.Opens, IsAffineOpen O ∧ x ∈ O ∧ ∀ r : Γ(C, O), (((C.basicOpen r).ι ≫ e).appTop).hom.IsStandardSmoothOfRelativeDimension g := by
  first | exact @GlobalTheory.Pinch.exists_affine_basicOpen_standardSmooth | exact GlobalTheory.Pinch.exists_affine_basicOpen_standardSmooth | (intros; apply GlobalTheory.Pinch.exists_affine_basicOpen_standardSmooth <;> assumption)
