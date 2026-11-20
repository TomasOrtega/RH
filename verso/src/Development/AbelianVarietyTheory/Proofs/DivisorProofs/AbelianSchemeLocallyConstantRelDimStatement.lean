import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLocallyConstantRelDim
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbelianSchemeLocallyConstantRelDim.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.abelianScheme_locally_constant_relDim : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ s : S, ∃ (V : S.Opens) (g : ℕ), IsAffineOpen V ∧ s ∈ V ∧ SmoothOfRelativeDimension g (pullback.snd A.hom V.ι) := by
  first | exact @GlobalTheory.DualCon.abelianScheme_locally_relDim | exact GlobalTheory.DualCon.abelianScheme_locally_relDim | (intros; apply GlobalTheory.DualCon.abelianScheme_locally_relDim <;> assumption)
