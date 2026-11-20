import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardExtendOfLocallyTrivialNormalCodimTwo
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCechPicardExtendOfLocallyTrivialNormalCodimTwo.lean&line=169#L169)
-/
theorem _root_.GlobalTheory.T.cechPicard_extend_of_locally_trivial_normal_codimTwo : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ W : X.Opens, (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → ∀ c : Pic W.toScheme, (∀ x : X, ∃ N : X.Opens, x ∈ N ∧ GlobalTheory.CechPic.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) c = 0) → ∃ c' : Pic X, GlobalTheory.CechPic.pull W.ι c' = c := by
  first | exact @GlobalTheory.extend_class_of_locally_trivial | exact GlobalTheory.extend_class_of_locally_trivial | (intros; apply GlobalTheory.extend_class_of_locally_trivial <;> assumption)
