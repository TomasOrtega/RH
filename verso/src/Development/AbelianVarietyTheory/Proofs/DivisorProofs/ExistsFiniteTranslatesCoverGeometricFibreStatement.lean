import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTranslatesCoverGeometricFibre
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
Apply `GlobalTheory.FibreCover.cover_geometric_fibre` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFiniteTranslatesCoverGeometricFibre.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.exists_finite_translates_cover_geometric_fibre : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens) (K : Type) [Field K] [IsAlgClosed K] (ξ : Sp K ⟶ S), (∀ z, ∃ x ∈ V, A.hom x = ξ z) → ∃ (n : ℕ) (a : Fin n → (Over.mk ξ ⟶ A)), ⨆ i, ((fst A (Over.mk ξ) * (snd A (Over.mk ξ) ≫ a i)).left ⁻¹ᵁ V ⊓ (fst A (Over.mk ξ) * (snd A (Over.mk ξ) ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ := by
  first | exact @GlobalTheory.FibreCover.cover_geometric_fibre | exact GlobalTheory.FibreCover.cover_geometric_fibre | (intros; apply GlobalTheory.FibreCover.cover_geometric_fibre <;> assumption)
