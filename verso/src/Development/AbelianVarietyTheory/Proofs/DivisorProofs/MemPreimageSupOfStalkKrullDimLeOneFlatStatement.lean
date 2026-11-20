import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPreimageSupOfStalkKrullDimLeOneFlat
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
Apply `GlobalTheory.CodimOne.mem_preimage_sup_of_ringKrullDim_stalk_le_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMemPreimageSupOfStalkKrullDimLeOneFlat.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.mem_preimage_sup_of_stalk_krullDim_le_one_flat : ∀ (X S : Scheme.{0}) [IsIntegral S] (f : X ⟶ S) [Flat f] [GeometricallyIntegral f] (V : X.Opens) (U : S.Opens), (∀ s : S, ∃ x ∈ V, f x = s) → (U : Set S).Nonempty → (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ f ⁻¹ᵁ U ⊔ V) := by
  first | exact @GlobalTheory.CodimOne.mem_preimage_sup_of_ringKrullDim_stalk_le_one | exact GlobalTheory.CodimOne.mem_preimage_sup_of_ringKrullDim_stalk_le_one | (intros; apply GlobalTheory.CodimOne.mem_preimage_sup_of_ringKrullDim_stalk_le_one <;> assumption)
