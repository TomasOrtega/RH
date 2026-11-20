import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KunnethCupTensorInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKunnethCupTensorInjective.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.kunneth_cup_tensor_injective : ∀ (K : Type) [Field K] (X Y : Over (Sp K)), IsSeparated X.hom → QuasiCompact X.hom → IsSeparated Y.hom → QuasiCompact Y.hom → ∀ (n : ℕ) (x : Fin n → HO1 X.hom) (y : Fin n → HO1 Y.hom), ∑ i, cup (OAff (X ⊗ Y).hom) (pO1 (fst X Y) (x i)) (pO1 (snd X Y) (y i)) = 0 → ∑ i, x i ⊗ₜ[K] y i = 0 := by
  first | exact @GlobalTheory.Kunneth.cup_tmul_injective | exact GlobalTheory.Kunneth.cup_tmul_injective | (intros; apply GlobalTheory.Kunneth.cup_tmul_injective <;> assumption)
