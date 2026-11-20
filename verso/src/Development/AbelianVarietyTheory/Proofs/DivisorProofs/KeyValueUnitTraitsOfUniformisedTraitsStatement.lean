import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUnitTraitsOfUniformisedTraits
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKeyValueUnitTraitsOfUniformisedTraits.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.keyValue_unit_traits_of_uniformised_traits : ∀ κ : Rule, KeyTraitU κ → KeyTrait κ := by
  first | exact @GlobalTheory.KeyEven.keyTrait_of_keyTraitU | exact GlobalTheory.KeyEven.keyTrait_of_keyTraitU | (intros; apply GlobalTheory.KeyEven.keyTrait_of_keyTraitU <;> assumption)
