import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaEvenDegenerationGlobalOfLocalUnits
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKeyFormulaEvenDegenerationGlobalOfLocalUnits.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.key_formula_even_degeneration_global_of_local_units : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ → KeyGlob := by
  first | exact @GlobalTheory.KeyEvenGlue.keyGlob_of_keyLoc | exact GlobalTheory.KeyEvenGlue.keyGlob_of_keyLoc | (intros; apply GlobalTheory.KeyEvenGlue.keyGlob_of_keyLoc <;> assumption)
