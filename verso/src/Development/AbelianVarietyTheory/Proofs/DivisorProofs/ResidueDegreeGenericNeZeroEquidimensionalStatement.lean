import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericNeZeroEquidimensional
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FResidueDegreeGenericNeZeroEquidimensional.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.residue_degree_generic_ne_zero_equidimensional : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp F) (f : M ⟶ W) (n : ℕ), LocallyOfFiniteType p → LocallyOfFiniteType f → Surjective f → topologicalKrullDim M = n → topologicalKrullDim W = n → f.residueDegree (genericPoint M) ≠ 0 := by
  first | exact @GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero | exact GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero | (intros; apply GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero <;> assumption)
