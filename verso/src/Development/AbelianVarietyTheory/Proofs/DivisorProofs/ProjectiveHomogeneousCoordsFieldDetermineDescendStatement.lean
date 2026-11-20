import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsFieldDetermineDescend
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UMin.CrdUniq.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProjectiveHomogeneousCoordsFieldDetermineDescend.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.projectiveHomogeneousCoords_field_determine_descend : (∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x x' : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K), x ≫ PSpace.str o n = x' ≫ PSpace.str o n → PCrd x v → PCrd x' v → x = x') ∧ (∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v w : Fin (n + 1) → K), PCrd x v → PCrd x w → ∃ a : K, a ≠ 0 ∧ ∀ j, w j = a * v j) ∧ ∀ (o K K' : Type) [CommRing o] [Field K] [Field K'] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K) (i : K →+* K'), PCrd (spMap i ≫ x) (fun j => i (v j)) → PCrd x v := by
  first | exact @GlobalTheory.UMin.CrdUniq.main | exact GlobalTheory.UMin.CrdUniq.main | (intros; apply GlobalTheory.UMin.CrdUniq.main <;> assumption)
