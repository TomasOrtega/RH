import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUnifRefl
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatTorsionIsomorphism
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.TorsionRepresent

section
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] (k : ℕ)

noncomputable def incl : GlobalTheory.IndefiniteRowSideFullHecke.FlatTorsionIsomorphism.torsScheme G k ⟶ G :=
  pullback.fst ((𝟙 G : G ⟶ G) ^ k) η[G]

instance : Mono (incl G k) := by
  have : Mono η[G] := ⟨fun _ _ _ => toUnit_unique _ _⟩
  exact pullback.fst_of_mono

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem comp_incl_pow {T : Over S} (y : T ⟶ GlobalTheory.IndefiniteRowSideFullHecke.FlatTorsionIsomorphism.torsScheme G k) : (y ≫ incl G k) ^ k = 1 := by
  have h : incl G k ≫ ((𝟙 G : G ⟶ G) ^ k) = pullback.snd ((𝟙 G : G ⟶ G) ^ k) η[G] ≫ η[G] := pullback.condition
  rw [MonObj.comp_pow, Category.comp_id] at h
  have h1 : incl G k ^ k = 1 := by
    rw [h, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  rw [← MonObj.comp_pow, h1, MonObj.comp_one]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem exists_lift {T : Over S} (x : T ⟶ G) (hx : x ^ k = 1) :
    ∃ y : T ⟶ GlobalTheory.IndefiniteRowSideFullHecke.FlatTorsionIsomorphism.torsScheme G k, y ≫ incl G k = x := by
  refine ⟨pullback.lift x (toUnit _) ?_, pullback.lift_fst _ _ _⟩
  rw [MonObj.comp_pow, Category.comp_id, hx, Hom.one_def]

end

end GlobalTheory.TorsionRepresent
