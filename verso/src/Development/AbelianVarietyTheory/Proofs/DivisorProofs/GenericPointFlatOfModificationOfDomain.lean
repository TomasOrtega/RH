import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SecMoveK
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Use `haveI := M.integral`. Use `haveI := M.dominant`. Use `Flat.of_stalkMap _ fun x => ?_` and prove the remaining obligations. Establish `hx : M.gp.base x = genericPoint M.S`. Establish `hd : DenseRange M.gp.base` using `M.gp.denseRange`.

Establish `hr : Set.range M.gp.base = {M.gp.base x}`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Rewrite using `[Subsingleton.elim z x]`.

Both sides reduce to the same expression. Introduce and unpack `rfl`. Conclude with `⟨x, rfl⟩`. Establish `hg : IsGenericPoint (M.gp.base x) ⊤`. Rewrite using `[IsGenericPoint, ← hr]`.

Simplify `hd.closure_range` using `[Set.top_eq_univ]`. Conclude with `hg.eq (genericPoint_spec M.S)`. Establish `hF : IsField (M.S.presheaf.stalk (M.gp.base x))`. Rewrite using `[hx]`. Conclude with `Field.toIsField _`.

Use `letI : Field (M.S.presheaf.stalk (M.gp.base x)) := hF.toField`. Unfold `RingHom.Flat`. Conclude with `inferInstance`.
-/
theorem Modif.flat_gp (R : Type) [CommRing R] [IsDomain R] (M : Modif R) : Flat M.gp := by
  haveI := M.integral
  haveI := M.dominant
  refine Flat.of_stalkMap _ fun x => ?_
  have hx : M.gp.base x = genericPoint M.S := by
    have hd : DenseRange M.gp.base := M.gp.denseRange
    have hr : Set.range M.gp.base = {M.gp.base x} := by
      ext y; constructor
      · rintro ⟨z, rfl⟩; rw [Subsingleton.elim z x]; rfl
      · rintro rfl; exact ⟨x, rfl⟩
    have hg : IsGenericPoint (M.gp.base x) ⊤ := by
      rw [IsGenericPoint, ← hr]
      simpa [Set.top_eq_univ] using hd.closure_range
    exact hg.eq (genericPoint_spec M.S)
  have hF : IsField (M.S.presheaf.stalk (M.gp.base x)) := by
    rw [hx]; exact Field.toIsField _
  letI : Field (M.S.presheaf.stalk (M.gp.base x)) := hF.toField
  unfold RingHom.Flat
  exact inferInstance

end GlobalTheory.Mum
