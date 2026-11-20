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
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Equip the data with the indicated structure. Replace the relevant objects with their definitions. A detailed English derivation is pending.
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
