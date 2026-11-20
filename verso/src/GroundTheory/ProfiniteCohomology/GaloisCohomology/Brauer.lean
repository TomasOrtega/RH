import Mathlib
import GroundTheory.ProfiniteCohomology.Colimit
import GroundTheory.ProfiniteCohomology.GaloisCohomology.UnitsInflationCochainsFHomApply
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology IntermediateField

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]

noncomputable def unitsInflation (E : IntermediateField K L) [FiniteDimensional K E] [Normal K E]
    (n : ℕ) : groupCohomology (galUnits.{u} K E) n ⟶ cohomology (galUnits.{u} K L) n :=
  HomologicalComplex.homologyMap (unitsInflationCochains E) n

noncomputable abbrev brauerInflation (E : IntermediateField K L) [FiniteDimensional K E]
    [Normal K E] : groupCohomology (galUnits.{u} K E) 2 ⟶ galoisBrauerGroup K L :=
  unitsInflation E 2

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem quotientEquivGal_mk_eq_restrictNormalHom (U : OpenNormalSubgroup Gal(L/K))
    (σ : Gal(L/K)) :
    quotientEquivGal U (σ : Gal(L/K) ⧸ (U : Subgroup Gal(L/K))) =
      AlgEquiv.restrictNormalHom (fixedField (U : Subgroup Gal(L/K))) σ := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  rw [quotientEquivGal_mk_apply]
  exact (AlgEquiv.restrictNormal_commutes σ _ x).symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem inflation_galUnits_eq (U : OpenNormalSubgroup Gal(L/K)) (n : ℕ) :
    inflation (galUnits.{u} K L) U n =
      (groupCohomologyQuotientGalUnitsIso U n).hom ≫
        unitsInflation (fixedField (U : Subgroup Gal(L/K))) n := by
  rw [groupCohomologyQuotientGalUnitsIso, groupCohomology.mapIso_hom]
  unfold inflation unitsInflation
  refine Eq.trans ?_ (HomologicalComplex.homologyMap_comp _ _ n)
  congr 1
  ext m : 1
  rw [← cancel_mono ((cochainsComplexι (galUnits.{u} K L)).f m), HomologicalComplex.comp_f,
    Category.assoc]
  ext x : 2
  funext g
  have hq : ∀ i, (quotientEquivGal U).symm
      (AlgEquiv.restrictNormalHom (fixedField (U : Subgroup Gal(L/K))) (g i)) =
        (g i : Gal(L/K) ⧸ (U : Subgroup Gal(L/K))) := fun i =>
    (MulEquiv.symm_apply_eq _).2 (quotientEquivGal_mk_eq_restrictNormalHom U (g i)).symm
  change ((x fun i => (g i : Gal(L/K) ⧸ (U : Subgroup Gal(L/K)))).1 : Additive Lˣ) =
    (unitsRestrictHom (fixedField (U : Subgroup Gal(L/K)))).hom
      (invariantsGalUnitsAddEquiv (U : Subgroup Gal(L/K))
        (x fun i => (quotientEquivGal U).symm
          (AlgEquiv.restrictNormalHom (fixedField (U : Subgroup Gal(L/K))) (g i))))
  simp only [hq]
  exact Additive.toMul.injective (Units.ext rfl)

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem exists_unitsInflation_eq (n : ℕ) (x : cohomology (galUnits.{u} K L) n) :
    ∃ (E : FiniteGaloisIntermediateField K L)
      (y : groupCohomology (galUnits.{u} K E.toIntermediateField) n),
      (unitsInflation E.toIntermediateField n).hom y = x := by
  obtain ⟨U, y, rfl⟩ := exists_inflation_eq (galUnits.{u} K L) n x
  refine ⟨fixedFiniteGalois U, (groupCohomologyQuotientGalUnitsIso U n).hom.hom y, ?_⟩
  rw [inflation_galUnits_eq]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exists_brauerInflation_eq (x : galoisBrauerGroup K L) :
    ∃ (E : FiniteGaloisIntermediateField K L)
      (y : groupCohomology (galUnits.{u} K E.toIntermediateField) 2),
      (brauerInflation E.toIntermediateField).hom y = x :=
  exists_unitsInflation_eq 2 x

end GroundTheory.ProfCoh
