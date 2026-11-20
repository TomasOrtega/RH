import Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfD
import Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfF
import Development.EtaleCohomology.EtaleSheaves.LeafFinInfPf
import Development.EtaleCohomology.EtaleSheaves.LeafFinValPf

open Polynomial IntermediateField.algebraAdjoinAdjoin

namespace LateralTheory.E.CurveUnitsOrderAtInfinity

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem minpolyCoeff : LateralTheory.E.E4.LeafMinpolyCoeff := by
  intro k L _ _ _ s hs F hF x hx i
  subst hF
  have : UniqueFactorizationMonoid (Algebra.adjoin k {s}) := hs.uniqueFactorizationMonoid_adjoin
  have : IsIntegrallyClosed (Algebra.adjoin k {s}) := inferInstance
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' (IntermediateField.adjoin k {s}) hx, coeff_map]
  exact ((minpoly (Algebra.adjoin k {s}) x).coeff i).2

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ordInfHom : LateralTheory.E.E4.LeafOrdInfHom :=
  LateralTheory.E.E4.LeafOrdInfHom_of_local (LateralTheory.E.E4.LeafOrdInfLocal_of' LateralTheory.E.E4.LeafFinInf_of LateralTheory.E.E4.LeafFinVal_of)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LeafUnits_of : LateralTheory.E.E4.LeafUnits :=
  LateralTheory.E.E4.LeafUnits_of (LateralTheory.E.E4.LeafUnitsFG_of_dim LateralTheory.E.E4.LeafNoetherDim_of
    (LateralTheory.E.E4.LeafOrdAtInfinity_of_cut ordInfHom minpolyCoeff))

end LateralTheory.E.CurveUnitsOrderAtInfinity
