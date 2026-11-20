import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ValsExtOf
import GroundTheory.GlobalFields.KummerTheory.Splitting
import Mathlib.NumberTheory.RamificationInertia.Galois

noncomputable section

open NumberField IsDedekindDomain
open GroundTheory.Global.SemiLocal UpperTheory.V.Z.Gam

namespace UpperTheory.Gal.GamX

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fdegEq : FdegEq := by
  intro K L _ _ _ _ _ _ v
  refine ⟨GroundTheory.Global.nonempty_placesOver L v, fun w w' => ?_⟩
  have hw := w.2
  have hw' := w'.2
  unfold fdeg
  rw [Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w.1.asIdeal,
    Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w'.1.asIdeal]
  exact Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal w.1.asIdeal w'.1.asIdeal Gal(L/K)

end UpperTheory.Gal.GamX
