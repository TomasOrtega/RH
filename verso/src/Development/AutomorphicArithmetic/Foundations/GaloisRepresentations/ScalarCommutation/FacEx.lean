import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLocComm

open NumberField IsDedekindDomain

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.Spc.facEx :
    UpperTheory.Gal.Spc.FacEx := by
  intro E _ _ _ A n p _ S F w
  refine ⟨F.tr.at UpperTheory.Gal.W2.Seed.pLocComm w.1 w.2.1 w.2.2, fun g => ?_, fun y => ?_⟩
  · have h := (F.tr.j_eq (F.tr.sec (F.j g)) g).1 (by rw [F.j_tr]; exact F.tr.j_sec _) w.1 w.2.2
    exact h
  · rw [F.j_tr]
    rfl
