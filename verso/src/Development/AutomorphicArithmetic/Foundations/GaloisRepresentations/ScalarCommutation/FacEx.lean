import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLocComm

open NumberField IsDedekindDomain

/- English proof (translation)
Introduce `E _ _ _ A n p _ S F w`. Use `⟨F.tr.at UpperTheory.Gal.W2.Seed.pLocComm w.1 w.2.1 w.2.2, fun g => ?_, fun y => ?_⟩` and prove the remaining obligations. Establish `h` using `(F.tr.j_eq (F.tr.sec (F.j g)) g).1 (by rw [F.j_tr]; exact F.tr.j_sec _) w.1 w.2.2`. Conclude with `h`. Rewrite using `[F.j_tr]`.

Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.Spc.facEx :
    UpperTheory.Gal.Spc.FacEx := by
  intro E _ _ _ A n p _ S F w
  refine ⟨F.tr.at UpperTheory.Gal.W2.Seed.pLocComm w.1 w.2.1 w.2.2, fun g => ?_, fun y => ?_⟩
  · have h := (F.tr.j_eq (F.tr.sec (F.j g)) g).1 (by rw [F.j_tr]; exact F.tr.j_sec _) w.1 w.2.2
    exact h
  · rw [F.j_tr]
    rfl
