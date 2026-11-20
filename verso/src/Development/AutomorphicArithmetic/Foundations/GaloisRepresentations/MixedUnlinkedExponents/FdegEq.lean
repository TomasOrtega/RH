import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ValsExtOf
import GroundTheory.GlobalFields.KummerTheory.Splitting
import Mathlib.NumberTheory.RamificationInertia.Galois

noncomputable section

open NumberField IsDedekindDomain
open GroundTheory.Global.SemiLocal UpperTheory.V.Z.Gam

namespace UpperTheory.Gal.GamX

/- English proof (translation)
Introduce `K L _ _ _ _ _ _ v`. Use `⟨GroundTheory.Global.nonempty_placesOver L v, fun w w' => ?_⟩` and prove the remaining obligations. Establish `hw` using `w.2`. Establish `hw'` using `w'.2`. Unfold `fdeg`.

Rewrite using `[Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w.1.asIdeal, Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w'.1.asIdeal]`. Conclude with `Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal w.1.asIdeal w'.1.asIdeal Gal(L/K)`.
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
