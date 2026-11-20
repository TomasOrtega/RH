import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsEigvec

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
The claim follows from `(residue_ne_zero_iff_isUnit x).1 h.ne_zero`.
-/
private theorem unit_of_res {R : Type} [CommRing R] [IsLocalRing R] {x : R} (h : IsUnit (residue R x)) :
    IsUnit x :=
  (residue_ne_zero_iff_isUnit x).1 h.ne_zero

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qf19.exists_canon`.
-/
theorem UpperTheory.V.UnitaryThreeInertia.exists_canon :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (X : Matrix (Fin 3) (Fin 3) R), (∀ a b, a ≠ b → IsUnit (X a a - X b b)) → (∀ a b, a ≠ b → X a b ∈ maximalIdeal R) → ∃ h, Canon X h :=
  _root_.UpperTheory.Reformulated.B.Qf19.exists_canon
