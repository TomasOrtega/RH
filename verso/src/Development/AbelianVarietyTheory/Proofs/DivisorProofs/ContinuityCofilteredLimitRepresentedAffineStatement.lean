import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuityCofilteredLimitRepresentedAffine
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.contCone_of_represented`. Consider the case `exact GlobalTheory.contCone_of_represented`. Consider the case `(intros; apply GlobalTheory.contCone_of_represented <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.continuity_cofiltered_limit_represented_affine : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (D : I ⥤ PSh) (c : Cone D), IsLimit c → (∀ i, ∃ Z : Scheme.{0}, IsAffine Z ∧ Nonempty (yoneda.obj Z ≅ D.obj i)) → (∃ Z : Scheme.{0}, Nonempty (yoneda.obj Z ≅ c.pt)) → ContCone R F (disc.mapCone c) := by
  first
  | exact @GlobalTheory.contCone_of_represented
  | exact GlobalTheory.contCone_of_represented
  | (intros; apply GlobalTheory.contCone_of_represented <;> assumption)
