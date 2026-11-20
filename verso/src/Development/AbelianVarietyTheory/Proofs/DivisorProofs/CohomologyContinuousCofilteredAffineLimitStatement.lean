import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousCofilteredAffineLimit
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtC.contCone_of_affine_limit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCohomologyContinuousCofilteredAffineLimit.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Scheme.{0}) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i)) → ContCone R F (sch.mapCone c) := by
  first
  | exact @GlobalTheory.EtC.contCone_of_affine_limit
  | exact GlobalTheory.EtC.contCone_of_affine_limit
  | (intros; apply GlobalTheory.EtC.contCone_of_affine_limit <;> assumption)
