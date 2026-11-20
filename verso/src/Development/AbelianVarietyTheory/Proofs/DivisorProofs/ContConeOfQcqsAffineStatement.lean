import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContConeOfQcqsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContConeOfQcqsAffine.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.contCone_of_isLimit_of_qcqs_affine_transitions : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Scheme.{0}) (c : Cone G), IsLimit c → (∀ i, CompactSpace (G.obj i)) → (∀ i, QuasiSeparatedSpace (G.obj i)) → (∀ (i j : I) (f : i ⟶ j), IsAffineHom (G.map f)) → ContCone R F (sch.mapCone c) := by
  first
  | exact @GlobalTheory.EtC.contCone_of_qcqs_affine
  | exact GlobalTheory.EtC.contCone_of_qcqs_affine
  | (intros; apply GlobalTheory.EtC.contCone_of_qcqs_affine <;> assumption)
