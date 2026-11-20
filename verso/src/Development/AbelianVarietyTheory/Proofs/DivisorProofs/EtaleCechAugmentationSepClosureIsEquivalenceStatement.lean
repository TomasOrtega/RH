import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechAugmentationSepClosureIsEquivalence
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SepCech.cechAug_sepClosure_eqv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEtaleCechAugmentationSepClosureIsEquivalence.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.etaleCechAugmentation_sepClosure_isEquivalence : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω], Eqv R (cechAug (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) F := by
  first
  | exact @GlobalTheory.SepCech.cechAug_sepClosure_eqv
  | exact GlobalTheory.SepCech.cechAug_sepClosure_eqv
  | (intros; apply GlobalTheory.SepCech.cechAug_sepClosure_eqv <;> assumption)
