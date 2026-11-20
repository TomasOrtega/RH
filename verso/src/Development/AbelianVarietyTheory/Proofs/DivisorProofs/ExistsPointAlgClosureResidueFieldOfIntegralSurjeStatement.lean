import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointAlgClosureResidueFieldOfIntegralSurje
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPointAlgClosureResidueFieldOfIntegralSurje.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.exists_point_algClosure_residueField_of_integral_surjective : ∀ (A : Type) [CommRing A] [IsLocalRing A] (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of A)),
    IsIntegralHom g → Surjective g → ∃ s : Spec (CommRingCat.of (AlgebraicClosure (IsLocalRing.ResidueField A))) ⟶ Y,
    s ≫ g = Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure (IsLocalRing.ResidueField A)))) := by
  first | exact @GlobalTheory.exists_point_algClosure_residueField_of_isIntegralHom | exact GlobalTheory.exists_point_algClosure_residueField_of_isIntegralHom | (intros; apply GlobalTheory.exists_point_algClosure_residueField_of_isIntegralHom <;> assumption)
