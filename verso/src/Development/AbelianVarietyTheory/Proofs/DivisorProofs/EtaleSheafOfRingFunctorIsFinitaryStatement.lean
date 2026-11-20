import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorIsFinitary
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ofRings_finitary` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEtaleSheafOfRingFunctorIsFinitary.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.etaleSheafOfRingFunctor_isFinitary : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)), PreservesFilteredColimitsOfSize.{0, 0} M → Finitary (ofRings R M) := by
  first
  | exact @GlobalTheory.ofRings_finitary
  | exact GlobalTheory.ofRings_finitary
  | (intros; apply GlobalTheory.ofRings_finitary <;> assumption)
