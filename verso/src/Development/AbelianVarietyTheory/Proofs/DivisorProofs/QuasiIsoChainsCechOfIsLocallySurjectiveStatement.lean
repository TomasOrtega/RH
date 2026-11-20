import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoChainsCechOfIsLocallySurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FQuasiIsoChainsCechOfIsLocallySurjective.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.quasiIso_chains_cech_of_isLocallySurjective' : ∀ (R : Type) [CommRing R] (P Q : PSh) (f : P ⟶ Q), Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f → QuasiIso ((chains R).map (show ((Arrow.mk f).cechNerve : Spc) ⟶ disc.obj Q from (Arrow.mk f).augmentedCechNerve.hom)) := by
  first | exact @GlobalTheory.EtC.quasiIso_chains_cech_of_isLocallySurjective | exact GlobalTheory.EtC.quasiIso_chains_cech_of_isLocallySurjective | (intros; apply GlobalTheory.EtC.quasiIso_chains_cech_of_isLocallySurjective <;> assumption)
