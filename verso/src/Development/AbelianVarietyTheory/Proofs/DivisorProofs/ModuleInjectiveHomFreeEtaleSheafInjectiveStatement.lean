import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleInjectiveHomFreeEtaleSheafInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FModuleInjectiveHomFreeEtaleSheafInjective.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.moduleInjective_hom_free_etaleSheaf_injective : ∀ (R : Type) [CommRing R] (J : Shv R) [Injective J] (P : PSh), Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J) := by
  first | exact @GlobalTheory.EtC.HomInj.hom_free_injective | exact GlobalTheory.EtC.HomInj.hom_free_injective | (intros; apply GlobalTheory.EtC.HomInj.hom_free_injective <;> assumption)
