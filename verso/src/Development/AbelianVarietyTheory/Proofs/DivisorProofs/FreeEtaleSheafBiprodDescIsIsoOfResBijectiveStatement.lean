import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafBiprodDescIsIsoOfResBijective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFreeEtaleSheafBiprodDescIsIsoOfResBijective.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.freeEtaleSheaf_biprodDesc_isIso_of_res_bijective : ∀ (R : Type) [CommRing R] {Y₁ Y₂ X : Scheme.{0}} (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X), (∀ F : Shv R, Function.Bijective fun s : Sec F X => (Sec.res f₁ s, Sec.res f₂ s)) → IsIso (biprod.desc ((free R).map (yoneda.map f₁)) ((free R).map (yoneda.map f₂))) := by
  first | exact @GlobalTheory.EtC.freeYoneda_desc_isIso | exact GlobalTheory.EtC.freeYoneda_desc_isIso | (intros; apply GlobalTheory.EtC.freeYoneda_desc_isIso <;> assumption)
