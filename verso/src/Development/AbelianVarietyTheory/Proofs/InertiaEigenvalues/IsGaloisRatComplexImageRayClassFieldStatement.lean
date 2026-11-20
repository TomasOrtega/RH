import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaloisRatComplexImageRayClassField
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsGaloisRatComplexImageRayClassField.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.isGalois_rat_complexImage_rayClassField : ∀ {K H : Type} [Field K] [NumberField K] [IsGalois ℚ K] [Field H] [NumberField H] [Algebra K H] [IsAbelianGalois K H] {n : ℕ}, n ≠ 0 → GlobalTheory.FieldSize.IsRay H (Ideal.span {(n : 𝓞 K)}) → ∀ j : H →+* ℂ, IsGalois ℚ j.toRatAlgHom.fieldRange := by
  first | exact @GlobalTheory.RayNatGalois.isGalois_fieldRange | exact GlobalTheory.RayNatGalois.isGalois_fieldRange | (intros; apply GlobalTheory.RayNatGalois.isGalois_fieldRange <;> assumption)
