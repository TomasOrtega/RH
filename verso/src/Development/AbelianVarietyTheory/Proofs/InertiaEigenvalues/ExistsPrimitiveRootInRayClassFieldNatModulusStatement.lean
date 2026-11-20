import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveRootInRayClassFieldNatModulus
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsPrimitiveRootInRayClassFieldNatModulus.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.exists_primitiveRoot_in_rayClassField_natModulus : ∀ {K H : Type} [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] [IsAbelianGalois K H] {n : ℕ}, n ≠ 0 → GlobalTheory.FieldSize.IsRay H (Ideal.span {(n : 𝓞 K)}) → ∃ ζ : H, IsPrimitiveRoot ζ n := by
  first | exact @GlobalTheory.RayRootOfUnity.exists_isPrimitiveRoot_of_isRay | exact GlobalTheory.RayRootOfUnity.exists_isPrimitiveRoot_of_isRay | (intros; apply GlobalTheory.RayRootOfUnity.exists_isPrimitiveRoot_of_isRay <;> assumption)
