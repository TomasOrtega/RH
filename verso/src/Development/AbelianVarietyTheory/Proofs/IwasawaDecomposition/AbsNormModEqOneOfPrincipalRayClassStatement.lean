import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsNormModEqOneOfPrincipalRayClass
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAbsNormModEqOneOfPrincipalRayClass.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.absNorm_modEq_one_of_principal_rayClass : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (𝔮 : Ideal (𝓞 K)) (p : ℕ), 𝔮 ≤ Ideal.span {(p : 𝓞 K)} → ∀ (I : Ideal (𝓞 K)) (α β : 𝓞 K), RayPair 𝔮 α β → I * Ideal.span {β} = Ideal.span {α} → Ideal.absNorm I ≡ 1 [MOD p] := by
  first | exact @GlobalTheory.Mem.RayNorm.absNorm_modEq_one | exact GlobalTheory.Mem.RayNorm.absNorm_modEq_one | (intros; apply GlobalTheory.Mem.RayNorm.absNorm_modEq_one <;> assumption)
