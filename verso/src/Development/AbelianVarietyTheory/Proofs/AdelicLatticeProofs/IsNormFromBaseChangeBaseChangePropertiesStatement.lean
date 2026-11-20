import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsNormFromBaseChangeBaseChangeProperties
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CNorm.tnorm_baseChange` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FIsNormFromBaseChangeBaseChangeProperties.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.isNormFromBaseChange_base_change_properties : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E], (∀ (K K' : Type) [Field K] [Algebra F K] [Field K'] [Algebra F K'] (_ : K →ₐ[F] K') (x : F), TNorm F E K x → TNorm F E K' x) ∧ (∀ (K : Type) [Field K] [Algebra F K] (e : E), TNorm F E K (Algebra.norm F e)) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x y : F), y ≠ 0 → TNorm F E K (x * y) → TNorm F E K y → TNorm F E K x := by
  first | exact @GlobalTheory.CNorm.tnorm_baseChange | exact GlobalTheory.CNorm.tnorm_baseChange | (intros; apply GlobalTheory.CNorm.tnorm_baseChange <;> assumption)
