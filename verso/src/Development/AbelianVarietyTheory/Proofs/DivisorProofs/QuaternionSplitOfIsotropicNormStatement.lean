import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionSplitOfIsotropicNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.quaternion_split_of_isotropic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FQuaternionSplitOfIsotropicNorm.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.quaternion_split_of_isotropic_norm : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0) → ∃ φ : ℍ[F, a, b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F, ∀ x, (φ x).det = nrm x := by
  first | exact @GlobalTheory.quaternion_split_of_isotropic | exact GlobalTheory.quaternion_split_of_isotropic | (intros; apply GlobalTheory.quaternion_split_of_isotropic <;> assumption)
