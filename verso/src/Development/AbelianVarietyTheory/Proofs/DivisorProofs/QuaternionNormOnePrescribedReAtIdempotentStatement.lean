import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOnePrescribedReAtIdempotent
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.quat_norm_one_re_at_idem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FQuaternionNormOnePrescribedReAtIdempotent.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.quaternion_norm_one_prescribed_re_at_idempotent : ∀ (R : Type) [CommRing R] (a b ε p q : R), ε * ε = ε → IsUnit a → IsUnit b → IsUnit (2 : R) → ε * (b - (p ^ 2 - a * q ^ 2)) = 0 → ∀ t : R, ∃ h : ℍ[R, a, b], nrm h = 1 ∧ ε * h.re = ε * t := by
  first | exact @GlobalTheory.quat_norm_one_re_at_idem | exact GlobalTheory.quat_norm_one_re_at_idem | (intros; apply GlobalTheory.quat_norm_one_re_at_idem <;> assumption)
