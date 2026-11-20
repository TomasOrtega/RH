import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionAlgebraTopologicalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FQuaternionAlgebraTopologicalRing.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.quaternion_algebra_topological_ring : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a b : R), IsTopologicalRing ℍ[R, a, b] ∧ Continuous (nrm : ℍ[R, a, b] → R) ∧ Continuous (fun x : ℍ[R, a, b] => x.re) ∧ (T2Space R → T2Space ℍ[R, a, b]) := by
  first | exact @GlobalTheory.quaternion_isTopologicalRing_nrm_re_t2 | exact GlobalTheory.quaternion_isTopologicalRing_nrm_re_t2 | (intros; apply GlobalTheory.quaternion_isTopologicalRing_nrm_re_t2 <;> assumption)
