import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseConjMemClosureOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_inverse_conj_mem_closure_of_isCompact` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsInverseConjMemClosureOfIsCompact.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_conj_mem_closure_of_isCompact : ∀ (X : Type) [Monoid X] [TopologicalSpace X] [ContinuousMul X] [T2Space X] (H C : Set X), IsCompact C → ∀ g : X, (∀ W ∈ 𝓝 g, ∃ c ∈ C, ∃ c' ∈ C, c * c' = 1 ∧ c' * c = 1 ∧ ∃ w ∈ W, c * w * c' ∈ H) → ∃ c ∈ C, ∃ c' ∈ C, c * c' = 1 ∧ c' * c = 1 ∧ c * g * c' ∈ closure H := by
  first | exact @GlobalTheory.exists_inverse_conj_mem_closure_of_isCompact | exact GlobalTheory.exists_inverse_conj_mem_closure_of_isCompact | (intros; apply GlobalTheory.exists_inverse_conj_mem_closure_of_isCompact <;> assumption)
