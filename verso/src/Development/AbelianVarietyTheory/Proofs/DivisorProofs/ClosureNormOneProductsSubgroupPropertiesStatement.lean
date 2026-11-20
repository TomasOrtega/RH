import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureNormOneProductsSubgroupProperties
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FClosureNormOneProductsSubgroupProperties.lean&line=169#L169)
-/
theorem _root_.GlobalTheory.T.closure_normOneProducts_h0_properties : ∀ (F : Type) [Field F] [NumberField F] (a b : F) (ε : AF F), ε * ε = ε → (∀ x ∈ closure (H0 (a := a) (b := b) ε), ∀ y ∈ closure (H0 (a := a) (b := b) ε), x * y ∈ closure (H0 (a := a) (b := b) ε)) ∧ (∀ x ∈ closure (H0 (a := a) (b := b) ε), star x ∈ closure (H0 (a := a) (b := b) ε)) ∧ (∀ δ δ' : ℍ[F, a, b], δ * δ' = 1 → ∀ x ∈ closure (H0 (a := a) (b := b) ε), rat δ * x * rat δ' ∈ closure (H0 (a := a) (b := b) ε)) ∧ (∀ x ∈ closure (H0 (a := a) (b := b) ε), nrm x = 1) := by
  first | exact @GlobalTheory.QSA.Grp.closure_normOneProducts_subgroup_properties | exact GlobalTheory.QSA.Grp.closure_normOneProducts_subgroup_properties | (intros; apply GlobalTheory.QSA.Grp.closure_normOneProducts_subgroup_properties <;> assumption)
