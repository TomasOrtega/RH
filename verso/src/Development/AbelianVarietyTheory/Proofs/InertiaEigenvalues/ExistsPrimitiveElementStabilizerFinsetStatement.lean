import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveElementStabilizerFinset
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.stab_finset_eq_stab_primitive` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsPrimitiveElementStabilizerFinset.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.exists_primitive_element_stabilizer_finset : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (s : Finset Ω), ∃ β : Ω, ∀ σ : G E Ω, σ β = β ↔ ∀ x ∈ s, σ x = x := by
  first | exact @GlobalTheory.stab_finset_eq_stab_primitive | exact GlobalTheory.stab_finset_eq_stab_primitive | (intros; apply GlobalTheory.stab_finset_eq_stab_primitive <;> assumption)
