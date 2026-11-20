import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingIffPreservesSubgroupOrbit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.orbit_stab_cut_finite` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsFinsetFixingIffPreservesSubgroupOrbit.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_finset_fixing_iff_preserves_subgroup_orbit : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (H : Subgroup (G E Ω)) (y : Ω), ∃ s : Finset Ω, ∀ σ : G E Ω, (∀ x ∈ s, σ x = x) ↔ ∀ τ ∈ H, ∃ τ' ∈ H, σ (τ y) = τ' y := by
  first | exact @GlobalTheory.orbit_stab_cut_finite | exact GlobalTheory.orbit_stab_cut_finite | (intros; apply GlobalTheory.orbit_stab_cut_finite <;> assumption)
