import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FinitelyManyOpenSubgroupsBoundedIndex
import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.ContinuousCochains
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FFinitelyManyOpenSubgroupsBoundedIndex.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.finitely_many_open_subgroups_bounded_index : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))), (∀ N : ℕ, {E : IntermediateField F Ω | FiniteDimensional F E ∧ IsUnramifiedOutside S E ∧ Module.finrank F E ≤ N}.Finite) → ∀ N : ℕ, {H : Subgroup (galUnramifiedOutside F Ω S) | IsOpen (H : Set (galUnramifiedOutside F Ω S)) ∧ H.index ≠ 0 ∧ H.index ≤ N}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.GlobalFiniteness.openSubgroups_finite_of_fields_finite | exact GlobalTheory.CompanionTheory.GlobalFiniteness.openSubgroups_finite_of_fields_finite | (intros; apply GlobalTheory.CompanionTheory.GlobalFiniteness.openSubgroups_finite_of_fields_finite <;> assumption)
