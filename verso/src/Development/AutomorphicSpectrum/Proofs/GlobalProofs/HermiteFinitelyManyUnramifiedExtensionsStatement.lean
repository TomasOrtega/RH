import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermiteFinitelyManyUnramifiedExtensions
import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.ContinuousCochains
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FHermiteFinitelyManyUnramifiedExtensions.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.hermite_finitely_many_unramified_extensions : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) (N : ℕ), {E : IntermediateField F Ω | FiniteDimensional F E ∧ IsUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) E ∧ Module.finrank F E ≤ N}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree | exact GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree | (intros; apply GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree <;> assumption)
