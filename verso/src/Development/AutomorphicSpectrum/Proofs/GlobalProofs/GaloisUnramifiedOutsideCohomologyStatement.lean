import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GaloisUnramifiedOutsideCohomology
import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.ContinuousCochains
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FGaloisUnramifiedOutsideCohomology.lean&line=190#L190)
-/
theorem _root_.GlobalTheory.T.galois_unramified_outside_cohomology : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))), (maxUnramifiedOutside F Ω S).fixingSubgroup ≤ NS Ω S := by
  first | exact @GlobalTheory.CompanionTheory.Glob.InertiaLift.fixingSubgroup_le_NS | exact GlobalTheory.CompanionTheory.Glob.InertiaLift.fixingSubgroup_le_NS | (intros; apply GlobalTheory.CompanionTheory.Glob.InertiaLift.fixingSubgroup_le_NS <;> assumption)
