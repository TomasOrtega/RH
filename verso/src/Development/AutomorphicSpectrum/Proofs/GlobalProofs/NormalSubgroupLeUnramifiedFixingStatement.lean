import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NormalSubgroupLeUnramifiedFixing
import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.ContinuousCochains
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GlobalFiniteness.NS_le_fixingSubgroup` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FNormalSubgroupLeUnramifiedFixing.lean&line=93#L93)
-/
theorem _root_.GlobalTheory.T.normal_subgroup_le_unramified_fixing : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))), NS Ω S ≤ (maxUnramifiedOutside F Ω S).fixingSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.GlobalFiniteness.NS_le_fixingSubgroup | exact GlobalTheory.CompanionTheory.GlobalFiniteness.NS_le_fixingSubgroup | (intros; apply GlobalTheory.CompanionTheory.GlobalFiniteness.NS_le_fixingSubgroup <;> assumption)
