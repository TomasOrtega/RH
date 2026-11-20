import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermFrameKTypeCoefficients
import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.ContinuousCochains
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsDiscreteRepResMuROrep
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global FiniteSubfield ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.CompanionTheory.GSCd GroundTheory.Global.IdeleGroup GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped DirectSum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FConstantTermFrameKTypeCoefficients.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.cohomological_dimension_topological_iso : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (p : ℕ), (G ≃ₜ* H) → cdp p G = cdp p H := by
  first | exact @GlobalTheory.CompanionTheory.GSCd.cdp_eq_of_continuousMulEquiv | exact GlobalTheory.CompanionTheory.GSCd.cdp_eq_of_continuousMulEquiv | (intros; apply GlobalTheory.CompanionTheory.GSCd.cdp_eq_of_continuousMulEquiv <;> assumption)
