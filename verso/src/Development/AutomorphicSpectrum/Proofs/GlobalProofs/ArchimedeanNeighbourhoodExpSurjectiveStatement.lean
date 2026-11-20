import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanNeighbourhoodExpSurjective
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IoInjective
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SkewOfCommute
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.HCCusp.RealLog.exists_small_log` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FArchimedeanNeighbourhoodExpSurjective.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.archimedean_neighbourhood_exp_surjective : ∀ (D : D7) (θ : GlobalTheory.Mem.Th.InfF D), IsInfFam θ → ∀ (V : HSp D) (δ : ℝ), 0 < δ → ∃ N ∈ 𝓝 (1 : GA D V), ∀ r ∈ N, r ∈ GinfC V → ∃ X : GlobalTheory.SmoothForms.LieN V, ‖X‖ < δ ∧ GlobalTheory.SmoothForms.expInf θ V X = r := by
  first | exact @GlobalTheory.CompanionTheory.HCCusp.RealLog.exists_small_log | exact GlobalTheory.CompanionTheory.HCCusp.RealLog.exists_small_log | (intros; apply GlobalTheory.CompanionTheory.HCCusp.RealLog.exists_small_log <;> assumption)
