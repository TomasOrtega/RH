import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlanePropOfAllStrongApprox
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPlanePropOfAllStrongApprox.lean&line=138#L138)
-/
theorem _root_.GlobalTheory.T.plane_prop_of_all_strong_approx : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ β : F, β ≠ 0 → HermitianPlaneStrongApprox σ β) → Sa2.PropPlane := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.OfTwo.plane_prop_of_strong_approx | exact GlobalTheory.CompanionTheory.PlaneSA.OfTwo.plane_prop_of_strong_approx | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.OfTwo.plane_prop_of_strong_approx <;> assumption)
