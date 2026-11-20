import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSquareRootsNearOne
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalSquareRootsNearOne.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.local_square_roots_near_one : ∀ {F : Type} [Field F] [NumberField F] (u : Pl F), ∀ V ∈ 𝓝 (1 : Kp u), ∀ᶠ x in 𝓝 (1 : Kp u), ∃ μ ∈ V, μ ^ 2 = x := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.sq_fills_nhds_one | exact GlobalTheory.CompanionTheory.PlaneSA.sq_fills_nhds_one | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.sq_fills_nhds_one <;> assumption)
