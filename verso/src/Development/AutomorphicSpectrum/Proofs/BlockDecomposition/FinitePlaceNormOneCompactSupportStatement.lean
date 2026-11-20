import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePlaceNormOneCompactSupport
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFinitePlaceNormOneCompactSupport.lean&line=101#L101)
-/
theorem _root_.GlobalTheory.T.finite_place_norm_one_compact_support : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (S : Finset (Pl F)), (∀ s ∈ S, IsCompact {x : Q d β (Kp s) | qn x = 1}) → IsCompact (SuppAt d β (S : Set (Pl F))) := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.CptAdelic.isCompact_suppAt | exact GlobalTheory.CompanionTheory.PlaneSA.CptAdelic.isCompact_suppAt | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.CptAdelic.isCompact_suppAt <;> assumption)
