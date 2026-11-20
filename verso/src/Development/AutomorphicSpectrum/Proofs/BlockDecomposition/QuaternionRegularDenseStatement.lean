import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionRegularDense
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FQuaternionRegularDense.lean&line=132#L132)
-/
theorem _root_.GlobalTheory.T.quaternion_regular_dense : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalDivisionRing K] (d β : F),
  (2 : K) ≠ 0 → d ≠ 0 → β ≠ 0 → (𝓝[≠] (0 : K)).NeBot →
  ∀ a : Q d β K, qn a = 1 → ∀ U ∈ 𝓝 a, ∃ b ∈ U, qn b = 1 ∧ b.re ^ 2 ≠ 1 := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.RegDense.regular_dense | exact GlobalTheory.CompanionTheory.PlaneSA.RegDense.regular_dense | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.RegDense.regular_dense <;> assumption)
