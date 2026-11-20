import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionNormOneConjugate
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PlaneSA.ConjQ.conj_of_same_re` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FQuaternionNormOneConjugate.lean&line=103#L103)
-/
theorem _root_.GlobalTheory.T.quaternion_norm_one_conjugate : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F), (2 : K) ≠ 0 → d ≠ 0 → β ≠ 0 →
  ∀ x b : Q d β K, qn x = 1 → qn b = 1 → x.re = b.re → x.re ^ 2 ≠ 1 →
    ∃ y : (Q d β K)ˣ, (y : Q d β K) * x * ((y⁻¹ : (Q d β K)ˣ) : Q d β K) = b := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.ConjQ.conj_of_same_re | exact GlobalTheory.CompanionTheory.PlaneSA.ConjQ.conj_of_same_re | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.ConjQ.conj_of_same_re <;> assumption)
