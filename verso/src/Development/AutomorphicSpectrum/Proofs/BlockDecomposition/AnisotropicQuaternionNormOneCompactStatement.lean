import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropicQuaternionNormOneCompact
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PlaneSA.isCompact_qn_eq_one_at_place` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAnisotropicQuaternionNormOneCompact.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.anisotropic_quaternion_norm_one_compact : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (s : Pl F), (∀ x : Q d β (Kp s), qn x = 0 → x = 0) → IsCompact {x : Q d β (Kp s) | qn x = 1} := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.isCompact_qn_eq_one_at_place | exact GlobalTheory.CompanionTheory.PlaneSA.isCompact_qn_eq_one_at_place | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.isCompact_qn_eq_one_at_place <;> assumption)
