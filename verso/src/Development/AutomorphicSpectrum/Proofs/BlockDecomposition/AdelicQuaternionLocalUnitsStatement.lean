import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicQuaternionLocalUnits
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PlaneSA.LocalUnit.exists_adelic_unit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAdelicQuaternionLocalUnits.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.adelic_quaternion_local_units : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (T : Finset (Pl F)) (y : (u : Pl F) → (Q d β (Kp u))ˣ),
  ∃ Y : (Q d β (AF F))ˣ, (∀ u ∈ T, qmap (proj u) (Y : Q d β (AF F)) = y u) ∧
    ∀ u, u ∉ T → qmap (proj u) (Y : Q d β (AF F)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.LocalUnit.exists_adelic_unit | exact GlobalTheory.CompanionTheory.PlaneSA.LocalUnit.exists_adelic_unit | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.LocalUnit.exists_adelic_unit <;> assumption)
