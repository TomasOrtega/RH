import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionClassNumberFinite
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PlaneSA.Compact.exists_isCompact_units` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FQuaternionClassNumberFinite.lean&line=129#L129)
-/
theorem _root_.GlobalTheory.T.quaternion_class_number_finite : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∃ C : Set (Q d β (AF F))ˣ, IsCompact C ∧ ∀ y : (Q d β (AF F))ˣ, ∃ c ∈ C, ∃ δ : (Q d β F)ˣ, ∃ z : (AF F)ˣ,
    y = c * Units.map (rat (R := AF F) : Q d β F →+* Q d β (AF F)).toMonoidHom δ *
      Units.map (algebraMap (AF F) (Q d β (AF F))).toMonoidHom z := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.Compact.exists_isCompact_units | exact GlobalTheory.CompanionTheory.PlaneSA.Compact.exists_isCompact_units | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.Compact.exists_isCompact_units <;> assumption)
