import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneStrongApproxGenerator
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPlaneStrongApproxGenerator.lean&line=239#L239)
-/
theorem _root_.GlobalTheory.T.plane_strong_approx_generator : Sa2.PropGen := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.propGen | exact GlobalTheory.CompanionTheory.SaGen.propGen | (intros; apply GlobalTheory.CompanionTheory.SaGen.propGen <;> assumption)
