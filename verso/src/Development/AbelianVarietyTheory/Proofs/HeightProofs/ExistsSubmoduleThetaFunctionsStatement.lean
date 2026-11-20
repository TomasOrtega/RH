import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSubmoduleThetaFunctions
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FockCompare.exists_thetaSubmodule` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FExistsSubmoduleThetaFunctions.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.exists_submodule_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D), ∃ M : Submodule ℂ (WA V W → ℂ), ∀ f, f ∈ M ↔ IsThetaFun ψ V W f := by
  first | exact @GlobalTheory.FockCompare.exists_thetaSubmodule | exact GlobalTheory.FockCompare.exists_thetaSubmodule | (intros; apply GlobalTheory.FockCompare.exists_thetaSubmodule <;> assumption)
