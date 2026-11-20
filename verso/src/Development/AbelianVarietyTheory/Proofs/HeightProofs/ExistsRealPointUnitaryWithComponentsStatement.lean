import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealPointUnitaryWithComponents
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FExistsRealPointUnitaryWithComponents.lean&line=79#L79)
-/
theorem _root_.GlobalTheory.T.exists_real_point_unitary_with_components : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (V : HSp D) (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) → ∃ k ∈ GinfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) k = g τ := by
  first | exact @GlobalTheory.FockCompare.LiftUnitary.lift_unitary | exact GlobalTheory.FockCompare.LiftUnitary.lift_unitary | (intros; apply GlobalTheory.FockCompare.LiftUnitary.lift_unitary <;> assumption)
