import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedUnipotentRadicalStabilizer
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.QKAvg.isClosed_radN` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIsClosedUnipotentRadicalStabilizer.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.isClosed_unipotent_radical_stabilizer : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t), IsClosed (radN d : Set (GlobalTheory.RegSW.stab d)) := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.isClosed_radN | exact GlobalTheory.CompanionTheory.QKAvg.isClosed_radN | (intros; apply GlobalTheory.CompanionTheory.QKAvg.isClosed_radN <;> assumption)
