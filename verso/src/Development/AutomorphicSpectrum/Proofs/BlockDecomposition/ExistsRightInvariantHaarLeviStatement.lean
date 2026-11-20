import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightInvariantHaarLevi
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsRightInvariantHaarLevi.lean&line=111#L111)
-/
theorem _root_.GlobalTheory.T.exists_right_invariant_haar_levi : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (levM d)], ∃ νM : Measure (levM d), νM.IsHaarMeasure ∧ νM.IsMulRightInvariant := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.exists_levM_haar | exact GlobalTheory.CompanionTheory.QKAvg.exists_levM_haar | (intros; apply GlobalTheory.CompanionTheory.QKAvg.exists_levM_haar <;> assumption)
