import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularCharacterAdelicGLEqOne
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

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FModularCharacterAdelicGLEqOne.lean&line=365#L365)
-/
theorem _root_.GlobalTheory.T.modularCharacter_adelic_GL_eq_one : ∀ (D : D7) (r : ℕ) [LocallyCompactSpace (GL (Fin r) (AE D))] (a : GL (Fin r) (AE D)), Measure.modularCharacterFun a = 1 := by
  first | exact @GlobalTheory.CompanionTheory.GLUnimod.modularCharacterFun_GL_adele | exact GlobalTheory.CompanionTheory.GLUnimod.modularCharacterFun_GL_adele | (intros; apply GlobalTheory.CompanionTheory.GLUnimod.modularCharacterFun_GL_adele <;> assumption)
