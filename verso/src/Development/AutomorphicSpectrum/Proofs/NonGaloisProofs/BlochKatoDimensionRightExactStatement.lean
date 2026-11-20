import Mathlib
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.BlochKatoDimensionRightExact
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BKDim.bkADim_and_bkARightExact` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FNonGaloisProofs%2FBlochKatoDimensionRightExact.lean&line=645#L645)
-/
theorem _root_.GlobalTheory.T.blochKato_dimension_rightExact : ∀ D : D7, LocalSituation.adm5 D → LocalSituation.adm6 D → LocalSituation.adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), LocalSituation.bkADim ((D.loc l).PD K) ∧ LocalSituation.bkARightExact ((D.loc l).PD K) := by
  first | exact @GlobalTheory.CompanionTheory.BKDim.bkADim_and_bkARightExact | exact GlobalTheory.CompanionTheory.BKDim.bkADim_and_bkARightExact | (intros; apply GlobalTheory.CompanionTheory.BKDim.bkADim_and_bkARightExact <;> assumption)
