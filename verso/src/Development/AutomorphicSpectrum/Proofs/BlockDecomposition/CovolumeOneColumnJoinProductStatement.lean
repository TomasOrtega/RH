import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneColumnJoinProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColJoinColLColR
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCovolumeOneColumnJoinProduct.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.covolume_one_column_join_product : ∀ (D : D7) (m r s : ℕ) (μr : Measure (Mx D m r)) (𝓕r : Set (Mx D m r)) (μs : Measure (Mx D m s))
    (𝓕s : Set (Mx D m s)), IsCovolOne (ratMx D m r) μr 𝓕r → IsCovolOne (ratMx D m s) μs 𝓕s →
    IsCovolOne (ratMx D m (r + s)) ((μr.prod μs).map fun z => colJoin z.1 z.2)
      ((fun z : Mx D m r × Mx D m s => colJoin z.1 z.2) '' (𝓕r ×ˢ 𝓕s)) := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.ProdCovol.isCovolOne_colJoin | exact GlobalTheory.CompanionTheory.EisUnfold.ProdCovol.isCovolOne_colJoin | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.ProdCovol.isCovolOne_colJoin <;> assumption)
