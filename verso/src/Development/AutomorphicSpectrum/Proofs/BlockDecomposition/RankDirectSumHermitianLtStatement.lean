import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankDirectSumHermitianLt
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanTransport
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PcFc.rank_dsum_ge` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRankDirectSumHermitianLt.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.rank_direct_sum_hermitian_lt : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (b₀ : HermE D ρ), b₀.1.det ≠ 0 → ∀ β' : HermE D p, β'.1 ≠ 0 → ρ + 1 ≤ (dsum hn b₀ β').1.rank := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.rank_dsum_ge | exact GlobalTheory.CompanionTheory.PcFc.rank_dsum_ge | (intros; apply GlobalTheory.CompanionTheory.PcFc.rank_dsum_ge <;> assumption)
