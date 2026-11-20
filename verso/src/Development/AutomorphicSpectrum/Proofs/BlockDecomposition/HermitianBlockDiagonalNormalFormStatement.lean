import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDiagonalNormalForm
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanTransport
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PcFc.exists_cg_dsum` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHermitianBlockDiagonalNormalForm.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.hermitian_block_diagonal_normal_form : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (β : HermE D n), ρ ≤ β.1.rank → ∃ (a : GL (Fin n) D.host.E) (b₀ : HermE D ρ) (β' : HermE D p), IsDiagInv b₀ ∧ cg a β = dsum hn b₀ β' := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.exists_cg_dsum | exact GlobalTheory.CompanionTheory.PcFc.exists_cg_dsum | (intros; apply GlobalTheory.CompanionTheory.PcFc.exists_cg_dsum <;> assumption)
