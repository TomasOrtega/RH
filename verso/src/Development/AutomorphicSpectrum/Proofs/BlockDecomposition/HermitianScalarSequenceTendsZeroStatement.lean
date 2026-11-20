import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianScalarSequenceTendsZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHermitianScalarSequenceTendsZero.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.hermitian_scalar_sequence_tends_zero : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ r : ℕ, ∃ e : ℕ → Mx D r r, (∀ n, e n ∈ hermA D r) ∧ Filter.Tendsto e Filter.atTop (nhds 0) ∧ ∀ (n : ℕ) (ρ : D.what₂.Tau), compAt θ ρ (e n) = (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path.exists_herm_seq | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path.exists_herm_seq | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path.exists_herm_seq <;> assumption)
