import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumCharacterOrthogonalityMatrices
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSumCharacterOrthogonalityMatrices.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.sum_character_orthogonality_matrices : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (ψ₀ : AddChar k ℂ), ψ₀ ≠ 1 → ∀ β T : Matrix (Fin n) (Fin n) k, T ≠ β → ∑ Y : Matrix (Fin n) (Fin n) k, coY ψ₀ β Y * ψ₀ (Matrix.trace (Y * T)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Jp.coY_sum_mul_eq_zero | exact GlobalTheory.CompanionTheory.Jp.coY_sum_mul_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Jp.coY_sum_mul_eq_zero <;> assumption)
