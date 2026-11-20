import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameBlockZeroStabilizesFlag
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumFrameIdem
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RapidDecay.stabilises_flag_span` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFrameBlockZeroStabilizesFlag.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.frame_block_zero_stabilizes_flag : ∀ (E : Type) [Field E] (S : E →+* E) (n r : ℕ) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E), cT S Y * J * X = 1 → ∀ (g : Matrix (Fin n) (Fin n) E) (j : Fin r), (∀ α β : FrameIx r, frameLev j α < 2 → frameLev j β = 2 → frameIdem S J X Y α * g * frameIdem S J X Y β = 0) → ∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, g *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.stabilises_flag_span | exact GlobalTheory.CompanionTheory.RapidDecay.stabilises_flag_span | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.stabilises_flag_span <;> assumption)
