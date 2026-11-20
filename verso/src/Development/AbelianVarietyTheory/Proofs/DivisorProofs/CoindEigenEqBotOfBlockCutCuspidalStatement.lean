import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoindEigenEqBotOfBlockCutCuspidal
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoindEigenEqBotOfBlockCutCuspidal.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.coindEigen_eq_bot_of_block_cut_cuspidal : ∀ (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ (j : ℕ) (w : Equiv.Perm (Fin r)) (x : GL (Fin r) F), (∀ (g : GL (Fin r) F) (a c : Fin r), ((x⁻¹ * g * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a c = (g : Matrix (Fin r) (Fin r) F) (w a) (w c)) → ∀ a c : Fin r, a.val < j → j ≤ c.val → b (w a) = b (w c) → eig σ {p | x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r} (fun p => ψ (edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x))) = ⊥ := by
  first | exact @GlobalTheory.FinGL.MackeyCut.eig_eq_bot_of_cut | exact GlobalTheory.FinGL.MackeyCut.eig_eq_bot_of_cut | (intros; apply GlobalTheory.FinGL.MackeyCut.eig_eq_bot_of_cut <;> assumption)
