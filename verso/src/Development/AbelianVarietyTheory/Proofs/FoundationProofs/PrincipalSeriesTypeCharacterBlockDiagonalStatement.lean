import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterBlockDiagonal
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PsType.theta_emb₂_std` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FPrincipalSeriesTypeCharacterBlockDiagonal.lean&line=202#L202)
-/
theorem _root_.GlobalTheory.T.principalSeriesTypeCharacter_blockDiagonal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp (fun i => ψ (Fin.castAdd t i)), ∀ b ∈ grp (fun i => ψ (Fin.natAdd r i)), theta ψ (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) = theta (fun i => ψ (Fin.castAdd t i)) a * theta (fun i => ψ (Fin.natAdd r i)) b := by
  first | exact @GlobalTheory.PsType.theta_emb₂_std | exact GlobalTheory.PsType.theta_emb₂_std | (intros; apply GlobalTheory.PsType.theta_emb₂_std <;> assumption)
