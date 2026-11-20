import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilradicalAdjointExpStable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNilradicalAdjointExpStable.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.nilradical_adjoint_exp_stable : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Jᴴ = J → IsUnit J.det → ∀ (x : Fin n → ℂ) (Y : Matrix (Fin n) (Fin n) ℂ), Y ∈ nilRad J x → J⁻¹ * Yᴴ * J ∈ nilRad J x ∧ NormedSpace.exp Y - 1 ∈ nilRad J x := by
  first | exact @GlobalTheory.TorFin.NilAdj.nilRad_adj_exp | exact GlobalTheory.TorFin.NilAdj.nilRad_adj_exp | (intros; apply GlobalTheory.TorFin.NilAdj.nilRad_adj_exp <;> assumption)
