import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPowFibreRankEqPDivGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDivGroup.exists_mulPow_fibreRank_eq` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsMulPowFibreRankEqPDivGroup.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_mulPow_fibreRank_eq_pDivGroup : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (k m : ℕ), ∃ (r : G.A (k + m) →ₐc[O] G.A k) (μ : G.A k →ₐc[O] G.A (k + m)), Function.Surjective r ∧ RingHom.ker r = torsionIdeal O (G.A (k + m)) (p ^ k) ∧ (∀ a, μ (r a) = mulBy O (G.A (k + m)) (p ^ m) a) ∧ ∀ q, fibreRank (μ : G.A k →ₐ[O] G.A (k + m)).toLinearMap q = fibreDim (G.A k) q := by
  first | exact @GlobalTheory.PDivGroup.exists_mulPow_fibreRank_eq | exact GlobalTheory.PDivGroup.exists_mulPow_fibreRank_eq | (intros; apply GlobalTheory.PDivGroup.exists_mulPow_fibreRank_eq <;> assumption)
