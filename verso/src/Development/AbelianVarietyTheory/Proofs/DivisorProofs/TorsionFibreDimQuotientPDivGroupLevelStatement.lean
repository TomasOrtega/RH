import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFibreDimQuotientPDivGroupLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTorsionFibreDimQuotientPDivGroupLevel.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.torsion_fibreDim_quotient_pDivGroupLevel : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (k m : ℕ), 1 ≤ k → ∀ (B : Type) [CommRing B] [HopfAlgebra O B] [IsCocomm O B] [Module.Finite O B] [Module.Projective O B] (j : B →ₐc[O] G.A (k + m)) (ρ : G.A (k + m) →ₗ[O] B), (∀ b, ρ (j b) = b) → torsionIdeal O (G.A (k + m)) p ≤ kerIdeal j → ∀ q : PrimeSpectrum O, fibreDim (B ⧸ torsionIdeal O B (p ^ m)) q = p ^ (m * G.height) := by
  first | exact @GlobalTheory.TorsDim.fibreDim_quot_torsionIdeal | exact GlobalTheory.TorsDim.fibreDim_quot_torsionIdeal | (intros; apply GlobalTheory.TorsDim.fibreDim_quot_torsionIdeal <;> assumption)
