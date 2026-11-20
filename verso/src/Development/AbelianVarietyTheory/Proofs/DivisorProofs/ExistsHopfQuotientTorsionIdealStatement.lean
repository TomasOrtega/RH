import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHopfQuotientTorsionIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDiv.exists_hopf_quotient_torsionIdeal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsHopfQuotientTorsionIdeal.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_hopf_quotient_ker_eq_torsionIdeal : ∀ (O : Type) [CommRing O] (B : Type) [CommRing B] [HopfAlgebra O B] [IsCocomm O B] (n : ℕ), ∃ (D : Type) (_ : CommRing D) (_ : HopfAlgebra O D) (_ : IsCocomm O D) (π : B →ₐc[O] D), Function.Surjective π ∧ RingHom.ker π = torsionIdeal O B n := by
  first | exact @GlobalTheory.PDiv.exists_hopf_quotient_torsionIdeal | exact GlobalTheory.PDiv.exists_hopf_quotient_torsionIdeal | (intros; apply GlobalTheory.PDiv.exists_hopf_quotient_torsionIdeal <;> assumption)
