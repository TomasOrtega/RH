import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotKernelIdealEqBeyondExponent
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Dieu.finrank_quot_kerIdeal_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinrankQuotKernelIdealEqBeyondExponent.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.finrank_quot_kernelIdeal_eq_beyond_exponent : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G Q : PDivGroup p k) (m n : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G), q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G → m ≤ n → Module.finrank k (G.A n ⧸ kerIdeal (q.app n)) = Module.finrank k (G.A m ⧸ kerIdeal (q.app m)) := by
  first | exact @GlobalTheory.Dieu.finrank_quot_kerIdeal_eq | exact GlobalTheory.Dieu.finrank_quot_kerIdeal_eq | (intros; apply GlobalTheory.Dieu.finrank_quot_kerIdeal_eq <;> assumption)
