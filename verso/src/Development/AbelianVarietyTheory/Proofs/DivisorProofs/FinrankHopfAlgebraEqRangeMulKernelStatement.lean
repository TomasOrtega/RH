import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHopfAlgebraEqRangeMulKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinrankHopfAlgebraEqRangeMulKernel.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.finrank_hopfAlgebra_eq_range_mul_kernel : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A] [IsCocomm k A] [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (f : C →ₐc[k] A), Module.finrank k A = Module.finrank k (LinearMap.range (f : C →ₐ[k] A).toLinearMap) * Module.finrank k (A ⧸ kerIdeal f) := by
  first | exact @GlobalTheory.Dieu.finrank_eq_range_mul_ker | exact GlobalTheory.Dieu.finrank_eq_range_mul_ker | (intros; apply GlobalTheory.Dieu.finrank_eq_range_mul_ker <;> assumption)
