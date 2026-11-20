import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussLemmaSymPowMatrixUpperTriangularPlaceOrder
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAtOfNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NrmCoeffProdLinearStatement

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Nef.ordVec_symMat_mulVec_triangular` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGaussLemmaSymPowMatrixUpperTriangularPlaceOrder.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.gaussLemma_symPowMatrix_upperTriangular_placeOrder : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (P : Place k E) (m : ℕ) (A : Matrix (Fin 2) (Fin 2) E), A 1 0 = 0 → A.det ≠ 0 → ∀ (q : Fin (m + 1) → E) (c : E) (s t : Fin m → E), c ≠ 0 → (∀ j, ![s j, t j] ≠ 0) → ∑ i : Fin (m + 1), C (q i) * (C (A 0 1) + C (A 1 1) * X) ^ (i : ℕ) * C (A 0 0) ^ (m - i) = C c * ∏ j, (C (s j) * C (A 0 0) + C (t j) * (C (A 0 1) + C (A 1 1) * X)) → ordVec P ((symMat m A).mulVec q) = ord P c + ∑ j, ordVec P (A.mulVec ![s j, t j]) := by
  first | exact @GlobalTheory.Nef.ordVec_symMat_mulVec_triangular | exact GlobalTheory.Nef.ordVec_symMat_mulVec_triangular | (intros; apply GlobalTheory.Nef.ordVec_symMat_mulVec_triangular <;> assumption)
