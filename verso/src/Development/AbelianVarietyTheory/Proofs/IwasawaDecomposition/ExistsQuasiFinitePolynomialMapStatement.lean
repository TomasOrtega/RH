import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsQuasiFinitePolynomialMap
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_algebraicIndependent_int_quasiFiniteAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsQuasiFinitePolynomialMap.lean&line=406#L406)
-/
theorem _root_.GlobalTheory.T.exists_quasi_finite_polynomial_map : ∀ (S : Type) [CommRing S] [IsDomain S] [CharZero S] [Algebra.FiniteType ℤ S] (𝔮 : Ideal S) [𝔮.IsPrime], ∃ (r : ℕ) (y : Fin r → S), AlgebraicIndependent ℤ y ∧ @Algebra.QuasiFiniteAt (MvPolynomial (Fin r) ℤ) S _ _ (MvPolynomial.aeval y : MvPolynomial (Fin r) ℤ →ₐ[ℤ] S).toRingHom.toAlgebra 𝔮 _ := by
  first | exact @GlobalTheory.exists_algebraicIndependent_int_quasiFiniteAt | exact GlobalTheory.exists_algebraicIndependent_int_quasiFiniteAt | (intros; apply GlobalTheory.exists_algebraicIndependent_int_quasiFiniteAt <;> assumption)
