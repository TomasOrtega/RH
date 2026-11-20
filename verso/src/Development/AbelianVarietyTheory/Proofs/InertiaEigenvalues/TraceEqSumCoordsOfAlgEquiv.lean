import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem trace_pi_fin_self {F : Type} [Field F] (r : ℕ) (x : Fin r → F) :
    Algebra.trace F (Fin r → F) x = ∑ i, x i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun F (Fin r)), Matrix.trace]
  congr 1
  ext i
  simp [Algebra.leftMulMatrix_eq_repr_mul, Pi.basisFun_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem trace_eq_sum_coords_of_algEquiv {F K : Type} [Field F] [CommRing K] [Algebra F K] (r : ℕ)
    (e : K ≃ₐ[F] (Fin r → F)) (k : K) : Algebra.trace F K k = ∑ i, e k i := by
  rw [← Algebra.trace_eq_of_algEquiv e k, trace_pi_fin_self]

end GlobalTheory
