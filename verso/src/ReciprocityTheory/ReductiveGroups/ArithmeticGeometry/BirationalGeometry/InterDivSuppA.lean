import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAB

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

/- English proof (translation)
Use `haveI : IsJacobsonRing ℤ := int_isJacobsonRing`. Use `haveI := DimF.finiteRingKrullDim_mvPolynomialInt_quot P`. Use `haveI : (Q.map (Ideal.Quotient.mk P)).IsPrime := DimF.isPrime_map_mk h`. Establish `key` using `DimF.dim_quot_add_height (A := MvPolynomial σ ℤ ⧸ P) (DimF.height_eq_of_isMaximal_int P) (Q.map (Ideal.Quotient.mk P))`. Rewrite using `[← key, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE h)]`.
-/
theorem mvPolynomialInt_dimFormula {σ : Type*} [Finite σ] (P Q : Ideal (MvPolynomial σ ℤ))
    [P.IsPrime] [Q.IsPrime] (h : P ≤ Q) :
    ringKrullDim (MvPolynomial σ ℤ ⧸ Q) + ((Q.map (Ideal.Quotient.mk P)).height : WithBot ℕ∞) =
      ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by

  haveI : IsJacobsonRing ℤ := int_isJacobsonRing
  haveI := DimF.finiteRingKrullDim_mvPolynomialInt_quot P
  haveI : (Q.map (Ideal.Quotient.mk P)).IsPrime := DimF.isPrime_map_mk h
  have key := DimF.dim_quot_add_height (A := MvPolynomial σ ℤ ⧸ P)
    (DimF.height_eq_of_isMaximal_int P) (Q.map (Ideal.Quotient.mk P))

  rw [← key, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE h)]

end ReciprocityTheory.ChartRestriction.G.Geo
