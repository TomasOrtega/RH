import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ShortVectorBoundOfCoefficientBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ShortVectorSixthLemmaPrimeHolds

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem shortVectorBound : ShortVectorBound (E := E) :=
  shortVectorBound_of_coefficient_bounds fourier_coefficients_holds cusp_coefficient_quantitative_holds flowCoefficientDecay coefficientIndex_lowerBound coefficientHeight_bound counting_exponential_sum_holds isotropic_outside_line

end ReciprocityTheory.ChartRestriction.G.FD
