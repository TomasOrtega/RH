import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoefficientConvolutionHolds

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

/- English proof (translation)
The claim follows from `BoundedSectionAlgebra.siegelSpaceAlgebra_of moderateCoefficientPositivity_holds coefficientConvolution_holds`.
-/
theorem siegelSpaceAlgebra_holds : SiegelSpaceAlgebra (E := E) := BoundedSectionAlgebra.siegelSpaceAlgebra_of moderateCoefficientPositivity_holds coefficientConvolution_holds

end ReciprocityTheory.ChartRestriction.G.FD
