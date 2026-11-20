import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.DecIdentity
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ProjectionMemPartialSpan
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ImportsAlt
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembAlgF
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDegF
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembLabF

noncomputable section

namespace Formalism.MainNotions.Proposition5Numerics

/- English proof (translation)
The claim follows from `restDecG_of atl valSlice valComp hVB hXX hDd`.
-/
theorem decomposition_of_three_parts (hVB : RestValBdG) (hXX : RestXXG) (hDd : RestDdG) : RestDecG :=
  restDecG_of atl valSlice valComp hVB hXX hDd

/- English proof (translation)
The claim follows from `membership_of_four_parts (decomposition_of_three_parts hVB hXX hDd) restAlgG restDegG restLabG D CLa Ck Crk Cdeg`.
-/
theorem membership_of_three_parts (hVB : RestValBdG) (hXX : RestXXG) (hDd : RestDdG) (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) :
    RestMemb D CLa Ck Crk Cdeg :=
  membership_of_four_parts (decomposition_of_three_parts hVB hXX hDd) restAlgG restDegG restLabG D CLa Ck Crk Cdeg

end Formalism.MainNotions.Proposition5Numerics
