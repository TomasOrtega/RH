import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.LamMZero

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem restLam_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) (hDeg : RestLamDeg C₀) : RestLam C₀ :=
  restLam_of_rests C₀ (restLamA_of D hAdm) (restLamInj C₀) hDeg

end Formalism.MainNotions.SelectionLemmas.Pf
