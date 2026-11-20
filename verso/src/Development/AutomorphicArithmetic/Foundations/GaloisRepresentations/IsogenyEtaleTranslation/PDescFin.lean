import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

namespace UpperTheory.Gal.FixZ

/- English proof (translation)
Introduce `A B C c f hc hs he hfin`. Establish `: UniversallyClosed f` using `UniversallyClosed.of_comp_surjective c f`. Establish `: IsProper f` using `{ }`. Establish `: LocallyQuasiFinite f` using `GlobalTheory.TangentCrit.locallyQuasiFinite_of_formallyUnramified f`. Conclude with `IsFinite.of_isProper_of_locallyQuasiFinite f`.
-/
theorem descFin_of : DescFin := by
  intro A B C c f hc hs he hfin
  have : UniversallyClosed f := UniversallyClosed.of_comp_surjective c f
  have : IsProper f := { }
  have : LocallyQuasiFinite f := GlobalTheory.TangentCrit.locallyQuasiFinite_of_formallyUnramified f
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end UpperTheory.Gal.FixZ
