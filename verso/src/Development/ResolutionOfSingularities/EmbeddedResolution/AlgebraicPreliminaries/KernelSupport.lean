import Mathlib

namespace FunctorialResolution.EmbeddedResolution

open CategoryTheory AlgebraicGeometry

/- English proof (authored)
A section killed by pullback along f remains zero after further pullback along g. Thus the kernel ideal of f is contained in the kernel ideal of the composite. Larger ideals have smaller vanishing supports, giving the claimed containment.
-/
theorem support_ker_comp_subset_support_ker {T S Y : Scheme}
    (g : T ⟶ S) (f : S ⟶ Y) :
    ((g ≫ f).ker.support : Set Y) ⊆ (f.ker.support : Set Y) := by
  intro x hx
  exact Scheme.IdealSheafData.support_antitone (Scheme.Hom.le_ker_comp g f) hx

end FunctorialResolution.EmbeddedResolution
