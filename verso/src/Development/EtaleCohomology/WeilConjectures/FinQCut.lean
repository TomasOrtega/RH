import Development.EtaleCohomology.WeilConjectures.FermatCount
import Development.EtaleCohomology.KummerTheory.AdicLimPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.FinQCut

/- English proof (translation)
Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem inv_of_over {q : ℕ} {A : Type} [CommRing A] (hq : IsUnit (q : A)) {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of A)) : Inv q (sch.obj X) := by
  rintro U ⟨x⟩
  have f : U ⟶ X := x
  have h := hq.map (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (f ≫ p).appTop).hom)
  rwa [map_natCast] at h

end LateralTheory.EWeil.FinQCut

end
