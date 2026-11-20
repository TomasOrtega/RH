import Development.EtaleCohomology.WeilConjectures.FermatCount
import Development.EtaleCohomology.KummerTheory.AdicLimPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.FinQCut

/- English proof (translation)
Introduce and unpack `U ⟨x⟩`. Establish `f : U ⟶ X` using `x`. Establish `h` using `hq.map (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (f ≫ p).appTop).hom)`. Rewrite `h` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem inv_of_over {q : ℕ} {A : Type} [CommRing A] (hq : IsUnit (q : A)) {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of A)) : Inv q (sch.obj X) := by
  rintro U ⟨x⟩
  have f : U ⟶ X := x
  have h := hq.map (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (f ≫ p).appTop).hom)
  rwa [map_natCast] at h

end LateralTheory.EWeil.FinQCut

end
