import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber

noncomputable section

namespace GlobalTheory.AbHomDesc

variable {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (π : R →+* R₀)

def iota (hI : RingHom.ker π = I) (S : Subring R) : S ⧸ I.comap S.subtype →+* R₀ :=
  Ideal.Quotient.lift _ (π.comp S.subtype) fun x hx => by
    have h : (x : R) ∈ I := hx
    rw [← hI] at h
    exact h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iota_comp_mk (hI : RingHom.ker π = I) (S : Subring R) :
    (iota I π hI S).comp (Ideal.Quotient.mk _) = π.comp S.subtype := rfl

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Express the relevant statement in the definitionally equal form `(x : R) ∈ I`.

Rewrite using `[← hI]`. Conclude with `ha`.
-/
theorem iota_injective (hI : RingHom.ker π = I) (S : Subring R) : Function.Injective (iota I π hI S) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change (x : R) ∈ I
  rw [← hI]
  exact ha

def trans {S S' : Subring R} (h : S ≤ S') : S ⧸ I.comap S.subtype →+* S' ⧸ I.comap S'.subtype :=
  Ideal.quotientMap _ (Subring.inclusion h) fun x hx => hx

/- English proof (translation)
Use extensionality with `x`. Both sides reduce to the same expression.
-/
theorem iota_comp_trans (hI : RingHom.ker π = I) {S S' : Subring R} (h : S ≤ S') :
    (iota I π hI S').comp (trans I h) = iota I π hI S := by
  ext x
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trans_comp_mk {S S' : Subring R} (h : S ≤ S') :
    (trans I h).comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp (Subring.inclusion h) := rfl

end GlobalTheory.AbHomDesc
