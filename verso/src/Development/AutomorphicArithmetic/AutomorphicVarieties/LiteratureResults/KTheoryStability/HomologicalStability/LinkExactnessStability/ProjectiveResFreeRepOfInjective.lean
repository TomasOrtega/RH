import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

/- English proof (translation)
Set `e : H ≃* G` to `MulEquiv.ofBijective ψ hψ`. Use `haveI : (Rep.resFunctor (k := k) ψ).Full := Rep.full_res ψ hψ.2`. Use `haveI : (Rep.resFunctor (k := k) ψ).EssSurj := ⟨fun N => ⟨Rep.of (N.ρ.comp e.symm.toMonoidHom), ⟨Rep.mkIso (.mk (LinearEquiv.refl k N.V) fun h => by`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `N.ρ (e.symm (ψ h)) x = N.ρ h x`.

Establish `: e.symm (ψ h) = h` using `e.symm_apply_apply h`. Rewrite using `[this])⟩⟩⟩`. Conclude with `{ }`.
-/
theorem resFunctor_isEquivalence_of_bijective {k G H : Type} [CommRing k] [Group G] [Group H]
    (ψ : H →* G) (hψ : Function.Bijective ψ) : (Rep.resFunctor (k := k) ψ).IsEquivalence := by
  let e : H ≃* G := MulEquiv.ofBijective ψ hψ
  haveI : (Rep.resFunctor (k := k) ψ).Full := Rep.full_res ψ hψ.2
  haveI : (Rep.resFunctor (k := k) ψ).EssSurj := ⟨fun N => ⟨Rep.of (N.ρ.comp e.symm.toMonoidHom),
    ⟨Rep.mkIso (.mk (LinearEquiv.refl k N.V) fun h => by
      ext x
      change N.ρ (e.symm (ψ h)) x = N.ρ h x
      have : e.symm (ψ h) = h := e.symm_apply_apply h
      rw [this])⟩⟩⟩
  exact { }

/- English proof (translation)
Set `ψ : H →* φ.range` to `φ.rangeRestrict`. Establish `hψ : Function.Bijective ψ` using `⟨φ.rangeRestrict_injective_iff.2 hφ, φ.rangeRestrict_surjective⟩`. Use `haveI := resFunctor_isEquivalence_of_bijective (k := k) ψ hψ`. Establish `h1 : Projective (Rep.res φ.range.subtype P)` using `(Rep.resFunctor (k := k) φ.range.subtype).projective_obj_of_projective (X := P) inferInstance`. Establish `h2 : Projective (Rep.res ψ (Rep.res φ.range.subtype P))` using `(Rep.resFunctor (k := k) ψ).projective_obj_of_projective h1`.

Conclude with `h2`.
-/
theorem projective_res_of_injective {k G H : Type} [CommRing k] [Group G] [Group H]
    (φ : H →* G) (hφ : Function.Injective φ) (P : Rep k G) [Projective P] :
    Projective (Rep.res φ P) := by
  let ψ : H →* φ.range := φ.rangeRestrict
  have hψ : Function.Bijective ψ := ⟨φ.rangeRestrict_injective_iff.2 hφ, φ.rangeRestrict_surjective⟩
  haveI := resFunctor_isEquivalence_of_bijective (k := k) ψ hψ
  have h1 : Projective (Rep.res φ.range.subtype P) :=
    (Rep.resFunctor (k := k) φ.range.subtype).projective_obj_of_projective (X := P) inferInstance
  have h2 : Projective (Rep.res ψ (Rep.res φ.range.subtype P)) :=
    (Rep.resFunctor (k := k) ψ).projective_obj_of_projective h1
  exact h2

end GlobalTheory.HomStab

/- English proof (translation)
Introduce `k G H _ _ _ φ hφ ι`. Conclude with `GlobalTheory.HomStab.projective_res_of_injective φ hφ _`.
-/
theorem GlobalTheory.HomStab.projective_res_free_of_injective : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G), Function.Injective φ → ∀ ι : Type, Projective (Rep.res φ (Rep.free k G ι)) := by
  intro k G H _ _ _ φ hφ ι
  exact GlobalTheory.HomStab.projective_res_of_injective φ hφ _

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.HomStab.projective_res_free_of_injective`. Consider the case `exact @GlobalTheory.HomStab.projective_res_of_injective`. Consider the case `exact @GlobalTheory.HomStab.resFunctor_isEquivalence_of_bijective`.
-/
theorem _root_.GlobalTheory.T.projective_res_free_rep_of_injective : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G), Function.Injective φ → ∀ ι : Type, Projective (Rep.res φ (Rep.free k G ι)) := by
  first
  | exact @GlobalTheory.HomStab.projective_res_free_of_injective
  | exact @GlobalTheory.HomStab.projective_res_of_injective
  | exact @GlobalTheory.HomStab.resFunctor_isEquivalence_of_bijective
end
