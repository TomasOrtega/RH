import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ValHom

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

def stalkEquiv {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
  RingEquiv.ofBijective (genMap ξ p).rangeRestrict
    ⟨fun a b hab => hξ.inj p (congrArg Subtype.val hab), (genMap ξ p).rangeRestrict_surjective⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem stalkEquiv_coe {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) (s : X.presheaf.stalk p.1) :
    ((stalkEquiv ξ hξ p s : regAt ξ p) : Ω) = genMap ξ p s := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hs`. Take `⟨u, rfl⟩` from `hs`. Use `⟨((u.isUnit).map (genMap ξ p)).ne_zero, ⟨_, rfl⟩, ⟨((u⁻¹ : _ˣ) : X.presheaf.stalk p.1), ?_⟩⟩` and prove the remaining obligations. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises.

Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Introduce and unpack `⟨h0, -, ⟨t, ht⟩⟩`. Use `IsUnit.of_mul_eq_one t (hξ.inj p ?_)` and prove the remaining obligations. Rewrite using `[map_mul, map_one, ht, mul_inv_cancel₀ h0]`.
-/
theorem isUnit_iff_unitAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) (s : X.presheaf.stalk p.1) :
    IsUnit s ↔ unitAt ξ p (genMap ξ p s) := by
  constructor
  · intro hs
    obtain ⟨u, rfl⟩ := hs
    refine ⟨((u.isUnit).map (genMap ξ p)).ne_zero, ⟨_, rfl⟩, ⟨((u⁻¹ : _ˣ) : X.presheaf.stalk p.1), ?_⟩⟩
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, Units.inv_mul, map_one]
  · rintro ⟨h0, -, ⟨t, ht⟩⟩
    refine IsUnit.of_mul_eq_one t (hξ.inj p ?_)
    rw [map_mul, map_one, ht, mul_inv_cancel₀ h0]

/- English proof (translation)
Set `p : Cpt ξ` to `⟨centre z, h⟩`. Set `e` to `stalkEquiv ξ hξ p`. Set `v : X.presheaf.stalk (centre z) →+* R` to `(Scheme.stalkClosedPointTo z).hom`. Establish `hv : IsLocalHom v` using `inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)`. Establish `key : ∀ s, e.symm (e s) = s` using `e.symm_apply_apply`.

Use `⟨v.comp (e.symm : regAt ξ p →+* X.presheaf.stalk p.1), ?_, ?_⟩` and prove the remaining obligations. Introduce `a r`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h', s, hs, hr⟩`. Establish `hs' : genMap ξ p s = a` using `hs`.

Use `⟨⟨s, hs'⟩, ?_⟩` and prove the remaining obligations. Establish `: (⟨a, ⟨s, hs'⟩⟩ : regAt ξ p) = e s` using `Subtype.ext hs'.symm`. Simplify using `only [RingHom.comp_apply, RingHom.coe_coe]`. Rewrite using `[this, key]`. Conclude with `hr`.

Introduce and unpack `⟨ha, hr⟩`. Use `⟨h, e.symm ⟨a, ha⟩, ?_, hr⟩` and prove the remaining obligations. Use `stalkEquiv_coe ξ hξ p (e.symm ⟨a, ha⟩)` as an intermediate fact. Rewrite `this` using `[RingEquiv.apply_symm_apply]`. Conclude with `this.symm`.

Introduce `a`. Take `⟨s, rfl⟩` from `e.surjective a`. Simplify using `only [RingHom.comp_apply, RingHom.coe_coe]`. Rewrite using `[key]`. Establish `: IsUnit (v s) ↔ IsUnit s` using `isUnit_map_iff v s`.

Conclude with `this.trans (isUnit_iff_unitAt ξ hξ p s)`.
-/
theorem exists_valAt_hom (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (R : Type) [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X)
    (h : genPt ξ ⤳ centre z) (hξ : IsCptGen ξ) :
    ∃ φ : regAt ξ ⟨centre z, h⟩ →+* R,
      (∀ (a : Ω) (r : R), ValAt ξ z a r ↔ ∃ ha : a ∈ regAt ξ ⟨centre z, h⟩, φ ⟨a, ha⟩ = r) ∧
      ∀ a : regAt ξ ⟨centre z, h⟩, IsUnit (φ a) ↔ unitAt ξ ⟨centre z, h⟩ (a : Ω) := by
  let p : Cpt ξ := ⟨centre z, h⟩
  let e := stalkEquiv ξ hξ p
  let v : X.presheaf.stalk (centre z) →+* R := (Scheme.stalkClosedPointTo z).hom
  have hv : IsLocalHom v := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)
  have key : ∀ s, e.symm (e s) = s := e.symm_apply_apply
  refine ⟨v.comp (e.symm : regAt ξ p →+* X.presheaf.stalk p.1), ?_, ?_⟩
  · intro a r
    constructor
    · rintro ⟨h', s, hs, hr⟩
      have hs' : genMap ξ p s = a := hs
      refine ⟨⟨s, hs'⟩, ?_⟩
      have : (⟨a, ⟨s, hs'⟩⟩ : regAt ξ p) = e s := Subtype.ext hs'.symm
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      rw [this, key]
      exact hr
    · rintro ⟨ha, hr⟩
      refine ⟨h, e.symm ⟨a, ha⟩, ?_, hr⟩
      have := stalkEquiv_coe ξ hξ p (e.symm ⟨a, ha⟩)
      rw [RingEquiv.apply_symm_apply] at this
      exact this.symm
  · intro a
    obtain ⟨s, rfl⟩ := e.surjective a
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [key]
    have : IsUnit (v s) ↔ IsUnit s := isUnit_map_iff v s
    exact this.trans (isUnit_iff_unitAt ξ hξ p s)

end GlobalTheory.CompanionTheory.Ar.ValHom
