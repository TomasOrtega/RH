import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CptInh

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `t ht`. Take `⟨U, hyU, s, rfl⟩` from `X.presheaf.germ_exist t`. Establish `hxU : x ∈ U` using `h.mem_open U.isOpen hyU`. Establish `e : ConcreteCategory.hom (X.presheaf.stalkSpecializes h) (ConcreteCategory.hom (X.presheaf.germ U y hyU) s) = ConcreteCategory.hom (X.presheaf.germ U x hxU) s`.

Rewrite using `[← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]`. Establish `hs : s = 0`. Apply `germ_injective_of_isIntegral X x hxU` to reduce the goal to its premises. Rewrite using `[map_zero, ← e]`. Conclude with `ht`.

Rewrite using `[hs, map_zero]`.
-/
theorem spec_inj (X : Scheme.{0}) [IsIntegral X] {x y : X} (h : x ⤳ y) :
    Function.Injective (X.presheaf.stalkSpecializes h).hom := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨U, hyU, s, rfl⟩ := X.presheaf.germ_exist t
  have hxU : x ∈ U := h.mem_open U.isOpen hyU
  have e : ConcreteCategory.hom (X.presheaf.stalkSpecializes h) (ConcreteCategory.hom (X.presheaf.germ U y hyU) s) =
      ConcreteCategory.hom (X.presheaf.germ U x hxU) s := by
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  have hs : s = 0 := by
    apply germ_injective_of_isIntegral X x hxU
    rw [map_zero, ← e]
    exact ht
  rw [hs, map_zero]

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

/- English proof (translation)
Simplify using `only [unitAt, regAt, RingHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ha, ⟨u, rfl⟩, ⟨v, hv⟩⟩`. Use `⟨u, ?_, rfl⟩` and prove the remaining obligations. Establish `e : genMap ξ p (u * v) = genMap ξ p 1`.

Rewrite using `[map_mul, hv, map_one, mul_inv_cancel₀ ha]`. Conclude with `IsUnit.of_mul_eq_one v (h.inj p e)`. Introduce and unpack `⟨u, ⟨w, rfl⟩, rfl⟩`. Establish `key : genMap ξ p ↑w * genMap ξ p ↑w⁻¹ = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`.

Conclude with `⟨left_ne_zero_of_mul_eq_one key, ⟨↑w, rfl⟩, ⟨↑w⁻¹, eq_inv_of_mul_eq_one_right key⟩⟩`.
-/
theorem unit_iff (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (p : Cpt ξ) (a : Ω) :
    unitAt ξ p a ↔ ∃ u, IsUnit u ∧ genMap ξ p u = a := by
  simp only [unitAt, regAt, RingHom.mem_range]
  constructor
  · rintro ⟨ha, ⟨u, rfl⟩, ⟨v, hv⟩⟩
    refine ⟨u, ?_, rfl⟩
    have e : genMap ξ p (u * v) = genMap ξ p 1 := by
      rw [map_mul, hv, map_one, mul_inv_cancel₀ ha]
    exact IsUnit.of_mul_eq_one v (h.inj p e)
  · rintro ⟨u, ⟨w, rfl⟩, rfl⟩
    have key : genMap ξ p ↑w * genMap ξ p ↑w⁻¹ = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact ⟨left_ne_zero_of_mul_eq_one key, ⟨↑w, rfl⟩, ⟨↑w⁻¹, eq_inv_of_mul_eq_one_right key⟩⟩

/- English proof (translation)
Conclude with `Function.Injective.isDomain (genMap ξ p) (h.inj p)`.
-/
theorem dom (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (p : Cpt ξ) :
    IsDomain (X.presheaf.stalk p.1) := by
  exact Function.Injective.isDomain (genMap ξ p) (h.inj p)

/- English proof (translation)
Establish `hy' : y ∈ Set.range (X.fromSpecStalk (genPt ξ))`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `hy`. Take `⟨q, hq⟩` from `hy'`. Take `⟨f, hf⟩ : ∃ f : X.presheaf.stalk (genPt ξ) →+* Ω, Function.Bijective f` from `⟨(Scheme.stalkClosedPointTo ξ).hom, h.bij⟩`.

Establish `hmax : ∀ x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (genPt ξ)), x = 0`. Introduce `x hx`. Assume the negation of the conclusion as `hne`. Establish `h1 : f x ≠ 0`. Introduce `h0`.

Apply `hne` to reduce the goal to its premises. Apply `hf.1` to reduce the goal to its premises. Rewrite using `[h0, map_zero]`. Take `⟨v, hv⟩` from `hf.2 (f x)⁻¹`. Establish `hxv : x * v = 1` using `hf.1 (by rw [map_mul, hv, mul_inv_cancel₀ h1, map_one])`.

Conclude with `mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x).mp hx) (IsUnit.of_mul_eq_one v hxv)`. Establish `hq' : q = IsLocalRing.closedPoint (X.presheaf.stalk (genPt ξ))`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `IsLocalRing.le_maximalIdeal (PrimeSpectrum.isPrime q).ne_top`.

Introduce `x hx`. Rewrite using `[hmax x hx]`. Conclude with `zero_mem _`. Rewrite using `[← hq, hq']`. Conclude with `Scheme.fromSpecStalk_closedPoint`.
-/
theorem nogen (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (y : X) (hy : y ⤳ genPt ξ) :
    y = genPt ξ := by
  have hy' : y ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]
    exact hy
  obtain ⟨q, hq⟩ := hy'
  obtain ⟨f, hf⟩ : ∃ f : X.presheaf.stalk (genPt ξ) →+* Ω, Function.Bijective f :=
    ⟨(Scheme.stalkClosedPointTo ξ).hom, h.bij⟩
  have hmax : ∀ x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (genPt ξ)), x = 0 := by
    intro x hx
    by_contra hne
    have h1 : f x ≠ 0 := by
      intro h0
      apply hne
      apply hf.1
      rw [h0, map_zero]
    obtain ⟨v, hv⟩ := hf.2 (f x)⁻¹
    have hxv : x * v = 1 := hf.1 (by rw [map_mul, hv, mul_inv_cancel₀ h1, map_one])
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x).mp hx) (IsUnit.of_mul_eq_one v hxv)
  have hq' : q = IsLocalRing.closedPoint (X.presheaf.stalk (genPt ξ)) := by
    apply PrimeSpectrum.ext
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (PrimeSpectrum.isPrime q).ne_top
    · intro x hx
      rw [hmax x hx]
      exact zero_mem _
  rw [← hq, hq']
  exact Scheme.fromSpecStalk_closedPoint

end GlobalTheory.CompanionTheory.Ar.CptInh
