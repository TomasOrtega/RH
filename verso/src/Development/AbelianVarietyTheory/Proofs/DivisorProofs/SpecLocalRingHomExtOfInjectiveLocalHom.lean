import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Establish `hc : (spMap φ) (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R`. Establish `: IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom φ))` using `hl`. Conclude with `Spec_closedPoint (R := CommRingCat.of R) (S := CommRingCat.of R') (f := CommRingCat.ofHom φ)`. Establish `hp : x (IsLocalRing.closedPoint R) = y (IsLocalRing.closedPoint R)`. Rewrite using `[← hc]`.

Express the relevant statement in the definitionally equal form `(spMap φ ≫ x) (IsLocalRing.closedPoint R') = (spMap φ ≫ y) (IsLocalRing.closedPoint R')`. Rewrite using `[h]`. Take `⟨p, hpx⟩ : ∃ p, x (IsLocalRing.closedPoint R) = p` from `⟨_, rfl⟩`. Establish `ex : ∀ z : Sp R ⟶ Y, z (IsLocalRing.closedPoint R) = p → ∃ a, Spec.map a ≫ Y.fromSpecStalk p = z`. Introduce `z hz`.

Substitute `hz` using the available equality. Conclude with `⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R) z⟩`. Take `⟨a, rfl⟩` from `ex x hpx`. Take `⟨b, rfl⟩` from `ex y (hp ▸ hpx)`. Establish `h2 : spMap φ ≫ Spec.map a = spMap φ ≫ Spec.map b`.

Rewrite `h` using `[← Category.assoc, ← Category.assoc]`. Conclude with `(cancel_mono _).1 h`. Establish `h3 : a ≫ CommRingCat.ofHom φ = b ≫ CommRingCat.ofHom φ`. Apply `Spec.map_injective` to reduce the goal to its premises. Simplify `h2` using `[spMap, Spec.map_comp]`.

Establish `hab : a = b`. Use extensionality with `s`. Apply `hi` to reduce the goal to its premises. Use `congrArg (fun g => g.hom s) h3` as an intermediate fact. Simplify using `using this`.

Rewrite using `[hab]`.
-/
theorem GlobalTheory.spec_local_hom_ext_of_injective (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (φ : R →+* R') (hl : IsLocalHom φ) (hi : Function.Injective φ) (Y : Scheme.{0}) (x y : Sp R ⟶ Y)
    (h : spMap φ ≫ x = spMap φ ≫ y) : x = y := by
  have hc : (spMap φ) (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R := by
    have : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom φ)) := hl
    exact Spec_closedPoint (R := CommRingCat.of R) (S := CommRingCat.of R') (f := CommRingCat.ofHom φ)
  have hp : x (IsLocalRing.closedPoint R) = y (IsLocalRing.closedPoint R) := by
    rw [← hc]
    change (spMap φ ≫ x) (IsLocalRing.closedPoint R') = (spMap φ ≫ y) (IsLocalRing.closedPoint R')
    rw [h]
  obtain ⟨p, hpx⟩ : ∃ p, x (IsLocalRing.closedPoint R) = p := ⟨_, rfl⟩
  have ex : ∀ z : Sp R ⟶ Y, z (IsLocalRing.closedPoint R) = p →
      ∃ a, Spec.map a ≫ Y.fromSpecStalk p = z := by
    intro z hz
    subst hz
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R) z⟩
  obtain ⟨a, rfl⟩ := ex x hpx
  obtain ⟨b, rfl⟩ := ex y (hp ▸ hpx)
  have h2 : spMap φ ≫ Spec.map a = spMap φ ≫ Spec.map b := by
    rw [← Category.assoc, ← Category.assoc] at h
    exact (cancel_mono _).1 h
  have h3 : a ≫ CommRingCat.ofHom φ = b ≫ CommRingCat.ofHom φ := by
    apply Spec.map_injective
    simpa [spMap, Spec.map_comp] using h2
  have hab : a = b := by
    ext s
    apply hi
    have := congrArg (fun g => g.hom s) h3
    simpa using this
  rw [hab]
