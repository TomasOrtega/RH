import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.Member

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Use `⟨RingHom.Flat.comp (RingHom.Flat.of_bijective he) h1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]`. Conclude with `h2`. Rewrite using `[← RingHom.comp_assoc]`.

Conclude with `RingHom.Finite.comp h3 (RingHom.Finite.of_surjective e he.2)`.
-/
theorem isEtaleCompletion_comp_bijective' {B A R : Type} [CommRing B] [IsLocalRing B] [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (e : B →+* A) (he : Function.Bijective e) (φ : A →+* R)
    (h : IsEtaleCompletion φ) : IsEtaleCompletion (φ.comp e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨RingHom.Flat.comp (RingHom.Flat.of_bijective he) h1, ?_, ?_⟩
  · rw [← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]
    exact h2
  · rw [← RingHom.comp_assoc]
    exact RingHom.Finite.comp h3 (RingHom.Finite.of_surjective e he.2)

/- English proof (translation)
Introduce `R _ _ X Y ξ g _ h`. Establish `hb : Function.Bijective (g.stalkMap (ξ (IsLocalRing.closedPoint (CommRingCat.of R)))).hom` using `ConcreteCategory.bijective_of_isIso _`. Rewrite using `[Scheme.stalkClosedPointTo_comp]`. Conclude with `isEtaleCompletion_comp_bijective' _ hb _ h`.
-/
theorem isEtaleCompletion_stalkClosedPointTo_comp_iso : ∀ {R : Type} [CommRing R] [IsLocalRing R] {X Y : Scheme.{0}} (ξ : Spec (CommRingCat.of R) ⟶ X) (g : X ⟶ Y) [IsIso g], IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → IsEtaleCompletion (Scheme.stalkClosedPointTo (ξ ≫ g)).hom := by
  intro R _ _ X Y ξ g _ h
  have hb : Function.Bijective (g.stalkMap (ξ (IsLocalRing.closedPoint (CommRingCat.of R)))).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [Scheme.stalkClosedPointTo_comp]
  exact isEtaleCompletion_comp_bijective' _ hb _ h

end GlobalTheory.Member
