import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ S π hlft hsurj G' G β hpb hG'`. Use `⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩` and prove the remaining obligations. Set `jK : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K)` to `Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))`. Take `⟨t, ht⟩` from `GlobalTheory.GeomSurj.exists_lift_of_surjective (Ω := AlgebraicClosure K) π (jK ≫ y)`. Establish `hct : ConnectedSpace ↥(pullback G'.hom t)` using `pullback_of_geometrically hG'.geometrically_connectedSpace _ t`.

Establish `hP : IsPullback (pullback.fst G'.hom t ≫ β) (pullback.snd G'.hom t) G.hom (t ≫ π)` using `(IsPullback.of_hasPullback G'.hom t).paste_horiz hpb`. Rewrite `hP` using `[← ht]`. Establish `hc' : ConnectedSpace ↥(pullback G.hom (jK ≫ y))` using `hP.isoPullback.hom.homeomorph.connectedSpace_iff.mp hct`. Establish `hjK : Surjective jK` using `⟨fun z ↦ by`. Take `⟨w⟩ : Nonempty ↥(Spec (.of (AlgebraicClosure K)))` from `inferInstance`.

Conclude with `⟨w, Subsingleton.elim _ _⟩⟩`. Establish `hc'' : ConnectedSpace ↥(pullback (pullback.snd G.hom y) jK)` using `(pullbackLeftPullbackSndIso G.hom y jK).hom.homeomorph.connectedSpace_iff.mpr hc'`. Conclude with `(pullback.fst (pullback.snd G.hom y) jK).surjective.connectedSpace (pullback.fst (pullback.snd G.hom y) jK).continuous`.
-/
theorem geometricallyConnected_of_isPullback_of_surjective :
    ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π →
    ∀ (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π →
    GeometricallyConnected G'.hom → GeometricallyConnected G.hom := by
  intro R _ S π hlft hsurj G' G β hpb hG'
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  let jK : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  obtain ⟨t, ht⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective (Ω := AlgebraicClosure K) π (jK ≫ y)
  have hct : ConnectedSpace ↥(pullback G'.hom t) :=
    pullback_of_geometrically hG'.geometrically_connectedSpace _ t
  have hP : IsPullback (pullback.fst G'.hom t ≫ β) (pullback.snd G'.hom t) G.hom (t ≫ π) :=
    (IsPullback.of_hasPullback G'.hom t).paste_horiz hpb
  rw [← ht] at hP
  have hc' : ConnectedSpace ↥(pullback G.hom (jK ≫ y)) :=
    hP.isoPullback.hom.homeomorph.connectedSpace_iff.mp hct
  have hjK : Surjective jK := ⟨fun z ↦ by
    obtain ⟨w⟩ : Nonempty ↥(Spec (.of (AlgebraicClosure K))) := inferInstance
    exact ⟨w, Subsingleton.elim _ _⟩⟩
  have hc'' : ConnectedSpace ↥(pullback (pullback.snd G.hom y) jK) :=
    (pullbackLeftPullbackSndIso G.hom y jK).hom.homeomorph.connectedSpace_iff.mpr hc'
  exact (pullback.fst (pullback.snd G.hom y) jK).surjective.connectedSpace
    (pullback.fst (pullback.snd G.hom y) jK).continuous

end GlobalTheory.Mum
