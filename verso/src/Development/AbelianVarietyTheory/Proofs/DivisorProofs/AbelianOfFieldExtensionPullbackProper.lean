import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

/- English proof (translation)
Introduce `K K' _ _ i G _ B _ φ g hG h hP hB`. Establish `hc` using `hG.comm`. Use `hG.smooth` as an intermediate fact. Use `hG.separated` as an intermediate fact. Use `hG.quasiCompact` as an intermediate fact.

Use `hG.geomConnected` as an intermediate fact. Establish `: Flat (spMap i)` using `inferInstance`. Establish `: Surjective (spMap i)` using `inferInstance`. Establish `: UniversallyClosed G.hom` using `MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.1.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance`. Establish `hp : IsProper G.hom` using `⟨⟩`.

Establish `: ConnectedSpace G.left` using `GeometricallyConnected.geometrically_connectedSpace (f := G.hom) (𝟙 _) (𝟙 _) G.hom (IsPullback.of_horiz_isIso ⟨by simp⟩)`. Take `⟨d, hd⟩` from `exists_dim_of_preconnected G.hom (eSec G (default : PrimeSpectrum K))`. Establish `hd' : SmoothOfRelativeDimension d B.hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback h.1 hd`. Establish `e : d = g` using `ReciprocityTheory.ChartRestriction.G.H1.dim_unique B.hom hd' hB (eSec B (default : PrimeSpectrum K'))`. Substitute `e` using the available equality.

Conclude with `⟨⟨hc, inferInstance, hp, inferInstance⟩, hd⟩`.
-/
theorem abelian_of_field_of_pullback : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K') (G : Over (Sp K)) [GrpObj G] (B : Over (Sp K')) [GrpObj B] (φ : B.left ⟶ G.left) (g : ℕ), IsSemiAbelian G → IsGrpPullback B G (spMap i) φ → IsProper B.hom → SmoothOfRelativeDimension g B.hom → IsAbelianScheme G ∧ SmoothOfRelativeDimension g G.hom := by
  intro K K' _ _ i G _ B _ φ g hG h hP hB
  have hc := hG.comm
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have : Flat (spMap i) := inferInstance
  have : Surjective (spMap i) := inferInstance
  have : UniversallyClosed G.hom := MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.1.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have hp : IsProper G.hom := ⟨⟩
  have : ConnectedSpace G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := G.hom) (𝟙 _) (𝟙 _) G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected G.hom (eSec G (default : PrimeSpectrum K))
  have hd' : SmoothOfRelativeDimension d B.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback h.1 hd
  have e : d = g := ReciprocityTheory.ChartRestriction.G.H1.dim_unique B.hom hd' hB (eSec B (default : PrimeSpectrum K'))
  subst e
  exact ⟨⟨hc, inferInstance, hp, inferInstance⟩, hd⟩

end GlobalTheory.Mum.GenDesc
