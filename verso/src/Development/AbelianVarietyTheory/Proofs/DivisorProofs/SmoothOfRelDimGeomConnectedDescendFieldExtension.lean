import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescentSmoothDimension

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.FieldDescentSm

/- English proof (translation)
Introduce `k E _ _ _ Y X p q π H D hX hD hq`. Establish `hf` using `GlobalTheory.FieldDescentAb.fpqc_spMap (algebraMap k E)`. Establish `hsq : Smooth q` using `SmoothOfRelativeDimension.smooth D q`. Establish `hsm : Smooth p` using `MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) H.flip hf hsq`. Establish `hp : GeometricallyConnected p` using `GlobalTheory.FieldDescentAb.geometricallyConnected_of_isPullback (algebraMap k E) H`.

Use `⟨?_, hp⟩` and prove the remaining obligations. Establish `hc : ConnectedSpace Y` using `hp.geometrically_connectedSpace (𝟙 _) (𝟙 Y) p (IsPullback.of_horiz_isIso ⟨by simp⟩)`. Take `⟨x⟩` from `hX`. Take `⟨D', hD'⟩` from `ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_dim_of_preconnected p (π x)`. Establish `h' : SmoothOfRelativeDimension D' q` using `(smoothOfRelativeDimension_isStableUnderBaseChange D').of_isPullback H hD'`.

Rewrite using `[ReciprocityTheory.ChartRestriction.G.H1.dim_unique q hD h' x]`. Conclude with `hD'`.
-/
theorem smoothOfRelativeDimension_and_geometricallyConnected_descend : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → ∀ D : ℕ, Nonempty X → SmoothOfRelativeDimension D q → GeometricallyConnected q → SmoothOfRelativeDimension D p ∧ GeometricallyConnected p := by
  intro k E _ _ _ Y X p q π H D hX hD hq
  have hf := GlobalTheory.FieldDescentAb.fpqc_spMap (algebraMap k E)
  have hsq : Smooth q := SmoothOfRelativeDimension.smooth D q
  have hsm : Smooth p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) H.flip hf hsq
  have hp : GeometricallyConnected p :=
    GlobalTheory.FieldDescentAb.geometricallyConnected_of_isPullback (algebraMap k E) H
  refine ⟨?_, hp⟩
  have hc : ConnectedSpace Y :=
    hp.geometrically_connectedSpace (𝟙 _) (𝟙 Y) p (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨x⟩ := hX
  obtain ⟨D', hD'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_dim_of_preconnected p (π x)
  have h' : SmoothOfRelativeDimension D' q :=
    (smoothOfRelativeDimension_isStableUnderBaseChange D').of_isPullback H hD'
  rw [ReciprocityTheory.ChartRestriction.G.H1.dim_unique q hD h' x]
  exact hD'

end GlobalTheory.FieldDescentSm
