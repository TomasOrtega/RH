import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `H Q Z U f ν hU hc`. Establish `hs : IsIso (pullback.snd U.ι (pullback.fst f ν))`. Use `isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_` and prove the remaining obligations. Rewrite using `[Scheme.Hom.opensRange_pullbackSnd]`. Use `top_unique fun z _ => ?_` and prove the remaining obligations.

Use `show pullback.fst f ν z ∈ U.ι.opensRange`. Rewrite using `[Scheme.Opens.opensRange_ι]`. Use `hU _ ⟨pullback.snd f ν z, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]`. Set `e` to `Scheme.homeoOfIso ((pullbackRightPullbackFstIso f ν U.ι).symm ≪≫ asIso (pullback.snd U.ι (pullback.fst f ν)))`.

Conclude with `e.connectedSpace_iff.2 hc`.
-/
theorem geomFibre_restrict_open_connected : ∀ (H Q Z : Scheme.{0}) (U : H.Opens) (f : H ⟶ Q) (ν : Z ⟶ Q), (∀ h : H, f h ∈ Set.range ν → h ∈ U) → ConnectedSpace (pullback f ν : Scheme.{0}) → ConnectedSpace (pullback (U.ι ≫ f) ν : Scheme.{0}) := by
  intro H Q Z U f ν hU hc
  have hs : IsIso (pullback.snd U.ι (pullback.fst f ν)) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    rw [Scheme.Hom.opensRange_pullbackSnd]
    refine top_unique fun z _ => ?_
    show pullback.fst f ν z ∈ U.ι.opensRange
    rw [Scheme.Opens.opensRange_ι]
    refine hU _ ⟨pullback.snd f ν z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  let e := Scheme.homeoOfIso ((pullbackRightPullbackFstIso f ν U.ι).symm ≪≫
    asIso (pullback.snd U.ι (pullback.fst f ν)))
  exact e.connectedSpace_iff.2 hc

end GlobalTheory.Mum
