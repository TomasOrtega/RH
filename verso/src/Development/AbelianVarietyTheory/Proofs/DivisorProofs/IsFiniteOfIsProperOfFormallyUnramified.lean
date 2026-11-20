import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.PropFin

/- English proof (translation)
Introduce `X S f _ hp hu`. Establish `hlqf : LocallyQuasiFinite f`. Use `⟨fun {U} hU {V} hV e => ?_⟩` and prove the remaining obligations. Establish `h₁` using `f.formallyUnramified_appLE hU hV e`. Establish `h₂` using `f.finiteType_appLE hU hV e`.

Use `algebraize [(f.appLE U V e).hom]`. Conclude with `inferInstanceAs (Algebra.QuasiFinite _ _)`. Conclude with `IsFinite.of_isProper_of_locallyQuasiFinite f`.
-/
theorem isFinite_of_isProper_of_formallyUnramified :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) [IsLocallyNoetherian S],
      IsProper f → FormallyUnramified f → IsFinite f := by
  intro X S f _ hp hu
  have hlqf : LocallyQuasiFinite f := by
    refine ⟨fun {U} hU {V} hV e => ?_⟩
    have h₁ := f.formallyUnramified_appLE hU hV e
    have h₂ := f.finiteType_appLE hU hV e
    algebraize [(f.appLE U V e).hom]
    exact inferInstanceAs (Algebra.QuasiFinite _ _)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end GlobalTheory.PropFin
