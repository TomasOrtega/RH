import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.ProjClosure

/- English proof (translation)
Take `⟨N, c, hc, rfl⟩` from `hs`. Establish `P` using `GlobalTheory.ProjSpace.isPullback_baseChange N (algebraMap O R)`. Establish `hf : Flat (spMap (algebraMap O R))` using `GlobalTheory.flat_specMap_localization M R`. Establish `hm : Mono (spMap (algebraMap O R))` using `GlobalTheory.mono_specMap_localization M R`. Establish `hq : QuasiCompact (spMap (algebraMap O R))` using `inferInstance`.

Establish `: Flat (GlobalTheory.ProjSpace.baseChange N (algebraMap O R))` using `MorphismProperty.of_isPullback P.flip hf`. Establish `: Mono (GlobalTheory.ProjSpace.baseChange N (algebraMap O R))` using `(MorphismProperty.monomorphisms _).of_isPullback P.flip hm`. Establish `: QuasiCompact (GlobalTheory.ProjSpace.baseChange N (algebraMap O R))` using `MorphismProperty.of_isPullback P.flip hq`. Set `j` to `c ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap O R)`. Establish `H` using `GlobalTheory.isPullback_toImage_of_isClosedImmersion j c _ rfl`.

Conclude with `⟨j.image, j.imageι ≫ PSpace.str O N, j.toImage, ⟨N, j.imageι, inferInstance, rfl⟩, H.flip.paste_vert P⟩`.
-/
theorem exists_isProjOver_isPullback_of_isLocalization {O R : Type} [CommRing O] [CommRing R] [Algebra O R]
    (M : Submonoid O) [IsLocalization M R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : IsProjOver s) :
    ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp O) (i : X ⟶ X'),
      IsProjOver s' ∧ IsPullback i s s' (spMap (algebraMap O R)) := by
  obtain ⟨N, c, hc, rfl⟩ := hs
  have P := GlobalTheory.ProjSpace.isPullback_baseChange N (algebraMap O R)
  have hf : Flat (spMap (algebraMap O R)) := GlobalTheory.flat_specMap_localization M R
  have hm : Mono (spMap (algebraMap O R)) := GlobalTheory.mono_specMap_localization M R
  have hq : QuasiCompact (spMap (algebraMap O R)) := inferInstance
  have : Flat (GlobalTheory.ProjSpace.baseChange N (algebraMap O R)) := MorphismProperty.of_isPullback P.flip hf
  have : Mono (GlobalTheory.ProjSpace.baseChange N (algebraMap O R)) :=
    (MorphismProperty.monomorphisms _).of_isPullback P.flip hm
  have : QuasiCompact (GlobalTheory.ProjSpace.baseChange N (algebraMap O R)) :=
    MorphismProperty.of_isPullback P.flip hq
  let j := c ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap O R)
  have H := GlobalTheory.isPullback_toImage_of_isClosedImmersion j c _ rfl
  exact ⟨j.image, j.imageι ≫ PSpace.str O N, j.toImage, ⟨N, j.imageι, inferInstance, rfl⟩,
    H.flip.paste_vert P⟩

/- English proof (translation)
Introduce `_ _ _ _ _ a _ _ s hs` and use `exists_isProjOver_isPullback_of_isLocalization (Submonoid.powers a) s hs`.
-/
theorem exists_projective_closure : ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (a : O) [IsLocalization.Away a R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProjOver s → ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp O) (i : X ⟶ X'), IsProjOver s' ∧ IsPullback i s s' (spMap (algebraMap O R)) :=
  fun _ _ _ _ _ a _ _ s hs =>
    exists_isProjOver_isPullback_of_isLocalization (Submonoid.powers a) s hs

end GlobalTheory.ProjClosure
