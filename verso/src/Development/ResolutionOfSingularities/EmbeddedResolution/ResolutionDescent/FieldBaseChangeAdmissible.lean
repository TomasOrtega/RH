import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SupportFlatPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MarkedIdealWithBoundary

/- English proof (authored)
After extending the field, the ambient structural morphism is the base change of the original one. Smoothness, local finite type, and quasi-compactness are preserved by base change. The map back to the original scheme is flat, since it is pulled back from a field extension. Flat pullback preserves nonvanishing on components. The new field has characteristic zero, the marking is unchanged and remains positive, and the pulled-back boundary has strict normal crossings by the field base-change result. These are the admissibility conditions.
-/
theorem isAdmissible_baseChange (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (L : Type u) [Field L]
    [CharZero L] (f : T.base →+* L) : (T.baseChange L f).IsAdmissible := by
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have := hV.quasiCompact
  have hflat : AlgebraicGeometry.Flat (specMapOfFieldHom T.base L f) :=
    instFlatSpecMapOfFieldHom T.base L f
  have hfst : AlgebraicGeometry.Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    inferInstance
  refine
    { charZero := ‹CharZero L›
      locallyOfFiniteType := ?_
      nonzeroOnComponents := ?_
      one_le_mult := hV.one_le_mult
      quasiCompact := ?_
      smooth := ?_
      snc := ?_ }
  · exact
      (inferInstance : AlgebraicGeometry.LocallyOfFiniteType
        (pullback.snd T.structMap (specMapOfFieldHom T.base L f)))
  · exact hV.nonzeroOnComponents.comap_of_flat
      (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
  · exact
      (inferInstance : AlgebraicGeometry.QuasiCompact
        (pullback.snd T.structMap (specMapOfFieldHom T.base L f)))
  · exact smooth_pullbackSnd_specMap T.structMap (CommRingCat.ofHom f)
  · exact inStrictNormalCrossingPosition_comap_pullback_specMap T.structMap (CommRingCat.ofHom f) T.boundary hV.snc

end MarkedIdealWithBoundary

end FunctorialResolution.EmbeddedResolution
