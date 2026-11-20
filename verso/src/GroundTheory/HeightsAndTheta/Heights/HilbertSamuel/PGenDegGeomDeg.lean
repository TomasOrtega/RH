import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegGeomDeg
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D A hV hA`. Establish `h` using `hDG K ι (mCoordIdeal y) D (fun _ => A) hV (fun _ => hA)`. Establish `hpot : pot (fun _ : Fin D => A) = fun (_ : Fin D) z => Real.log (A.h z)` using `rfl`. Rewrite `h` using `[hpot]`. Unfold `geomDeg genDeg`.

Rewrite using `[h]`.
-/
theorem GenDegGeomDeg.proof (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) :
    GenDegGeomDeg.Statement := by
  intro K _ ι _ Ω _ y D A hV hA
  classical
  have h := hDG K ι (mCoordIdeal y) D (fun _ => A) hV (fun _ => hA)
  have hpot : pot (fun _ : Fin D => A) = fun (_ : Fin D) z => Real.log (A.h z) := rfl
  rw [hpot] at h
  unfold geomDeg genDeg
  rw [h]

end GroundTheory.Heights₂.Heights.HilbertSamuel
