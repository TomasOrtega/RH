import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PReductionSmallLast
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PReductionSmallFirst
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PInteriorDichotomy
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PAvoidMatrixLemma
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMinkowskiCovolumeBound
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PCuspWeightBound
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PShortVectorsOrthogonal
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PPackingCount
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMeanCountBound
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PTailBound
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMeanLogPlus
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMeanCuspWeight
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PTelescopeMetric
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PLimitInEpsilon
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

universe u

/- English proof (translation)
The claim follows from `ReductionSmallLast.proof`.
-/
theorem ReductionSmallLast.full : ReductionSmallLast.Statement :=
  ReductionSmallLast.proof

/- English proof (translation)
The claim follows from `ReductionSmallFirst.proof`.
-/
theorem ReductionSmallFirst.full : ReductionSmallFirst.Statement :=
  ReductionSmallFirst.proof

/- English proof (translation)
The claim follows from `InteriorDichotomy.proof`.
-/
theorem InteriorDichotomy.full : InteriorDichotomy.Statement :=
  InteriorDichotomy.proof

/- English proof (translation)
The claim follows from `AvoidMatrixLemma.proof`.
-/
theorem AvoidMatrixLemma.full : AvoidMatrixLemma.Statement :=
  AvoidMatrixLemma.proof

/- English proof (translation)
The claim follows from `MinkowskiCovolumeBound.proof`.
-/
theorem MinkowskiCovolumeBound.full : MinkowskiCovolumeBound.Statement.{u} :=
  MinkowskiCovolumeBound.proof

/- English proof (translation)
The claim follows from `CuspWeightBound.proof`.
-/
theorem CuspWeightBound.full : CuspWeightBound.Statement :=
  CuspWeightBound.proof

/- English proof (translation)
The claim follows from `ShortVectorsOrthogonal.proof`.
-/
theorem ShortVectorsOrthogonal.full : ShortVectorsOrthogonal.Statement :=
  ShortVectorsOrthogonal.proof

/- English proof (translation)
The claim follows from `PackingCount.proof`.
-/
theorem PackingCount.full : PackingCount.Statement :=
  PackingCount.proof

/- English proof (translation)
The claim follows from `MeanCountBound.proof`.
-/
theorem MeanCountBound.full : MeanCountBound.Statement.{u} :=
  MeanCountBound.proof

/- English proof (translation)
The claim follows from `TailBound.proof MeanCountBound.full`.
-/
theorem TailBound.full : TailBound.Statement.{u} :=
  TailBound.proof MeanCountBound.full

/- English proof (translation)
The claim follows from `MeanLogPlus.proof TailBound.full`.
-/
theorem MeanLogPlus.full : MeanLogPlus.Statement.{u} :=
  MeanLogPlus.proof TailBound.full

/- English proof (translation)
The claim follows from `MeanCuspWeight.proof`.
-/
theorem MeanCuspWeight.full : MeanCuspWeight.Statement :=
  MeanCuspWeight.proof

/- English proof (translation)
The claim follows from `TelescopeMetric.proof`.
-/
theorem TelescopeMetric.full : TelescopeMetric.Statement :=
  TelescopeMetric.proof

/- English proof (translation)
The claim follows from `LimitInEpsilon.proof`.
-/
theorem LimitInEpsilon.full : LimitInEpsilon.Statement :=
  LimitInEpsilon.proof

end GroundTheory.Heights₂.Heights.LowerBound
