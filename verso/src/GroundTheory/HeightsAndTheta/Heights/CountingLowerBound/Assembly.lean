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
A detailed English derivation is pending.
-/
theorem ReductionSmallLast.full : ReductionSmallLast.Statement :=
  ReductionSmallLast.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ReductionSmallFirst.full : ReductionSmallFirst.Statement :=
  ReductionSmallFirst.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem InteriorDichotomy.full : InteriorDichotomy.Statement :=
  InteriorDichotomy.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem AvoidMatrixLemma.full : AvoidMatrixLemma.Statement :=
  AvoidMatrixLemma.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MinkowskiCovolumeBound.full : MinkowskiCovolumeBound.Statement.{u} :=
  MinkowskiCovolumeBound.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CuspWeightBound.full : CuspWeightBound.Statement :=
  CuspWeightBound.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ShortVectorsOrthogonal.full : ShortVectorsOrthogonal.Statement :=
  ShortVectorsOrthogonal.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PackingCount.full : PackingCount.Statement :=
  PackingCount.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MeanCountBound.full : MeanCountBound.Statement.{u} :=
  MeanCountBound.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TailBound.full : TailBound.Statement.{u} :=
  TailBound.proof MeanCountBound.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MeanLogPlus.full : MeanLogPlus.Statement.{u} :=
  MeanLogPlus.proof TailBound.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MeanCuspWeight.full : MeanCuspWeight.Statement :=
  MeanCuspWeight.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TelescopeMetric.full : TelescopeMetric.Statement :=
  TelescopeMetric.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LimitInEpsilon.full : LimitInEpsilon.Statement :=
  LimitInEpsilon.proof

end GroundTheory.Heights₂.Heights.LowerBound
