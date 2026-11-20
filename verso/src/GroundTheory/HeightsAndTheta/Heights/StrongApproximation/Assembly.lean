import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PHypPairExists
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PAETopologicalRing
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PEDenseInAE
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.POrthProjection
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PEichlerDense
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PClosureIsSubmonoid
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PLocalRingHypotheses
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PPlaceMaps
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PEichlerAtPlace
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PLocalInClosure
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PTruncation
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PAENeighbourhoods
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PSAHolds
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PSAOpenHolds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.StrongApprox

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem AETopologicalRing.full : AETopologicalRing.Statement := AETopologicalRing.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HypPairExists.full : HypPairExists.Statement := HypPairExists.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem EDenseInAE.full : EDenseInAE.Statement := EDenseInAE.proof AETopologicalRing.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem OrthProjection.full : OrthProjection.Statement := OrthProjection.proof AETopologicalRing.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem EichlerDense.full : EichlerDense.Statement :=
  EichlerDense.proof AETopologicalRing.full EDenseInAE.full OrthProjection.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ClosureIsSubmonoid.full : ClosureIsSubmonoid.Statement :=
  ClosureIsSubmonoid.proof AETopologicalRing.full EichlerDense.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LocalRingHypotheses.full : LocalRingHypotheses.Statement := LocalRingHypotheses.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PlaceMaps.full : PlaceMaps.Statement := PlaceMaps.proof LocalRingHypotheses.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem EichlerAtPlace.full : EichlerAtPlace.Statement := EichlerAtPlace.proof PlaceMaps.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LocalInClosure.full : LocalInClosure.Statement :=
  LocalInClosure.proof HypPairExists.full ClosureIsSubmonoid.full LocalRingHypotheses.full
    PlaceMaps.full EichlerAtPlace.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Truncation.full : Truncation.Statement := Truncation.proof LocalInClosure.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem AENeighbourhoods.full : AENeighbourhoods.Statement :=
  AENeighbourhoods.proof AETopologicalRing.full PlaceMaps.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SAHolds.full : ReciprocityTheory.ChartRestriction.G.SA.SAStatement :=
  SAHolds.proof HypPairExists.full AENeighbourhoods.full Truncation.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SAOpenHolds.full : ReciprocityTheory.ChartRestriction.G.SA.SAOpenStatement :=
  SAOpenHolds.proof SAHolds.full AETopologicalRing.full

end GroundTheory.Heights₂.Heights.StrongApprox
