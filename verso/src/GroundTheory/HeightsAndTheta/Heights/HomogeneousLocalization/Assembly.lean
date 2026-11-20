import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.Assembly
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSCoord
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSIndex
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSValue
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSContinuousFrame
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSNormConj
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PPNFlat
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PPNReduced
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSFullSupport
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSConjInvariant
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PPolySections
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PMonomialBasis
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PSupMonomial
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.IntegralMonoInnerEqZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MeasureTheory NumberField
  GroundTheory.Arith.SchemeCoh

universe u

noncomputable section

namespace SectionsLatticeFS

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FSCoord.full : FSCoord.Statement.{u} := FSCoord.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FSIndex.full : FSIndex.Statement.{u} := FSIndex.proof FSCoord.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FSValue.full : FSValue.Statement.{u} := FSValue.proof FSCoord.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FSContinuousFrame.full : FSContinuousFrame.Statement.{u} :=
  FSContinuousFrame.proof FSIndex.full ComplexMetric.RegularContinuous.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FSNormConj.full : FSNormConj.Statement.{u} := FSNormConj.proof FSIndex.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PNFlat.full : PNFlat.Statement.{u} := PNFlat.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PNReduced.full : PNReduced.Statement.{u} := PNReduced.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FSFullSupport.full : FSFullSupport.Statement := FSFullSupport.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FSConjInvariant.full : FSConjInvariant.Statement := FSConjInvariant.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PolySections.full : PolySections.Statement.{u} := PolySections.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MonomialBasis.full : MonomialBasis.Statement.{u} := MonomialBasis.proof PolySections.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SupMonomial.full : SupMonomial.Statement := SupMonomial.proof FSValue.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem L2MonomialOrthogonality.full : L2MonomialOrthogonality.Statement := L2MonomialOrthogonality.proof FSCoord.full FSIndex.full

end SectionsLatticeFS

namespace ProjScheme

open SectionsLatticeFS

def fsBundleFull {A : Type u} [CommRing A] {N : ℕ} (n : ℕ) : (self A N).HermitianLineBundle :=
  fsBundle FSContinuousFrame.full FSNormConj.full n

def fsPointMeasuresFull (K : Type) [Field K] [NumberField K] (N : ℕ) : (self (𝓞 K) N).PointMeasures :=
  fsPointMeasures K N FSFullSupport.full FSConjInvariant.full

/- English proof (translation)
A detailed English derivation is pending.
-/
example : (self (𝓞 ℚ) 1).HermitianLineBundle := fsBundleFull 1

/- English proof (translation)
A detailed English derivation is pending.
-/
example : (self (𝓞 ℚ) 1).PointMeasures := fsPointMeasuresFull ℚ 1

end ProjScheme

end

end GroundTheory.Heights₂.Heights
