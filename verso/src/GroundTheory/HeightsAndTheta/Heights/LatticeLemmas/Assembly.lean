import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PBaseChange
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSublattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLatticeOfLocalisations
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalChange
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PNormComparison
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PDiagonalChange
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PExactSequence
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PChainSum
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PHadamard
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PHadamardQuotient
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PHadamardMean
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PHadamardMeanQuotient
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PGaussNormBasic
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSchwartzZippelPerVariable
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PRootsOfUnityValuation
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PHeightOfPoint
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PHeightOfCycle
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSphereLawUnitary
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSpherePhase
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSphereProjectionLaw
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PPointwiseLelong
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v w

namespace LatticeLemmas

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BaseChange.full : BaseChange.Statement := BaseChange.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Sublattice.full : Sublattice.Statement := Sublattice.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LatticeOfLocalisations.full : LatticeOfLocalisations.Statement :=
  LatticeOfLocalisations.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LocalChange.full_of_localIndex (h : LocalIndex.Statement.{u, v}) :
    LocalChange.Statement.{u, v} :=
  LocalChange.proof Sublattice.full h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem NormComparison.full : NormComparison.Statement := NormComparison.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DiagonalChange.full : DiagonalChange.Statement := DiagonalChange.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ExactSequence.full : ExactSequence.Statement := ExactSequence.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ChainSum.full : ChainSum.Statement.{u, v} := ChainSum.proof ExactSequence.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Hadamard.full : Hadamard.Statement.{u, v, w} := Hadamard.proof Sublattice.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HadamardQuotient.full : HadamardQuotient.Statement.{u, v, w} :=
  HadamardQuotient.proof Hadamard.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HadamardMean.full : HadamardMean.Statement.{u, v, w} := HadamardMean.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HadamardMeanQuotient.full : HadamardMeanQuotient.Statement.{u, v, w} :=
  HadamardMeanQuotient.proof HadamardMean.full

end LatticeLemmas

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GaussNormBasic.full : GaussNormBasic.Statement := GaussNormBasic.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchwartzZippelPerVariable.full : SchwartzZippelPerVariable.Statement :=
  SchwartzZippelPerVariable.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RootsOfUnityValuation.full : RootsOfUnityValuation.Statement :=
  RootsOfUnityValuation.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HeightOfPoint.full : HeightOfPoint.Statement := HeightOfPoint.proof GaussNormBasic.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HeightOfCycle.full_of_fibreMahlerForms (h : FibreMahlerForms.Statement) :
    HeightOfCycle.Statement :=
  HeightOfCycle.proof HeightOfPoint.full h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SphereLawUnitary.full : SphereLawUnitary.Statement := SphereLawUnitary.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SpherePhase.full_of_sphereLawBasic (hb : SphereLawBasic.Statement) :
    SpherePhase.Statement :=
  SpherePhase.proof hb SphereLawUnitary.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SphereProjectionLaw.full_of (hb : SphereLawBasic.Statement)
    (hc : SphereLawFirstCoord.Statement) : SphereProjectionLaw.Statement :=
  SphereProjectionLaw.proof hb SphereLawUnitary.full hc (SpherePhase.full_of_sphereLawBasic hb)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PointwiseLelong.full_of (hb : SphereLawBasic.Statement)
    (hc : SphereLawFirstCoord.Statement) : PointwiseLelong.Statement :=
  PointwiseLelong.proof (SphereProjectionLaw.full_of hb hc)

end GroundTheory.Heights₂.Heights
