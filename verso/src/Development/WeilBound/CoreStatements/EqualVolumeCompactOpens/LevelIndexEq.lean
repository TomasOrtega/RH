import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandherrAndLandherrSt
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.SaOpen
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.LocalToAdelic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelBlockOfEq

namespace PositivityTheory.EqVol

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem indexEq : IndexEq := indexEq_of (coSA saOpen) divisible

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem levelIndexEq : LevelIndexEq :=
  levelIndexEq_of indexEq (levelCO hatCompactOpen) levelConj (levelRat hatRat)

end PositivityTheory.EqVol
