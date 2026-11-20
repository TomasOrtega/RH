import Development.WeilBound.CoreStatements.VolumeEquality.BallVolMoeb
import Development.WeilBound.CoreStatements.VolumeEquality.BallVolStdZ
import Development.WeilBound.CoreStatements.VolumeEquality.BallVolModel
import Development.WeilBound.CoreStatements.VolumeEquality.BallVolArith
import Development.WeilBound.CoreStatements.VolumeEquality.BallVolLevel
import Development.WeilBound.CoreStatements.VolumeEquality.BallVolFam
import Development.WeilBound.CoreStatements.VolumeEquality.BallVolRed

namespace SheetDecomposition

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem famVol : FamVol := famVol_of moebVol (stdModel_of stdZ) arithIdx levelDict

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ballVolEq : BallVolEq := ballVolEq_of famVol

end SheetDecomposition
