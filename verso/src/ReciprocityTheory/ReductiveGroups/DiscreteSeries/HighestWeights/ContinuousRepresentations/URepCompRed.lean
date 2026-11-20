import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.RelOpCurve
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.Stable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.EntryEqZeroOfComm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.Decomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepHom
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRedOf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.FromHC

namespace ReciprocityTheory.ChartRestriction.DS.HW

/- English proof (translation)
The claim follows from `kRepPiece_of kRepRel kRepStable`.
-/
theorem kRepPiece : KRepPieceStatement := kRepPiece_of kRepRel kRepStable

/- English proof (translation)
The claim follows from `compRed_of kRepRel kRepStable kRepPiece`.
-/
theorem compRed : CompRedStatement := compRed_of kRepRel kRepStable kRepPiece

/- English proof (translation)
The claim follows from `derivExists_of derivExists_allPos`.
-/
theorem derivExists : DerivExistsStatement := derivExists_of derivExists_allPos

/- English proof (translation)
The claim follows from `uRepCompRed_of uRepHom derivExists kRepRel compRed`.
-/
theorem uRepCompRed : URepCompRedStatement := uRepCompRed_of uRepHom derivExists kRepRel compRed

end ReciprocityTheory.ChartRestriction.DS.HW
