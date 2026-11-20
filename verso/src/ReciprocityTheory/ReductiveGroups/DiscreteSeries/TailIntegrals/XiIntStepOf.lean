import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiRNonneg
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HermitianLiftIdentities

namespace ReciprocityTheory.ChartRestriction.DS.Xi

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem iw : IW := iwB

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem det_of (hB2 : InductiveHeisenbergInputs) : DET := detH hB2

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem coefStep_of (hB2 : InductiveHeisenbergInputs) (hT : TBoth) (hD : DET) : CoefStep := CB.coefStepC hB2 hT hD

end ReciprocityTheory.ChartRestriction.DS.Xi
