import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.ThetaFixOfOfMult
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.IsDiscreteOfNorm
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.UnitOf
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.CuspidalMultiplicityOne

namespace DiscreteGroups.T1.G

/- English proof (translation)
The claim follows from `thetaFixOf_of_mult PositivityTheory.jumpWindows.cuspidalMultiplicityOne`.
-/
theorem thetaFixOf : PositivityTheory.Rg.BcB.Desc.ThetaFixOf := thetaFixOf_of_mult PositivityTheory.jumpWindows.cuspidalMultiplicityOne

/- English proof (translation)
The claim follows from `oneEx_of thetaFixOf DiscreteGroups.T1.Desc.unitOf hA`.
-/
theorem oneEx_of_asc (hA : PositivityTheory.Rg.BcB.F.Rig.ThetaOfAsc) : PositivityTheory.Rg.BcB.Desc.OneEx :=
  oneEx_of thetaFixOf DiscreteGroups.T1.Desc.unitOf hA

end DiscreteGroups.T1.G
