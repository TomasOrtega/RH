import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvOf
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiClos

namespace DiscreteGroups.T1.G

/- English proof (translation)
The claim follows from `piInv_of piClosureInv`.
-/
theorem piInv : PositivityTheory.Rg.BcB.Desc.PiInv := piInv_of piClosureInv

end DiscreteGroups.T1.G
