import Development.EtaleCohomology.EtaleSheaves.SpreadingOutLocallyQuasiFinite

namespace LateralTheory.E.LeafSpreadLQFMap_vtuPfG

open LateralTheory.E.SpreadingOutLocallyQuasiFinite in

/- English proof (translation)
The claim follows from `LateralTheory.E.SpreadingOutLocallyQuasiFinite.LeafSpreadLQFMap_of quasi_finite_at_base_change_of_finite_type hD hO`.
-/
theorem LeafSpreadLQFMap_of (hD : LeafQFAtDescend) (hO : LeafOpenSpread) :
    LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap :=
  LateralTheory.E.SpreadingOutLocallyQuasiFinite.LeafSpreadLQFMap_of quasi_finite_at_base_change_of_finite_type hD hO

end LateralTheory.E.LeafSpreadLQFMap_vtuPfG
