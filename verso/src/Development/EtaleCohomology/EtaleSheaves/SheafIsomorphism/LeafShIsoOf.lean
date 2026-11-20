import Development.EtaleCohomology.EtaleSheaves.SheafIsomorphism.LeafSheafIsoOf

namespace LateralTheory.E.LeafShIsoPf.Glue
open LateralTheory.E.LeafDegCut LateralTheory.E.LeafShIsoPf LateralTheory.E.LeafShIsoPf.Sh

/- English proof (translation)
The claim follows from `LateralTheory.E.LeafShIsoPf.LeafShIso_of hL hK (LeafSheafIso_of hR)`.
-/
theorem LeafShIso_of (hL : EtaleDerivedDegreeZeroHomologyLocallyLifts) (hK : EtaleDerivedDegreeZeroHomologyKernelLocallyVanishes) (hR : LeafSecRep) : LeafShIso :=
  LateralTheory.E.LeafShIsoPf.LeafShIso_of hL hK (LeafSheafIso_of hR)

end LateralTheory.E.LeafShIsoPf.Glue
