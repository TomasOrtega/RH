import Development.EtaleCohomology.EtaleSheaves.LeafConsPfB

namespace LateralTheory.E.LeafConsPfC

/- English proof (translation)
The claim follows from `LateralTheory.E.LeafConsPf.LeafCons_of hL LateralTheory.E.LeafConsPfB.LeafGlob_pf`.
-/
theorem LeafCons_of (hL : LateralTheory.E.LeafConsPf.LeafLoc) : LateralTheory.E.EtaleTopologySheaves.LeafCons :=
  LateralTheory.E.LeafConsPf.LeafCons_of hL LateralTheory.E.LeafConsPfB.LeafGlob_pf

end LateralTheory.E.LeafConsPfC
