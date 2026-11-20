import Development.EtaleCohomology.EtaleSheaves.LeafVanStalk
import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling.LeafKill2Of

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.StalkVanishing
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem goal_of (hN : LateralTheory.E.SecondDegreeKilling.Nbhd.LeafKillNbhd) : LateralTheory.E.LeafVan0Pf.LeafVanStalk := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp U m hsub y
  refine LateralTheory.E.SecondDegreeKilling.Nbhd.killPt_of hN hH q k hq i toK ι p hp U m y ?_
  intro A _ t hA
  have := hsub A t hA
  exact Subsingleton.elim _ _

end LateralTheory.E.StalkVanishing
