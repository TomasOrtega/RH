import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.PstScalMem
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.PlusOp
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.LatticeLinearHolds
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.StepTie
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.StepPlus
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.LevelLatticeOf

namespace Formalism.InvariantFactorPaths.KP.Top

open Formalism.InvariantFactorPaths.KP.LL

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pairStep : PairStep := pair_induction_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem latTie : LatTie := lattice_equal_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem latPlus : LatPlus := lattice_plus_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem plLin : PLLin := lattice_linear_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem commPL : CommPL := comm_lattice_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem paramPL : ParamPL := param_lattice_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem midTop : MidTop := middle_top_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem midPEq : MidPEq := middle_p_eq_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stepTie : JoinCondition := StepTie_of pairStep latTie plLin commPL paramPL
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stepPlus : PlusCondition := StepPlus_of pairStep latPlus plLin commPL paramPL
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem levelLattice : Formalism.GM.M.LevelLattice := LevelLattice_of midTop midPEq stepTie stepPlus

end Formalism.InvariantFactorPaths.KP.Top
