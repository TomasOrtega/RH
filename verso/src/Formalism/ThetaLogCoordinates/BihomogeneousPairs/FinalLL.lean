import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.PstScalMem
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.PlusOp
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.LatticeLinearHolds
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.StepTie
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.StepPlus
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.LevelLatticeOf

namespace Formalism.InvariantFactorPaths.KP.Top

open Formalism.InvariantFactorPaths.KP.LL

/- English proof (translation)
The claim follows from `pair_induction_holds`.
-/
theorem pairStep : PairStep := pair_induction_holds
/- English proof (translation)
The claim follows from `lattice_equal_holds`.
-/
theorem latTie : LatTie := lattice_equal_holds
/- English proof (translation)
The claim follows from `lattice_plus_holds`.
-/
theorem latPlus : LatPlus := lattice_plus_holds
/- English proof (translation)
The claim follows from `lattice_linear_holds`.
-/
theorem plLin : PLLin := lattice_linear_holds
/- English proof (translation)
The claim follows from `comm_lattice_holds`.
-/
theorem commPL : CommPL := comm_lattice_holds
/- English proof (translation)
The claim follows from `param_lattice_holds`.
-/
theorem paramPL : ParamPL := param_lattice_holds
/- English proof (translation)
The claim follows from `middle_top_holds`.
-/
theorem midTop : MidTop := middle_top_holds
/- English proof (translation)
The claim follows from `middle_p_eq_holds`.
-/
theorem midPEq : MidPEq := middle_p_eq_holds
/- English proof (translation)
The claim follows from `StepTie_of pairStep latTie plLin commPL paramPL`.
-/
theorem stepTie : JoinCondition := StepTie_of pairStep latTie plLin commPL paramPL
/- English proof (translation)
The claim follows from `StepPlus_of pairStep latPlus plLin commPL paramPL`.
-/
theorem stepPlus : PlusCondition := StepPlus_of pairStep latPlus plLin commPL paramPL
/- English proof (translation)
The claim follows from `LevelLattice_of midTop midPEq stepTie stepPlus`.
-/
theorem levelLattice : Formalism.GM.M.LevelLattice := LevelLattice_of midTop midPEq stepTie stepPlus

end Formalism.InvariantFactorPaths.KP.Top
