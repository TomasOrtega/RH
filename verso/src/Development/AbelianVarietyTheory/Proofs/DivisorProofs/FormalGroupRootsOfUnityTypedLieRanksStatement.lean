import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupRootsOfUnityTypedLieRanks
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TypedPartSplitPrimes
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.PrimePart.formalGroupTypes | exact GlobalTheory.PrimePart.formalGroupTypes | (intros; apply GlobalTheory.PrimePart.formalGroupTypes <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.formalGroup_rootsOfUnity_typed_lieRanks : GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes.FormalGroupTypes := by
  first | exact @GlobalTheory.PrimePart.formalGroupTypes | exact GlobalTheory.PrimePart.formalGroupTypes | (intros; apply GlobalTheory.PrimePart.formalGroupTypes <;> assumption)
