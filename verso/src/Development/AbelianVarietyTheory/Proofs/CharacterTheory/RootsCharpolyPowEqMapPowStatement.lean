import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootsCharpolyPowEqMapPow
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FRootsCharpolyPowEqMapPow.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.roots_charpoly_pow_eq_map_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ) (M : Matrix (Fin n) (Fin n) k), (Matrix.charpoly (M ^ r)).roots = (Matrix.charpoly M).roots.map (· ^ r) := by
  first | exact @GlobalTheory.CharpolyPow.roots_charpoly_pow | exact GlobalTheory.CharpolyPow.roots_charpoly_pow | (intros; apply GlobalTheory.CharpolyPow.roots_charpoly_pow <;> assumption)
