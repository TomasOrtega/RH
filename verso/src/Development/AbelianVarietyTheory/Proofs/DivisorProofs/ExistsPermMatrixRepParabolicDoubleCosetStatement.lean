import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermMatrixRepParabolicDoubleCoset
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColReduced
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinGL.Bruhat.exists_perm_rep_blockTri` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPermMatrixRepParabolicDoubleCoset.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_permMatrix_rep_parabolic_doubleCoset : ∀ (F : Type) [Field F] (r : ℕ) (b b' : Fin r → ℕ), Monotone b → Monotone b' → ∀ g : GL (Fin r) F, ∃ (w : Equiv.Perm (Fin r)) (p' : blockTri (κ := F) b') (p : blockTri (κ := F) b), g = (p' : GL (Fin r) F) * permGL F w * (p : GL (Fin r) F) := by
  first | exact @GlobalTheory.FinGL.Bruhat.exists_perm_rep_blockTri | exact GlobalTheory.FinGL.Bruhat.exists_perm_rep_blockTri | (intros; apply GlobalTheory.FinGL.Bruhat.exists_perm_rep_blockTri <;> assumption)
