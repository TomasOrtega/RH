import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricUnipotentMemOfFlagBasisDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagDual.unipSym_of_dual` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSymmetricUnipotentMemOfFlagBasisDual.lean&line=101#L101)
-/
theorem _root_.GlobalTheory.T.symmetricUnipotent_mem_of_flagBasisDual : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ M M' : GL (Fin n) K, (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k → M ∈ unipSym K n ρ k → M' ∈ unipSym K n ρ k := by
  first | exact @GlobalTheory.FlagDual.unipSym_of_dual | exact GlobalTheory.FlagDual.unipSym_of_dual | (intros; apply GlobalTheory.FlagDual.unipSym_of_dual <;> assumption)
