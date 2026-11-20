import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfS
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FJordanHolderMultiplicityJacquetEqBorelJacquetOfS.lean&line=124#L124)
-/
theorem _root_.GlobalTheory.T.jordanHolderMultiplicity_jacquet_eq_borelJacquet_of_small : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β n : Type) [Fintype β] [LinearOrder β] [Fintype n] [DecidableEq n] [LinearOrder n] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (f : (Σ j, c j) ≃ n), StrictMono (blk f) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V) (χ : β → kˣ →* ℂˣ), jhMult (ofChar (leviChar c χ)) (jac f π) = jhMult (ofChar (torusChar fun i => χ (blk f i))) (jacB π) := by
  first | exact @GlobalTheory.SmGL.EmptyBlocks.jhMult_jac_eq_jacB | exact GlobalTheory.SmGL.EmptyBlocks.jhMult_jac_eq_jacB | (intros; apply GlobalTheory.SmGL.EmptyBlocks.jhMult_jac_eq_jacB <;> assumption)
