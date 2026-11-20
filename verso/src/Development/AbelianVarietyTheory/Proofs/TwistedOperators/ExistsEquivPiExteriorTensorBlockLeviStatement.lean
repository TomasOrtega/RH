import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsEquivPiExteriorTensorBlockLevi.lean&line=334#L334)
-/
theorem _root_.GlobalTheory.T.exists_equiv_piExteriorTensor_blockLevi : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (τ : GlobalTheory.SmGL.IrrRep (GlobalTheory.SmGL.Levi k c)), ∃ s : ∀ j, GlobalTheory.SmGL.IrrRep (GL (c j) k), Nonempty (τ.ρ.Equiv (GlobalTheory.SmGL.piTensor fun j => (s j).ρ)) := by
  first | exact @GlobalTheory.LeviFactor.exists_equiv_piTensor_levi | exact GlobalTheory.LeviFactor.exists_equiv_piTensor_levi | (intros; apply GlobalTheory.LeviFactor.exists_equiv_piTensor_levi <;> assumption)
