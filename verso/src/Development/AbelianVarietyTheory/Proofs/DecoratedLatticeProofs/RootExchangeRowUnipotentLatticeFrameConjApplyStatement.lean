import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeRowUnipotentLatticeFrameConjApply
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.typeFrame_conj_symm_rowE_apply` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FRootExchangeRowUnipotentLatticeFrameConjApply.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.rootExchangeRowUnipotent_latticeFrame_conj_apply : ∀ (k : Type) [Field k] (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (ϖ : kˣ) (j c l : ℕ) (h : j + c = l) (p : ℕ) (hp : p < c) (u : XIx κ t j → k) (a b : Ix (κ ⊕ Fin l) t j), ((typeFrame ϖ (stdOrd κ t j c h)).conj.symm (rowE c (p + 1) u)).val a b = (1 : Matrix (Ix (κ ⊕ Fin l) t j) (Ix (κ ⊕ Fin l) t j) k) a b + if a = Sum.inl (Sum.inr ⟨p, by omega⟩) then Sum.elim (fun y => ((ϖ : k) ^ (p + 1))⁻¹ * u y) (fun _ => 0) (stdOrd κ t j c h b) else 0 := by
  first | exact @GlobalTheory.typeFrame_conj_symm_rowE_apply | exact GlobalTheory.typeFrame_conj_symm_rowE_apply | (intros; apply GlobalTheory.typeFrame_conj_symm_rowE_apply <;> assumption)
