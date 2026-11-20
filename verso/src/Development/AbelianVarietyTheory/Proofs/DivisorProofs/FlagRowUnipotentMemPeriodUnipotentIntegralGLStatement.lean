import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagRowUnipotentMemPeriodUnipotentIntegralGL
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdL
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DiagVol.rowElt_mem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagRowUnipotentMemPeriodUnipotentIntegralGL.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.flagRowUnipotent_mem_periodUnipotent_integralGL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (t : n ⊕ Fin c) (y : n ⊕ Fin c → k), (∀ s, y s ∈ 𝒪[k]) → (∀ s, ¬ ordL c t < ordL c s → y s = 0) → ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c), x.val = 1 + Matrix.of (fun r s => if r = t then y s else 0) := by
  first | exact @GlobalTheory.DiagVol.rowElt_mem | exact GlobalTheory.DiagVol.rowElt_mem | (intros; apply GlobalTheory.DiagVol.rowElt_mem <;> assumption)
