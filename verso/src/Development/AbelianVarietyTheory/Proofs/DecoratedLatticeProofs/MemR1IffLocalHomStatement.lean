import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemR1IffLocalHom
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FMemR1IffLocalHom.lean&line=137#L137)
-/
theorem _root_.GlobalTheory.T.mem_R1_iff_local_hom : ∀ {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')), c' = c → (∀ i : Fin c, (e (Sum.inr i)).val = M + i.val) → ∀ x : Sp E (M + c') ≃ₗ[E] Sp E (M + c'), x ∈ Loc.R1 E M c' ↔ locHom ι e x ∈ R k A c 1 := by
  first | exact @GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange | exact GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange | (intros; apply GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange <;> assumption)
