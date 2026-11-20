import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndLatticeTraceIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEndLatticeTraceIntegral.lean&line=90#L90)
-/
theorem _root_.GlobalTheory.T.end_lattice_trace_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E), SelfDualLat G Λ → Y ∈ endLat Λ → IsIntegral ℤ Y.trace := by
  first | exact @GlobalTheory.LieDisc.trace_integral_main | exact GlobalTheory.LieDisc.trace_integral_main | (intros; apply GlobalTheory.LieDisc.trace_integral_main <;> assumption)
