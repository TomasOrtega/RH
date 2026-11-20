import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEndLatticeOfTraceDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMemEndLatticeOfTraceDual.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.mem_end_lattice_of_trace_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E), SelfDualLat G Λ → (∀ Z ∈ endLat Λ, IsIntegral ℤ (Y * Z).trace) → Y ∈ endLat Λ := by
  first | exact @GlobalTheory.LieDisc.mem_endLat_of_trace_integral | exact GlobalTheory.LieDisc.mem_endLat_of_trace_integral | (intros; apply GlobalTheory.LieDisc.mem_endLat_of_trace_integral <;> assumption)
