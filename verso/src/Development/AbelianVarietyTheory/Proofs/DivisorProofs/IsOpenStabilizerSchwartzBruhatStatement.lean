import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenStabilizerSchwartzBruhat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OmAStab.isOpen_omA_stab` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsOpenStabilizerSchwartzBruhat.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.isOpen_stabilizer_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), IsOpen {h : GL (Fin d) k | GlobalTheory.SplitFlip.omA ν β 1 h Φ = Φ} := by
  first | exact @GlobalTheory.OmAStab.isOpen_omA_stab | exact GlobalTheory.OmAStab.isOpen_omA_stab | (intros; apply GlobalTheory.OmAStab.isOpen_omA_stab <;> assumption)
