import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationStepFromSectionKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PositionRel.position_rel` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiltrationStepFromSectionKernel.lean&line=198#L198)
-/
theorem _root_.GlobalTheory.T.filtration_step_from_section_kernel : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V), KStable M.act N → ∀ (k : ℕ) (i : Fin (k + 1))
    (Ψ : (Fin (k + 1) → NC R S) → N), (∀ g, phiN M.act N 1 (section1 Ψ i g) = 0) →
    phiN M.act N (k + 1) Ψ ∈ filt M.act N k := by
  first | exact @GlobalTheory.PositionRel.position_rel | exact GlobalTheory.PositionRel.position_rel | (intros; apply GlobalTheory.PositionRel.position_rel <;> assumption)
