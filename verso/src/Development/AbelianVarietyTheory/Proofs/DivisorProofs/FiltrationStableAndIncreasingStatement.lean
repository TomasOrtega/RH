import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationStableAndIncreasing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiltrationStableAndIncreasing.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.filtration_stable_and_increasing : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V), KStable M.act N → ∀ k : ℕ,
    KStable M.act (filt M.act N k) ∧
    filt M.act N (k + 1) = filt M.act N k ⊔ LinearMap.range (phiN M.act N (k + 1)) ∧ filt M.act N 0 ≤ N := by
  first | exact @GlobalTheory.SteepMult.Filt.filt_basic | exact GlobalTheory.SteepMult.Filt.filt_basic | (intros; apply GlobalTheory.SteepMult.Filt.filt_basic <;> assumption)
