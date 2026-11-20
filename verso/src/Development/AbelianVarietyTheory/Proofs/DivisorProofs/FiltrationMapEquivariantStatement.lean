import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationMapEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiltrationMapEquivariant.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.filtration_map_equivariant : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V) (hN : KStable M.act N) (k : ℕ) (Z : Mat R S),
    IsKC Z → ∀ Ψ : (Fin k → NC R S) → N,
      phiN M.act N k (tAct k (restrAct M.act N hN) Z Ψ) = M.act Z (phiN M.act N k Ψ) := by
  first | exact @GlobalTheory.SteepMult.Equivariance.phiN_tAct | exact GlobalTheory.SteepMult.Equivariance.phiN_tAct | (intros; apply GlobalTheory.SteepMult.Equivariance.phiN_tAct <;> assumption)
