import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFormOrthogonalComplement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryFormOrthogonalComplement.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.unitary_form_orthogonal_complement : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), IsUnitary actW B →
    ∀ U : Submodule ℂ W, KStable actW U → KStable actW (U.orthogonalBilin B) ∧ U ⊔ U.orthogonalBilin B = ⊤ := by
  first | exact @GlobalTheory.SteepMult.orthogonal_kstable_compl | exact GlobalTheory.SteepMult.orthogonal_kstable_compl | (intros; apply GlobalTheory.SteepMult.orthogonal_kstable_compl <;> assumption)
