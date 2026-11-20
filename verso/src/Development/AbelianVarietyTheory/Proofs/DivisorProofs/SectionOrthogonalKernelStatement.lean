import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionOrthogonalKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SteepMult.section1_mem_orthogonal_ker` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSectionOrthogonalKernel.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.section_orthogonal_kernel : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V), KStable M.act N →
    ∀ (B : N →ₗ⋆[ℂ] N →ₗ[ℂ] ℂ) (k : ℕ) (Ψ : (Fin (k + 1) → NC R S) → N),
    Ψ ∈ ((filt M.act N k).comap (phiN M.act N (k + 1))).orthogonalBilin (formT (k + 1) B) →
    ∀ i g, section1 Ψ i g ∈ (LinearMap.ker (phiN M.act N 1)).orthogonalBilin (formT 1 B) := by
  first | exact @GlobalTheory.SteepMult.section1_mem_orthogonal_ker | exact GlobalTheory.SteepMult.section1_mem_orthogonal_ker | (intros; apply GlobalTheory.SteepMult.section1_mem_orthogonal_ker <;> assumption)
