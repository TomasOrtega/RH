import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentSubMemOfPowSubMem
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_idempotent_sub_mem_of_pow_sub_mem` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsIdempotentSubMemOfPowSubMem.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.exists_idempotent_sub_mem_of_pow_sub_mem' : ∀ (l : ℕ) [Fact l.Prime] {R : Type} [Ring R] [Algebra ℤ_[l] R] [Module.Finite ℤ_[l] R] (b : R), ∃ E : R, E * E = E ∧ ∀ (M : Submodule ℤ_[l] R) (c : R), (∀ n : ℕ, b ^ (n + 1) - c ∈ M) → E - c ∈ M := by
  first | exact @GlobalTheory.exists_idempotent_sub_mem_of_pow_sub_mem | exact GlobalTheory.exists_idempotent_sub_mem_of_pow_sub_mem | (intros; apply GlobalTheory.exists_idempotent_sub_mem_of_pow_sub_mem <;> assumption)
