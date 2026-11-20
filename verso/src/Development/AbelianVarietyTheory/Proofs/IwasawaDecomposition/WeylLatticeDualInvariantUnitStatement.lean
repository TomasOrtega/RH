import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeDualInvariantUnit
import Mathlib
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFunApply
open GlobalTheory.IntegralityCompare
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FWeylLatticeDualInvariantUnit.lean&line=194#L194)
-/
theorem _root_.GlobalTheory.T.weyl_lattice_dual_invariant_unit : ∀ (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ)
    (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]) (F : (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]),
    ‖c‖ = 1 → (∀ τ a b, ‖g τ a b‖ ≤ 1) → (∀ τ, ‖(g τ).det‖ = 1) →
    ((fun y => c * F (fun τ => g τ * y τ)) ∈ WeylLatticeDuality.DelW p T N ν ↔ F ∈ WeylLatticeDuality.DelW p T N ν) := by
  first | exact @GlobalTheory.WeylTensorSubst.subst_mem_iff | exact GlobalTheory.WeylTensorSubst.subst_mem_iff | (intros; apply GlobalTheory.WeylTensorSubst.subst_mem_iff <;> assumption)
