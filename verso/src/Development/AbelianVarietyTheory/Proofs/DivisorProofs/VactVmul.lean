import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPTorsionIsModularFamilyStatement

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFamGL

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem vact_vmul (N : ℕ) (D α : GL (Fin 2) (ZMod N)) (e : Fin 2 → ZMod N) (γ : SL(2, ℤ)) :
    vact N (vmul e (α * D)) γ = vmul e (gact N D α γ * D) := by
  have h : gact N D α γ * D = α * D * redGL N γ := by
    simp only [gact]
    group
  rw [h]
  simp only [vact, vmul, Units.val_mul, Matrix.vecMul_vecMul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem main : ∀ (N : ℕ) [NeZero N] (D : GL (Fin 2) (ZMod N)) (e : Fin 2 → ZMod N), IsFam (gact N D) 2 (fun α => wp N (vmul e (α * D))) ∧ IsFam (gact N D) 3 (fun α => wpd N (vmul e (α * D))) := by
  intro N _ D e
  obtain ⟨h2, h3⟩ := GlobalTheory.T.weierstrassP_torsion_isModularFamily N
  refine ⟨fun α γ => ?_, fun α γ => ?_⟩
  · have h := h2 (vmul e (α * D)) γ
    rw [vact_vmul] at h
    exact h
  · have h := h3 (vmul e (α * D)) γ
    rw [vact_vmul] at h
    exact h

end GlobalTheory.WpFamGL
