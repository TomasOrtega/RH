import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Submodule

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Substitute using the available equality. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem quotient_span_bijective_second_basis {R : Type} [CommRing R] (v : Fin 2 → R) (hv : v 0 = 1) :
    Function.Bijective (fun r : R => r • (span R {v}).mkQ (eps R 1)) := by
  constructor
  · intro r s h
    simp only at h
    rw [← map_smul, ← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq,
      ← sub_smul, mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp [eps, hv] at h0 h1
    subst h0
    simp at h1
    exact sub_eq_zero.mp h1.symm
  · intro q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    refine ⟨x 1 - x 0 * v 1, ?_⟩
    simp only
    rw [← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq, mem_span_singleton]
    refine ⟨-x 0, ?_⟩
    ext k
    fin_cases k <;> simp [eps, hv]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Substitute using the available equality. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem quotient_span_bijective_first_basis {R : Type} [CommRing R] (v : Fin 2 → R) (hv : v 1 = 1) :
    Function.Bijective (fun r : R => r • (span R {v}).mkQ (eps R 0)) := by
  constructor
  · intro r s h
    simp only at h
    rw [← map_smul, ← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq,
      ← sub_smul, mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp [eps, hv] at h0 h1
    subst h1
    simp at h0
    exact sub_eq_zero.mp h0.symm
  · intro q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    refine ⟨x 0 - x 1 * v 0, ?_⟩
    simp only
    rw [← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq, mem_span_singleton]
    refine ⟨-x 1, ?_⟩
    ext k
    fin_cases k <;> simp [eps, hv]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem SectionLocalEquation.proof : SectionLocalEquation.Statement := by
  intro R _ a₁ a₂ b₁ b₂
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact quotient_span_bijective_second_basis _ (by simp [eps])
  · rw [← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq, mem_span_singleton]
    refine ⟨1, ?_⟩
    ext k
    fin_cases k <;> simp [eps]
  · exact quotient_span_bijective_first_basis _ (by simp [eps])
  · rw [← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq, mem_span_singleton]
    refine ⟨1, ?_⟩
    ext k
    fin_cases k <;> simp [eps]
  · rw [← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq, mem_span_singleton]
    refine ⟨a₁, ?_⟩
    ext k
    fin_cases k <;> simp [eps]

end GroundTheory.Heights₂.Heights.FlagBundles
