import Mathlib
import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom

namespace ReciprocityTheory.MultiplicativeHeights

open scoped TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

A detailed English derivation is pending.
-/
theorem rank_equality_holds : RankStatement := by
  intro K L V _ _ _ _ _ _ W ι v hvW hspan
  have hU : Submodule.span K (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
      (lt_top_iff_ne_top.mpr hne) inferInstance
    let g : L ⊗[K] V →ₗ[L] L := (Algebra.linearMap K L ∘ₗ f).liftBaseChange L
    have hv : ∀ i, f (v i) = 0 := by
      intro i
      have : f (v i) ∈ (Submodule.span K (Set.range v)).map f :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
      rw [hf] at this
      exact (Submodule.mem_bot K).mp this
    have hg : g = 0 := by
      have hle : Submodule.span L (Set.range fun i => (1 : L) ⊗ₜ[K] v i) ≤ LinearMap.ker g := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        simp [g, hv i]
      rw [hspan, top_le_iff, LinearMap.ker_eq_top] at hle
      exact hle
    apply hf0
    ext x
    have h1 : g ((1 : L) ⊗ₜ[K] x) = 0 := by rw [hg]; rfl
    have h2 : g ((1 : L) ⊗ₜ[K] x) = algebraMap K L (f x) := by
      simp [g]
    rw [h2] at h1
    simpa using (FaithfulSMul.algebraMap_injective K L) (h1.trans (map_zero _).symm)
  refine ⟨?_, hU⟩
  rw [eq_top_iff, ← hU, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact hvW i

end ReciprocityTheory.MultiplicativeHeights
