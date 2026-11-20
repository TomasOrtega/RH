import Mathlib

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem sum_mem_span_range_le_of_isSimpleModule :
    ∀ (A P M : Type) [Ring A] [Algebra ℂ A] [AddCommGroup P] [Module A P] [Module ℂ P] [IsScalarTower ℂ A P]
    [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M], IsSimpleModule A P →
    ∀ (n : ℕ) (T : Fin n → P →ₗ[A] M) (ξ : Fin n → P) (N : Submodule A M), ∑ i, T i (ξ i) ∈ N →
      ∑ i, T i (ξ i) ∈ Submodule.span ℂ {x | ∃ (S : P →ₗ[A] M) (y : P), LinearMap.range S ≤ N ∧ x = S y} := by
  intro A P M _ _ _ _ _ _ _ _ _ _ hP n T ξ N hN
  classical
  let F : (Fin n → P) →ₗ[A] M := ∑ i, (T i).comp (LinearMap.proj i)
  have hF : ∀ y, F y = ∑ i, T i (y i) := by
    intro y
    simp [F, LinearMap.sum_apply]
  let D : Submodule A (Fin n → P) := N.comap F
  obtain ⟨C, hC⟩ := exists_isCompl D
  let G : (Fin n → P) →ₗ[A] M := F.comp (D.subtype.comp (D.projectionOnto C hC))
  have hGN : ∀ y, G y ∈ N := fun y => ((D.projectionOnto C hC) y).2
  have hξD : ξ ∈ D := by
    show F ξ ∈ N
    rw [hF]; exact hN
  have hGξ : G ξ = ∑ i, T i (ξ i) := by
    have : D.projectionOnto C hC ξ = ⟨ξ, hξD⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨ξ, hξD⟩
    simp only [G, LinearMap.comp_apply, this, Submodule.subtype_apply]
    exact hF ξ
  rw [← hGξ, ← Finset.univ_sum_single ξ, map_sum]
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ?_
  refine ⟨G.comp (LinearMap.single A (fun _ : Fin n => P) i), ξ i, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact hGN _
  · simp

end GlobalTheory
