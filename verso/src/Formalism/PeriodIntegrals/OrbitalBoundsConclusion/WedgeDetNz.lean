import Mathlib
import Formalism.PeriodIntegrals.WedgeDetNz

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
private theorem exists_dual_family_of_linearIndependent_orbital_bounds_conclusion (K V : Type) [Field K] [AddCommGroup V] [Module K V]
    (ρ : ℕ) (z : Fin ρ → V) (hz : LinearIndependent K z) :
    ∃ φ : Fin ρ → (V →ₗ[K] K), (Matrix.of fun i k => φ i (z k)) = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend hz.repr
  refine ⟨fun i => (Finsupp.lapply i).comp g, ?_⟩
  ext i k
  have hk : z k ∈ Submodule.span K (Set.range z) := Submodule.subset_span ⟨k, rfl⟩
  have h1 : g (z k) = hz.repr ⟨z k, hk⟩ := by
    have := congrArg (fun f => f ⟨z k, hk⟩) hg
    simpa using this
  have h2 : hz.repr ⟨z k, hk⟩ = Finsupp.single k 1 := hz.repr_eq_single k _ rfl
  simp only [Matrix.of_apply, LinearMap.comp_apply, Finsupp.lapply_apply, h1, h2,
    Finsupp.single_apply, Matrix.one_apply]
  by_cases h : i = k
  · subst h; simp
  · simp [h, Ne.symm h]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_pairing_det_ne_zero : PI.WedgeDetNz := by
  intro K V _ _ _ ρ z hz
  obtain ⟨φ, hφ⟩ := exists_dual_family_of_linearIndependent_orbital_bounds_conclusion K V ρ z hz
  exact ⟨φ, by rw [hφ, Matrix.det_one]; exact one_ne_zero⟩
