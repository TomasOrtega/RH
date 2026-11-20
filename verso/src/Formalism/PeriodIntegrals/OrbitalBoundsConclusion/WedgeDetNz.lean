import Mathlib
import Formalism.PeriodIntegrals.WedgeDetNz

/- English proof (translation)
Take `⟨g, hg⟩` from `LinearMap.exists_extend hz.repr`. Use `⟨fun i => (Finsupp.lapply i).comp g, ?_⟩` and prove the remaining obligations. Use extensionality with `i k`. Establish `hk : z k ∈ Submodule.span K (Set.range z)` using `Submodule.subset_span ⟨k, rfl⟩`. Establish `h1 : g (z k) = hz.repr ⟨z k, hk⟩`.

Use `congrArg (fun f => f ⟨z k, hk⟩) hg` as an intermediate fact. Simplify using `using this`. Establish `h2 : hz.repr ⟨z k, hk⟩ = Finsupp.single k 1` using `hz.repr_eq_single k _ rfl`. Simplify using `only [Matrix.of_apply, LinearMap.comp_apply, Finsupp.lapply_apply, h1, h2, Finsupp.single_apply, Matrix.one_apply]`. Distinguish the cases in `h : i = k`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`.
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
Introduce `K V _ _ _ ρ z hz`. Take `⟨φ, hφ⟩` from `exists_dual_family_of_linearIndependent_orbital_bounds_conclusion K V ρ z hz`. Conclude with `⟨φ, by rw [hφ, Matrix.det_one]; exact one_ne_zero⟩`.
-/
theorem exists_pairing_det_ne_zero : PI.WedgeDetNz := by
  intro K V _ _ _ ρ z hz
  obtain ⟨φ, hφ⟩ := exists_dual_family_of_linearIndependent_orbital_bounds_conclusion K V ρ z hz
  exact ⟨φ, by rw [hφ, Matrix.det_one]; exact one_ne_zero⟩
