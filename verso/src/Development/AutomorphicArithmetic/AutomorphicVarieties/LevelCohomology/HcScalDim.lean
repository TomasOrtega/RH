import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

/- English proof (translation)
Introduce `k Γ M _ _ _ _ _ ρ γ χ h`. Use `⟨fun σ hσ => ?_, fun σ hσ => ?_, fun hσ => ?_⟩` and prove the remaining obligations. Establish `: LinearMap.ker (ρ σ - 1) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `m _`.

Simplify using `[h, hσ]`. Rewrite using `[this, finrank_top]`. Establish `: LinearMap.ker (ρ σ - 1) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `m hm`.

Rewrite using `[Submodule.mem_bot]`. Break down `hσ with h0 | h0` into its components or cases. Conclude with `(finrank_zero_iff_forall_zero.mp h0) m`. Establish `h1 : ((γ σ : k) - 1) • m = 0`. Rewrite `hm` using `[LinearMap.mem_ker, LinearMap.sub_apply, h]`.

Rewrite using `[sub_smul, one_smul]`. Conclude with `hm`. Break down `smul_eq_zero.mp h1 with h2 | h2` into its components or cases. Conclude with `absurd (Units.ext (sub_eq_zero.mp h2)) h0`. Conclude with `h2`.

Rewrite using `[this, finrank_bot]`. Establish `: Loc.H0dual χ ρ = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `f hf`. Rewrite using `[Submodule.mem_bot]`.

Use extensionality with `m`. Break down `hσ with h0 | ⟨g, hg⟩` into its components or cases. Rewrite using `[(finrank_zero_iff_forall_zero.mp h0) m]`. Simplify using the standard rewrite rules. Establish `h1` using `hf g m`.

Rewrite `h1` using `[h, map_smul, smul_eq_mul]`. Establish `h2 : ((γ g : k) - χ g) * f m = 0`. Rewrite using `[sub_mul, h1]`. Simplify using the standard rewrite rules. Break down `mul_eq_zero.mp h2 with h3 | h3` into its components or cases.

Conclude with `absurd (Units.ext (sub_eq_zero.mp h3)) hg`. Simplify using `using h3`. Rewrite using `[this, finrank_bot]`.
-/
theorem UpperTheory.V.X.scalDim :
    ∀ {k Γ M : Type} [Field k] [Group Γ] [AddCommGroup M] [Module k M] [Module.Finite k M] (ρ : Representation k Γ M) (γ χ : Γ →* kˣ), (∀ g m, ρ g m = (γ g : k) • m) → (∀ σ, γ σ = 1 → finrank k (LinearMap.ker (ρ σ - 1)) = finrank k M) ∧ (∀ σ, (finrank k M = 0 ∨ γ σ ≠ 1) → finrank k (LinearMap.ker (ρ σ - 1)) = 0) ∧ ((finrank k M = 0 ∨ ∃ g, γ g ≠ χ g) → finrank k (Loc.H0dual χ ρ) = 0) := by
  intro k Γ M _ _ _ _ _ ρ γ χ h
  refine ⟨fun σ hσ => ?_, fun σ hσ => ?_, fun hσ => ?_⟩
  · have : LinearMap.ker (ρ σ - 1) = ⊤ := by
      rw [eq_top_iff]
      intro m _
      simp [h, hσ]
    rw [this, finrank_top]
  · have : LinearMap.ker (ρ σ - 1) = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      rw [Submodule.mem_bot]
      rcases hσ with h0 | h0
      · exact (finrank_zero_iff_forall_zero.mp h0) m
      · have h1 : ((γ σ : k) - 1) • m = 0 := by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, h] at hm
          rw [sub_smul, one_smul]
          exact hm
        rcases smul_eq_zero.mp h1 with h2 | h2
        · exact absurd (Units.ext (sub_eq_zero.mp h2)) h0
        · exact h2
    rw [this, finrank_bot]
  · have : Loc.H0dual χ ρ = ⊥ := by
      rw [eq_bot_iff]
      intro f hf
      rw [Submodule.mem_bot]
      ext m
      rcases hσ with h0 | ⟨g, hg⟩
      · rw [(finrank_zero_iff_forall_zero.mp h0) m]; simp
      · have h1 := hf g m
        rw [h, map_smul, smul_eq_mul] at h1
        have h2 : ((γ g : k) - χ g) * f m = 0 := by
          rw [sub_mul, h1]; simp
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd (Units.ext (sub_eq_zero.mp h3)) hg
        · simpa using h3
    rw [this, finrank_bot]
