import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPres
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

/- English proof (translation)
Introduce `G O LL V _ _ _ _ _ _ _ _ _ _ _ ρ Λ A hA hst μ hμ`. Establish `hinj : Function.Injective (algebraMap O LL)` using `IsFractionRing.injective O LL`. Establish `hmem : ∀ v, v ∈ A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V)) ↔ ∃ a ∈ A, ∃ u ∈ Λ.T, v = a + μ • u`. Introduce `v`. Rewrite using `[Submodule.mem_sup]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, z, ⟨u, hu, rfl⟩, rfl⟩`. Conclude with `⟨a, ha, u, hu, by simp⟩`. Introduce and unpack `⟨a, ha, u, hu, rfl⟩`. Conclude with `⟨a, ha, μ • u, ⟨u, hu, by simp⟩, rfl⟩`.

Establish `hfg : (A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V))).FG` using `hA.sup (Λ.fg.map _)`. Establish `htf : Module.IsTorsionFree O V`. Use `Module.IsTorsionFree.of_smul_eq_zero ?_` and prove the remaining obligations. Introduce `r m h`. Rewrite `h` using `[← algebraMap_smul LL r m, smul_eq_zero]`.

Break down `h with h | h` into its components or cases. Conclude with `Or.inl (hinj (by rw [h, map_zero]))`. Conclude with `Or.inr h`. Use `⟨⟨A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V)), ?_, hfg, ?_, ?_⟩, hmem⟩` and prove the remaining obligations. Introduce `g x hx`.

Take `⟨a, ha, u, hu, rfl⟩` from `(hmem x).1 hx`. Use `(hmem _).2 ⟨ρ g a, hst g a ha, ρ g u, Λ.stable g u hu, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, ← algebraMap_smul LL μ u, map_smul, algebraMap_smul]`. Use `haveI : Module.Finite O ↥(A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V))) := Module.Finite.iff_fg.2 hfg infer_instance`. Rewrite using `[eq_top_iff, ← Λ.span, Submodule.span_le]`.

Introduce `u hu`. Establish `hne : algebraMap O LL μ ≠ 0` using `fun h => hμ (hinj (by rw [h, map_zero]))`. Establish `: u = (algebraMap O LL μ)⁻¹ • (μ • u)`. Rewrite using `[← algebraMap_smul LL μ u, smul_smul, inv_mul_cancel₀ hne, one_smul]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ((hmem _).2 ⟨0, A.zero_mem, u, hu, by simp⟩))`.
-/
theorem _root_.UpperTheory.KN.exists_lattice_eq_add_smul_of_stable_fg_submodule :
    ∀ {G O LL V : Type} [Group G] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field LL] [Algebra O LL] [IsFractionRing O LL]
      [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] (ρ : Representation LL G V)
      (Λ : Lattice (O := O) ρ) (A : Submodule O V), A.FG → (∀ g, ∀ a ∈ A, ρ g a ∈ A) → ∀ μ : O, μ ≠ 0 →
      ∃ L : Lattice (O := O) ρ, ∀ v, v ∈ L.T ↔ ∃ a ∈ A, ∃ u ∈ Λ.T, v = a + μ • u := by
  intro G O LL V _ _ _ _ _ _ _ _ _ _ _ ρ Λ A hA hst μ hμ
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  have hmem : ∀ v, v ∈ A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V)) ↔
      ∃ a ∈ A, ∃ u ∈ Λ.T, v = a + μ • u := by
    intro v
    rw [Submodule.mem_sup]
    constructor
    · rintro ⟨a, ha, z, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨a, ha, u, hu, by simp⟩
    · rintro ⟨a, ha, u, hu, rfl⟩
      exact ⟨a, ha, μ • u, ⟨u, hu, by simp⟩, rfl⟩
  have hfg : (A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V))).FG := hA.sup (Λ.fg.map _)
  have htf : Module.IsTorsionFree O V := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro r m h
    rw [← algebraMap_smul LL r m, smul_eq_zero] at h
    rcases h with h | h
    · exact Or.inl (hinj (by rw [h, map_zero]))
    · exact Or.inr h
  refine ⟨⟨A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V)), ?_, hfg, ?_, ?_⟩, hmem⟩
  · intro g x hx
    obtain ⟨a, ha, u, hu, rfl⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨ρ g a, hst g a ha, ρ g u, Λ.stable g u hu, ?_⟩
    rw [map_add, ← algebraMap_smul LL μ u, map_smul, algebraMap_smul]
  · haveI : Module.Finite O ↥(A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V))) :=
      Module.Finite.iff_fg.2 hfg
    infer_instance
  · rw [eq_top_iff, ← Λ.span, Submodule.span_le]
    intro u hu
    have hne : algebraMap O LL μ ≠ 0 := fun h => hμ (hinj (by rw [h, map_zero]))
    have : u = (algebraMap O LL μ)⁻¹ • (μ • u) := by
      rw [← algebraMap_smul LL μ u, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ((hmem _).2 ⟨0, A.zero_mem, u, hu, by simp⟩))
