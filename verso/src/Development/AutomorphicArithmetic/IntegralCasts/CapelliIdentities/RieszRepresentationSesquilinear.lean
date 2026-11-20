import Mathlib

/- English proof (translation)
Introduce `V _ _ _ B _ hpos L`. Set `e` to `Module.finBasis ℂ V`. Set `Φ : V →ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ)` to `{ toFun := fun u i => B u (e i) map_add' := fun u v => by funext i; simp map_smul' := fun c u => by funext i; simp }`. Establish `hinj : Function.Injective Φ`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `u hu`. Establish `h0 : B u = 0` using `e.ext fun i => congrFun hu i`. Assume the negation of the conclusion as `hne`. Establish `h` using `hpos u hne`. Rewrite `h` using `[h0]`.

Simplify using `at h`. Establish `hsurj : Function.Surjective Φ` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj`. Take `⟨u, hu⟩` from `hsurj fun i => L (e i)`. Establish `hL : L = B u` using `e.ext fun i => (congrFun hu i).symm`. Conclude with `⟨u, fun b => by rw [hL]⟩`.
-/
theorem UpperTheory.Reformulated.B.Qh51.riesz_representation_sesquilinear :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] [FiniteDimensional ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ (a b : V), ((B : V → V →ₗ⋆[ℂ] ℂ) b : V → ℂ) a = Star.star (((B : V → V →ₗ⋆[ℂ] ℂ) a : V → ℂ) b)) →
      (∀ (a : V), a ≠ (0 : V) → (0 : ℝ) < (((B : V → V →ₗ⋆[ℂ] ℂ) a : V → ℂ) a).re) →
        ∀ (L : V →ₗ⋆[ℂ] ℂ), ∃ (u : V), ∀ (b : V), (L : V → ℂ) b = ((B : V → V →ₗ⋆[ℂ] ℂ) u : V → ℂ) b := by
  intro V _ _ _ B _ hpos L
  let e := Module.finBasis ℂ V
  let Φ : V →ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) :=
    { toFun := fun u i => B u (e i)
      map_add' := fun u v => by funext i; simp
      map_smul' := fun c u => by funext i; simp }
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have h0 : B u = 0 := e.ext fun i => congrFun hu i
    by_contra hne
    have h := hpos u hne
    rw [h0] at h
    simp at h
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨u, hu⟩ := hsurj fun i => L (e i)
  have hL : L = B u := e.ext fun i => (congrFun hu i).symm
  exact ⟨u, fun b => by rw [hL]⟩
