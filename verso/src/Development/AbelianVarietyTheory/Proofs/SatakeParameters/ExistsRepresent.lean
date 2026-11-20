import Mathlib

namespace GlobalTheory.ExistsRepresentation

/- English proof (translation)
Set `b` to `Module.finBasis ℂ W`. Set `Φ : W →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ)` to `{ toFun := fun u i => Bf (u : V) (b i : V) map_add' := by`. Introduce `u u'`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Use the proof step `map_smul' := by`. Introduce `c u`. Use function extensionality and compare the values at `i`. Simplify using `}`. Establish `hinj : Function.Injective Φ`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `u hu`. Establish `hall : ∀ w : W, Bf (u : V) (w : V) = 0`. Introduce `w`. Rewrite using `[← b.sum_repr w]`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smulₛₗ]`. Use `Finset.sum_eq_zero (fun i _ => ?_)` and prove the remaining obligations. Establish `h0` using `congrFun hu i`. Simplify using `only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0`. Simplify using `[h0]`.

Assume the negation of the conclusion as `hne`. Establish `hne' : (u : V) ≠ 0` using `by simpa using hne`. Establish `h1` using `hpos _ hne'`. Rewrite `h1` using `[hall u]`. Simplify using `at h1`.

Establish `hsurj : Function.Surjective Φ` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj`. Take `⟨u, hu⟩` from `hsurj (fun i => L (b i : V))`. Use `⟨u, u.2, fun w hw => ?_⟩` and prove the remaining obligations. Establish `hwsum : w = ∑ i, (b.repr ⟨w, hw⟩ i) • (b i : V)`. Establish `h2` using `congrArg Subtype.val (b.sum_repr ⟨w, hw⟩)`.

Rewrite `h2` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at h2`. Conclude with `h2.symm`. Rewrite using `[hwsum]`. Simplify using `only [map_sum, map_smulₛₗ]`.

Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Establish `h3` using `congrFun hu i`. Simplify using `only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at h3`. Rewrite using `[h3]`.
-/
theorem exists_represent {V : Type} [AddCommGroup V] [Module ℂ V]
    (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hpos : ∀ v : V, v ≠ 0 → (0 : ℝ) < (Bf v v).re)
    (L : V →ₗ⋆[ℂ] ℂ) (W : Submodule ℂ V) [FiniteDimensional ℂ W] :
    ∃ u ∈ W, ∀ w ∈ W, L w = Bf u w := by
  classical
  let b := Module.finBasis ℂ W
  let Φ : W →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    { toFun := fun u i => Bf (u : V) (b i : V)
      map_add' := by
        intro u u'
        funext i
        simp
      map_smul' := by
        intro c u
        funext i
        simp }
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have hall : ∀ w : W, Bf (u : V) (w : V) = 0 := by
      intro w
      rw [← b.sum_repr w]
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smulₛₗ]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have h0 := congrFun hu i
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
      simp [h0]
    by_contra hne
    have hne' : (u : V) ≠ 0 := by simpa using hne
    have h1 := hpos _ hne'
    rw [hall u] at h1
    simp at h1
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
  obtain ⟨u, hu⟩ := hsurj (fun i => L (b i : V))
  refine ⟨u, u.2, fun w hw => ?_⟩
  have hwsum : w = ∑ i, (b.repr ⟨w, hw⟩ i) • (b i : V) := by
    have h2 := congrArg Subtype.val (b.sum_repr ⟨w, hw⟩)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    exact h2.symm
  rw [hwsum]
  simp only [map_sum, map_smulₛₗ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h3 := congrFun hu i
  simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at h3
  rw [h3]

end GlobalTheory.ExistsRepresentation
