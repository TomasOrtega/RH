import Mathlib

open scoped ComplexConjugate

namespace GlobalTheory

/- English proof (translation)
Introduce `A C _ _ _ _ _ ipA ip _hsym hpos io u`. Set `g : C →ₗ[ℝ] (C →ₗ[ℂ] ℂ)` to `{ toFun := fun x => ip.flip x map_add' := fun x y => by simp map_smul' := fun r x => by`. Use extensionality with `y`. Establish `h1 : (r • x : C) = (r : ℂ) • x` using `rfl`. Establish `h2 : (r • ip.flip x : C →ₗ[ℂ] ℂ) y = (r : ℂ) * ip y x` using `by show ((r : ℂ) • ip.flip x) y = _`.

Simplify using the standard rewrite rules. Simplify using `only [RingHom.id_apply]`. Rewrite using `[h2, h1, LinearMap.map_smulₛₗ]`. Simplify using `[Complex.conj_ofReal] }`. Establish `hg : Function.Injective g`.

Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx`. Assume the negation of the conclusion as `hne`. Establish `h0 : ip x x = 0`. Use `LinearMap.congr_fun hx x` as an intermediate fact.

Simplify `this` using `[g]`. Use `hpos x hne` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `at this`. Establish `hrank : Module.finrank ℝ C = Module.finrank ℝ (C →ₗ[ℂ] ℂ)`.

Rewrite using `[finrank_real_of_complex, finrank_real_of_complex, Module.finrank_linearMap, Module.finrank_self, mul_one]`. Establish `hs : Function.Surjective g` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hg`. Take `⟨x, hx⟩` from `hs ((ipA.flip u).comp io)`. Use `⟨x, fun y => ?_, fun x' hx' => ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun hx y` as an intermediate fact.

Simplify `this` using `[g]`. Apply `hg` to reduce the goal to its premises. Use extensionality with `y`. Establish `hy` using `LinearMap.congr_fun hx y`. Simplify using `only [g, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.flip_apply] at hy ⊢`.

Rewrite using `[hx' y, hy]`. Both sides reduce to the same expression.
-/
theorem hermitian_adjoint_exists_unique :
    ∀ (A C : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]
      (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ),
      (∀ x y, ip x y = conj (ip y x)) → (∀ x, x ≠ 0 → 0 < (ip x x).re) →
      ∀ (io : C →ₗ[ℂ] A) (u : A), ∃! x : C, ∀ y, ip y x = ipA (io y) u := by
  intro A C _ _ _ _ _ ipA ip _hsym hpos io u

  let g : C →ₗ[ℝ] (C →ₗ[ℂ] ℂ) :=
    { toFun := fun x => ip.flip x
      map_add' := fun x y => by simp
      map_smul' := fun r x => by
        ext y
        have h1 : (r • x : C) = (r : ℂ) • x := rfl
        have h2 : (r • ip.flip x : C →ₗ[ℂ] ℂ) y = (r : ℂ) * ip y x := by
          show ((r : ℂ) • ip.flip x) y = _
          simp
        simp only [RingHom.id_apply]
        rw [h2, h1, LinearMap.map_smulₛₗ]
        simp [Complex.conj_ofReal] }
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have h0 : ip x x = 0 := by
      have := LinearMap.congr_fun hx x
      simpa [g] using this
    have := hpos x hne
    rw [h0] at this
    simp at this
  have hrank : Module.finrank ℝ C = Module.finrank ℝ (C →ₗ[ℂ] ℂ) := by
    rw [finrank_real_of_complex, finrank_real_of_complex, Module.finrank_linearMap, Module.finrank_self, mul_one]
  have hs : Function.Surjective g := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hg
  obtain ⟨x, hx⟩ := hs ((ipA.flip u).comp io)
  refine ⟨x, fun y => ?_, fun x' hx' => ?_⟩
  · have := LinearMap.congr_fun hx y
    simpa [g] using this
  · apply hg
    ext y
    have hy := LinearMap.congr_fun hx y
    simp only [g, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.flip_apply] at hy ⊢
    rw [hx' y, hy]
    rfl

end GlobalTheory
