import Mathlib

namespace GlobalTheory.OrthogonalProjection

open Module

/- English proof (translation)
Set `b : Basis (Fin (finrank ℂ M)) ℂ M` to `Module.finBasis ℂ M`. Set `T : M →ₗ[ℂ] (Fin (finrank ℂ M) → ℂ)` to `LinearMap.pi (fun i => (B (b i : W)).comp M.subtype)`. Establish `key : ∀ w : W, (∀ i, B (b i : W) w = 0) → ∀ z ∈ M, B z w = 0`. Introduce `w hw z hz`. Establish `h0 : (B.flip w).comp M.subtype = 0`.

Apply `b.ext` to reduce the goal to its premises. Introduce `i`. Simplify using `using hw i`. Use `LinearMap.congr_fun h0 ⟨z, hz⟩` as an intermediate fact. Simplify using `using this`.

Establish `hinj : Function.Injective T`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `m hm`. Establish `h1 : ∀ i, B (b i : W) (m : W) = 0`. Introduce `i`.

Use `congr_fun hm i` as an intermediate fact. Simplify `this` using `[T]`. Establish `h2` using `key m h1 m m.2`. Conclude with `Subtype.ext (hB _ h2)`. Establish `hsurj : Function.Surjective T` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [Module.finrank_fin_fun])).mp hinj`.

Take `⟨m, hm⟩` from `hsurj (fun i => B (b i : W) v)`. Use `⟨m, m.2, ?_⟩` and prove the remaining obligations. Apply `key` to reduce the goal to its premises. Introduce `i`. Use `congr_fun hm i` as an intermediate fact.

Simplify using `[T] at this`. Simplify using `[map_sub, this]`.
-/
theorem exists_orthogonal_projection_finite {W : Type} [AddCommGroup W] [Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hB : ∀ v : W, B v v = 0 → v = 0) (M : Submodule ℂ W) [FiniteDimensional ℂ M] (v : W) :
    ∃ m ∈ M, ∀ z ∈ M, B z (v - m) = 0 := by
  classical
  let b : Basis (Fin (finrank ℂ M)) ℂ M := Module.finBasis ℂ M
  let T : M →ₗ[ℂ] (Fin (finrank ℂ M) → ℂ) :=
    LinearMap.pi (fun i => (B (b i : W)).comp M.subtype)
  have key : ∀ w : W, (∀ i, B (b i : W) w = 0) → ∀ z ∈ M, B z w = 0 := by
    intro w hw z hz
    have h0 : (B.flip w).comp M.subtype = 0 := by
      apply b.ext
      intro i
      simpa using hw i
    have := LinearMap.congr_fun h0 ⟨z, hz⟩
    simpa using this
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    have h1 : ∀ i, B (b i : W) (m : W) = 0 := by
      intro i
      have := congr_fun hm i
      simpa [T] using this
    have h2 := key m h1 m m.2
    exact Subtype.ext (hB _ h2)
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_fin_fun])).mp hinj
  obtain ⟨m, hm⟩ := hsurj (fun i => B (b i : W) v)
  refine ⟨m, m.2, ?_⟩
  apply key
  intro i
  have := congr_fun hm i
  simp [T] at this
  simp [map_sub, this]

/- English proof (translation)
Introduce `W _ _ B hB M _ v`. Conclude with `exists_orthogonal_projection_finite B hB M v`.
-/
theorem exists_orth_proj : ∀ {W : Type} [inst : AddCommGroup W] [inst_1 : Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ (v : W), ((B : W → W →ₗ[ℂ] ℂ) v : W → ℂ) v = (0 : ℂ) → v = (0 : W)) → ∀ (M : Submodule ℂ W) [FiniteDimensional ℂ ↥M] (v : W), ∃ m ∈ M, ∀ z ∈ M, ((B : W → W →ₗ[ℂ] ℂ) z : W → ℂ) (v - m) = (0 : ℂ) := by
  intro W _ _ B hB M _ v
  exact exists_orthogonal_projection_finite B hB M v

end GlobalTheory.OrthogonalProjection
