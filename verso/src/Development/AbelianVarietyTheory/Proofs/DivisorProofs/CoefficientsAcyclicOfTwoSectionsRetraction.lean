import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo

set_option autoImplicit false

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Use function extensionality and compare the values at `T`. Establish `h1 : g (S.obj T) = M.map (u.app T) (g T)` using `hg T (S.obj T) (u.app T)`. Establish `h2 : g (S.obj T) = M.map (v.app T) (g T)` using `hg T (S.obj T) (v.app T)`.

Establish `e` using `hv T (g T)`. Rewrite `e` using `[← h2, h1, hu]`. Conclude with `e.symm`. Introduce `f hf`. Use `⟨fun T ↦ r T (f T (S.obj T) (u.app T) - f T (S.obj T) (v.app T)), ?_⟩` and prove the remaining obligations.

Introduce `T T' φ`. Establish `key : ∀ θ : 𝟭 C ⟶ S, r T' (M.map (θ.app T') (f T T' φ)) + r T' (f T' (S.obj T') (θ.app T')) = M.map φ (r T (f T (S.obj T) (θ.app T))) + r T' (f (S.obj T) (S.obj T') (S.map φ))`. Introduce `θ`. Establish `nat : φ ≫ θ.app T' = θ.app T ≫ S.map φ` using `θ.naturality φ`. Establish `e1` using `hf T T' (S.obj T') φ (θ.app T')`.

Establish `e2` using `hf T (S.obj T) (S.obj T') (θ.app T) (S.map φ)`. Rewrite `e1` using `[nat, e2]`. Establish `e3` using `congrArg (r T') e1`. Simplify using `only [map_add, hr] at e3`. Conclude with `e3.symm`.

Establish `ku` using `key u`. Establish `kv` using `key v`. Rewrite `ku` using `[hu]`. Rewrite `kv` using `[hv]`. Simplify using `only [map_sub]`.

Take the linear combination `(norm := abel1) kv - ku`. Introduce `z hz`. Set `A : (𝟭 C ⟶ S) → ∀ (T T' : C) (_ : T ⟶ T'), M.obj (S.obj T')` to `fun θ T T' φ ↦ z T T' (S.obj T') φ (θ.app T') - z T (S.obj T) (S.obj T') (θ.app T) (S.map φ)`. Use `⟨fun T T' φ ↦ r T' (A v T T' φ - A u T T' φ), ?_⟩` and prove the remaining obligations. Introduce `T T' T'' φ ψ`.

Establish `key : ∀ θ : 𝟭 C ⟶ S, M.map ψ (r T' (A θ T T' φ)) = r T'' (M.map (θ.app T'') (z T T' T'' φ ψ)) + r T'' (A θ T T'' (φ ≫ ψ)) - r T'' (A θ T' T'' ψ) - r T'' (z (S.obj T) (S.obj T') (S.obj T'') (S.map φ) (S.map ψ))`. Introduce `θ`. Establish `nat1 : φ ≫ θ.app T' = θ.app T ≫ S.map φ` using `θ.naturality φ`. Establish `nat2 : ψ ≫ θ.app T'' = θ.app T' ≫ S.map ψ` using `θ.naturality ψ`. Establish `h1` using `hz T T' T'' (S.obj T'') φ ψ (θ.app T'')`.

Establish `h2` using `hz T T' (S.obj T') (S.obj T'') φ (θ.app T') (S.map ψ)`. Establish `h3` using `hz T (S.obj T) (S.obj T') (S.obj T'') (θ.app T) (S.map φ) (S.map ψ)`. Rewrite `h2` using `[nat1, ← nat2]`. Rewrite `h3` using `[← S.map_comp]`. Establish `inner : M.map (S.map ψ) (A θ T T' φ) = M.map (θ.app T'') (z T T' T'' φ ψ) + A θ T T'' (φ ≫ ψ) - A θ T' T'' ψ - z (S.obj T) (S.obj T') (S.obj T'') (S.map φ) (S.map ψ)`.

Simplify using `only [A, map_sub]`. Use `first`. Consider the case `linear_combination (norm := abel1) h2 - h3 - h1`. Consider the case `linear_combination (norm := abel1) h2 - h3 + h1`. Consider the case `linear_combination (norm := abel1) h1 + h2 - h3`.

Consider the case `linear_combination (norm := abel1) -h1 - h2 + h3`. Rewrite using `[← hr, inner]`. Simplify using `only [map_sub, map_add]`. Establish `ku` using `key u`. Establish `kv` using `key v`.

Rewrite `ku` using `[hu]`. Rewrite `kv` using `[hv]`. Simplify using `only [map_sub]`. Take the linear combination `(norm := abel1) ku - kv`.
-/
theorem coef_acyclic_of_two_sections (C : Type 1) [Category.{0} C] (M : Coef C) (S : C ⥤ C) (u v : 𝟭 C ⟶ S)
    (r : ∀ T, M.obj (S.obj T) →+ M.obj T)
    (hr : ∀ (T T' : C) (φ : T ⟶ T') x, r T' (M.map (S.map φ) x) = M.map φ (r T x))
    (hu : ∀ T x, r T (M.map (u.app T) x) = 0) (hv : ∀ T x, r T (M.map (v.app T) x) = x) :
    M.Ac0 ∧ M.Ac1 ∧ M.Ac2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    funext T
    have h1 : g (S.obj T) = M.map (u.app T) (g T) := hg T (S.obj T) (u.app T)
    have h2 : g (S.obj T) = M.map (v.app T) (g T) := hg T (S.obj T) (v.app T)
    have e := hv T (g T)
    rw [← h2, h1, hu] at e
    exact e.symm
  · intro f hf
    refine ⟨fun T ↦ r T (f T (S.obj T) (u.app T) - f T (S.obj T) (v.app T)), ?_⟩
    intro T T' φ
    have key : ∀ θ : 𝟭 C ⟶ S, r T' (M.map (θ.app T') (f T T' φ)) + r T' (f T' (S.obj T') (θ.app T')) =
        M.map φ (r T (f T (S.obj T) (θ.app T))) + r T' (f (S.obj T) (S.obj T') (S.map φ)) := by
      intro θ
      have nat : φ ≫ θ.app T' = θ.app T ≫ S.map φ := θ.naturality φ
      have e1 := hf T T' (S.obj T') φ (θ.app T')
      have e2 := hf T (S.obj T) (S.obj T') (θ.app T) (S.map φ)
      rw [nat, e2] at e1
      have e3 := congrArg (r T') e1
      simp only [map_add, hr] at e3
      exact e3.symm
    have ku := key u
    have kv := key v
    rw [hu] at ku
    rw [hv] at kv
    simp only [map_sub]
    linear_combination (norm := abel1) kv - ku
  · intro z hz
    let A : (𝟭 C ⟶ S) → ∀ (T T' : C) (_ : T ⟶ T'), M.obj (S.obj T') := fun θ T T' φ ↦
      z T T' (S.obj T') φ (θ.app T') - z T (S.obj T) (S.obj T') (θ.app T) (S.map φ)
    refine ⟨fun T T' φ ↦ r T' (A v T T' φ - A u T T' φ), ?_⟩
    intro T T' T'' φ ψ
    have key : ∀ θ : 𝟭 C ⟶ S, M.map ψ (r T' (A θ T T' φ)) =
        r T'' (M.map (θ.app T'') (z T T' T'' φ ψ)) + r T'' (A θ T T'' (φ ≫ ψ)) - r T'' (A θ T' T'' ψ)
          - r T'' (z (S.obj T) (S.obj T') (S.obj T'') (S.map φ) (S.map ψ)) := by
      intro θ
      have nat1 : φ ≫ θ.app T' = θ.app T ≫ S.map φ := θ.naturality φ
      have nat2 : ψ ≫ θ.app T'' = θ.app T' ≫ S.map ψ := θ.naturality ψ
      have h1 := hz T T' T'' (S.obj T'') φ ψ (θ.app T'')
      have h2 := hz T T' (S.obj T') (S.obj T'') φ (θ.app T') (S.map ψ)
      have h3 := hz T (S.obj T) (S.obj T') (S.obj T'') (θ.app T) (S.map φ) (S.map ψ)
      rw [nat1, ← nat2] at h2
      rw [← S.map_comp] at h3
      have inner : M.map (S.map ψ) (A θ T T' φ) =
          M.map (θ.app T'') (z T T' T'' φ ψ) + A θ T T'' (φ ≫ ψ) - A θ T' T'' ψ
            - z (S.obj T) (S.obj T') (S.obj T'') (S.map φ) (S.map ψ) := by
        simp only [A, map_sub]
        first
          | linear_combination (norm := abel1) h2 - h3 - h1
          | linear_combination (norm := abel1) h2 - h3 + h1
          | linear_combination (norm := abel1) h1 + h2 - h3
          | linear_combination (norm := abel1) -h1 - h2 + h3
      rw [← hr, inner]
      simp only [map_sub, map_add]
    have ku := key u
    have kv := key v
    rw [hu] at ku
    rw [hv] at kv
    simp only [map_sub]
    linear_combination (norm := abel1) ku - kv

end GlobalTheory
