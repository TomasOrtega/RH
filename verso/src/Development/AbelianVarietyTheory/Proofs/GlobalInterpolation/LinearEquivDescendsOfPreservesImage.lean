import Mathlib

namespace GlobalTheory

/- English proof (translation)
Set `F : (ι → K) → (ι → ℂ)` to `fun v i => f (v i)`. Establish `hFinj : Function.Injective F`. Introduce `v w hvw`. Use function extensionality and compare the values at `i`. Conclude with `f.injective (congrFun hvw i)`.

Use `choose G hG using h`. Establish `hG' : ∀ v, u (F v) = F (G v)` using `hG`. Establish `hFadd : ∀ v w, F (v + w) = F v + F w`. Introduce `v w`. Use function extensionality and compare the values at `i`.

Simplify using `[F]`. Establish `hFsmul : ∀ (c : K) v, F (c • v) = f c • F v`. Introduce `c v`. Use function extensionality and compare the values at `i`. Simplify using `[F]`.

Set `Gl : (ι → K) →ₗ[K] (ι → K)` to `{ toFun := G map_add' := fun v w => hFinj (by rw [← hG', hFadd, map_add, hG', hG', hFadd]) map_smul' := fun c v => hFinj (by`. Simplify using `only [RingHom.id_apply]`. Rewrite using `[← hG', hFsmul, map_smul, hG', hFsmul]) }`. Establish `hGl : ∀ v, Gl v = G v` using `fun _ => rfl`. Establish `hinj : Function.Injective Gl`.

Introduce `v w hvw`. Apply `hFinj` to reduce the goal to its premises. Apply `u.injective` to reduce the goal to its premises. Rewrite using `[hG', hG']`. Conclude with `congrArg F hvw`.

Set `g : (ι → K) ≃ₗ[K] (ι → K)` to `LinearEquiv.ofInjectiveEndo Gl hinj`. Establish `hg : ∀ v, g v = G v` using `fun v => by`. Simplify using `[g, hGl]`. Establish `hsingle : ∀ j : ι, F (Pi.single j 1) = Pi.single j 1`. Introduce `j`.

Use function extensionality and compare the values at `i`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[F]`. Simplify using `[F, Pi.single_eq_of_ne hij]`.

Establish `hmat : LinearMap.toMatrix' (u : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) = (LinearMap.toMatrix' (g : (ι → K) →ₗ[K] (ι → K))).map f`. Use extensionality with `i j`. Use `congrFun (hG' (Pi.single j 1)) i` as an intermediate fact. Rewrite `this` using `[hsingle j]`. Simplify using `only [LinearMap.toMatrix'_apply, Matrix.map_apply]`.

Simplify using `only [LinearEquiv.coe_coe, hg]`. Conclude with `this`. Use `⟨g, fun v => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hg]`. Conclude with `hG v`.

Rewrite using `[← LinearMap.det_toMatrix', hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, LinearMap.det_toMatrix']`.
-/
theorem linearEquiv_descends_of_preserves_image {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (f : K →+* ℂ) (u : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ))
    (h : ∀ v : ι → K, ∃ v' : ι → K, u (fun i => f (v i)) = fun i => f (v' i)) :
    ∃ g : (ι → K) ≃ₗ[K] (ι → K), (∀ v, u (fun i => f (v i)) = fun i => f (g v i)) ∧
      LinearMap.det (u : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) =
        f (LinearMap.det (g : (ι → K) →ₗ[K] (ι → K))) := by
  classical
  let F : (ι → K) → (ι → ℂ) := fun v i => f (v i)
  have hFinj : Function.Injective F := by
    intro v w hvw
    funext i
    exact f.injective (congrFun hvw i)
  choose G hG using h
  have hG' : ∀ v, u (F v) = F (G v) := hG
  have hFadd : ∀ v w, F (v + w) = F v + F w := by
    intro v w; funext i; simp [F]
  have hFsmul : ∀ (c : K) v, F (c • v) = f c • F v := by
    intro c v; funext i; simp [F]
  let Gl : (ι → K) →ₗ[K] (ι → K) :=
    { toFun := G
      map_add' := fun v w => hFinj (by rw [← hG', hFadd, map_add, hG', hG', hFadd])
      map_smul' := fun c v => hFinj (by
        simp only [RingHom.id_apply]
        rw [← hG', hFsmul, map_smul, hG', hFsmul]) }
  have hGl : ∀ v, Gl v = G v := fun _ => rfl
  have hinj : Function.Injective Gl := by
    intro v w hvw
    apply hFinj
    apply u.injective
    rw [hG', hG']
    exact congrArg F hvw
  let g : (ι → K) ≃ₗ[K] (ι → K) := LinearEquiv.ofInjectiveEndo Gl hinj
  have hg : ∀ v, g v = G v := fun v => by
    simp [g, hGl]
  have hsingle : ∀ j : ι, F (Pi.single j 1) = Pi.single j 1 := by
    intro j
    funext i
    by_cases hij : i = j
    · subst hij; simp [F]
    · simp [F, Pi.single_eq_of_ne hij]
  have hmat : LinearMap.toMatrix' (u : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) =
      (LinearMap.toMatrix' (g : (ι → K) →ₗ[K] (ι → K))).map f := by
    ext i j
    have := congrFun (hG' (Pi.single j 1)) i
    rw [hsingle j] at this
    simp only [LinearMap.toMatrix'_apply, Matrix.map_apply]
    simp only [LinearEquiv.coe_coe, hg]
    exact this
  refine ⟨g, fun v => ?_, ?_⟩
  · rw [hg]; exact hG v
  · rw [← LinearMap.det_toMatrix', hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      LinearMap.det_toMatrix']

end GlobalTheory
