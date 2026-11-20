import Mathlib

open Matrix

namespace GlobalTheory

/- English proof (translation)
Use `set C := Matrix.toLin' c with hC`. Use `set D := Matrix.toLin' d with hD`. Take `⟨Wc, hW⟩` from `Submodule.exists_isCompl (LinearMap.range D)`. Set `π` to `Submodule.linearProjOfIsCompl Wc (LinearMap.range D) hW.symm`. Establish `hdec : ∀ w : Fin n → κ, C (p *ᵥ w) + D (q *ᵥ w) = w`.

Introduce `w`. Simplify using `only [hC, hD, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, h, Matrix.one_mulVec]`. Establish `hπD : ∀ v, π (D v) = 0`. Introduce `v`. Conclude with `Submodule.linearProjOfIsCompl_apply_right hW.symm ⟨D v, LinearMap.mem_range_self _ _⟩`.

Establish `hsurj : Function.Surjective (π ∘ₗ C)`. Introduce `w`. Use `⟨p *ᵥ (w : Fin n → κ), ?_⟩` and prove the remaining obligations. Establish `h2 : π (w : Fin n → κ) = w` using `Submodule.linearProjOfIsCompl_apply_left _ w`. Use `congrArg π (hdec w)` as an intermediate fact.

Rewrite `this` using `[map_add, hπD, add_zero, h2]`. Simplify using `using this`. Take `⟨g, hg⟩` from `LinearMap.exists_rightInverse_of_surjective (π ∘ₗ C) (LinearMap.range_eq_top.mpr hsurj)`. Establish `hdim : Module.finrank κ (LinearMap.ker D) = Module.finrank κ Wc`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker D`.

Establish `h2` using `Submodule.finrank_add_eq_of_isCompl hW`. Simplify using `only [Module.finrank_fin_fun] at h1 h2`. Use linear arithmetic over natural numbers and integers. Set `e` to `LinearEquiv.ofFinrankEq _ _ hdim`. Take `⟨K', hK⟩` from `Submodule.exists_isCompl (LinearMap.ker D)`.

Set `projK` to `Submodule.linearProjOfIsCompl (LinearMap.ker D) K' hK`. Set `Y : (Fin n → κ) →ₗ[κ] (Fin n → κ)` to `g ∘ₗ (e : LinearMap.ker D →ₗ[κ] Wc) ∘ₗ projK`. Use `⟨LinearMap.toMatrix' Y, ?_⟩` and prove the remaining obligations. Introduce `hdet`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`.

Establish `hM : (c * LinearMap.toMatrix' Y + d) *ᵥ v = C (Y v) + D v`. Rewrite using `[Matrix.add_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]`. Both sides reduce to the same expression. Rewrite `hv` using `[hM]`. Establish `hp : π (C (Y v)) = e (projK v)`.

Use `LinearMap.congr_fun hg (e (projK v))` as an intermediate fact. Simplify `this` using `[Y]`. Establish `h3 : e (projK v) = 0`. Use `congrArg π hv` as an intermediate fact. Rewrite `this` using `[map_add, hπD, add_zero, hp, map_zero]`. Then use the resulting hypothesis.

Establish `hk : projK v = 0` using `(LinearEquiv.map_eq_zero_iff e).mp h3`. Establish `hY : Y v = 0` using `by simp [Y, hk]`. Establish `hDv : D v = 0` using `by rw [hY, map_zero, zero_add] at hv; exact hv`. Establish `hvK : v ∈ LinearMap.ker D` using `hDv`. Establish `h4` using `Submodule.linearProjOfIsCompl_apply_left hK ⟨v, hvK⟩`.

Establish `: (⟨v, hvK⟩ : LinearMap.ker D) = 0` using `by rw [← h4]; exact hk`. Conclude with `hv0 (congrArg Subtype.val this)`.
-/
theorem matrix_stableRange_one (κ : Type) [Field κ] (n : ℕ) (c d p q : Matrix (Fin n) (Fin n) κ)
    (h : c * p + d * q = 1) : ∃ y : Matrix (Fin n) (Fin n) κ, (c * y + d).det ≠ 0 := by
  classical
  set C := Matrix.toLin' c with hC
  set D := Matrix.toLin' d with hD
  obtain ⟨Wc, hW⟩ := Submodule.exists_isCompl (LinearMap.range D)
  let π := Submodule.linearProjOfIsCompl Wc (LinearMap.range D) hW.symm
  have hdec : ∀ w : Fin n → κ, C (p *ᵥ w) + D (q *ᵥ w) = w := by
    intro w
    simp only [hC, hD, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, h,
      Matrix.one_mulVec]
  have hπD : ∀ v, π (D v) = 0 := by
    intro v
    exact Submodule.linearProjOfIsCompl_apply_right hW.symm ⟨D v, LinearMap.mem_range_self _ _⟩
  have hsurj : Function.Surjective (π ∘ₗ C) := by
    intro w
    refine ⟨p *ᵥ (w : Fin n → κ), ?_⟩
    have h2 : π (w : Fin n → κ) = w := Submodule.linearProjOfIsCompl_apply_left _ w
    have := congrArg π (hdec w)
    rw [map_add, hπD, add_zero, h2] at this
    simpa using this
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective (π ∘ₗ C)
    (LinearMap.range_eq_top.mpr hsurj)
  have hdim : Module.finrank κ (LinearMap.ker D) = Module.finrank κ Wc := by
    have h1 := LinearMap.finrank_range_add_finrank_ker D
    have h2 := Submodule.finrank_add_eq_of_isCompl hW
    simp only [Module.finrank_fin_fun] at h1 h2
    omega
  let e := LinearEquiv.ofFinrankEq _ _ hdim
  obtain ⟨K', hK⟩ := Submodule.exists_isCompl (LinearMap.ker D)
  let projK := Submodule.linearProjOfIsCompl (LinearMap.ker D) K' hK
  let Y : (Fin n → κ) →ₗ[κ] (Fin n → κ) := g ∘ₗ (e : LinearMap.ker D →ₗ[κ] Wc) ∘ₗ projK
  refine ⟨LinearMap.toMatrix' Y, ?_⟩
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hM : (c * LinearMap.toMatrix' Y + d) *ᵥ v = C (Y v) + D v := by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    rfl
  rw [hM] at hv
  have hp : π (C (Y v)) = e (projK v) := by
    have := LinearMap.congr_fun hg (e (projK v))
    simpa [Y] using this
  have h3 : e (projK v) = 0 := by
    have := congrArg π hv
    rwa [map_add, hπD, add_zero, hp, map_zero] at this
  have hk : projK v = 0 := (LinearEquiv.map_eq_zero_iff e).mp h3
  have hY : Y v = 0 := by simp [Y, hk]
  have hDv : D v = 0 := by rw [hY, map_zero, zero_add] at hv; exact hv
  have hvK : v ∈ LinearMap.ker D := hDv
  have h4 := Submodule.linearProjOfIsCompl_apply_left hK ⟨v, hvK⟩
  have : (⟨v, hvK⟩ : LinearMap.ker D) = 0 := by rw [← h4]; exact hk
  exact hv0 (congrArg Subtype.val this)

/- English proof (translation)
Introduce `κ _ n c d p q h` and use `matrix_stableRange_one κ n c d p q h`.
-/
theorem matrix_stableRange_one' : ∀ (κ : Type) [Field κ] (n : ℕ) (c d p q : Matrix (Fin n) (Fin n) κ),
    c * p + d * q = 1 → ∃ y : Matrix (Fin n) (Fin n) κ, (c * y + d).det ≠ 0 :=
  fun κ _ n c d p q h => matrix_stableRange_one κ n c d p q h

end GlobalTheory
