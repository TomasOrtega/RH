import Mathlib
open Matrix

namespace GlobalTheory.HermGram

noncomputable def reForm {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (z ⬝ᵥ H *ᵥ star w).re)
    (by intro a b c; simp [add_dotProduct])
    (by intro c a b; simp [smul_dotProduct, Complex.smul_re])
    (by intro a b c; simp [star_add, mulVec_add, dotProduct_add])
    (by intro c a b
        have : star (c • b) = c • star b := by
          ext i; simp [Complex.conj_ofReal]
        rw [this, mulVec_smul, dotProduct_smul, Complex.smul_re])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem reForm_apply {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    reForm H z w = (z ⬝ᵥ H *ᵥ star w).re := rfl

/- English proof (translation)
Simplify using `only [reForm_apply]`. Establish `: star (z ⬝ᵥ H *ᵥ star w) = w ⬝ᵥ H *ᵥ star z`. Simplify using `only [dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, star_star]`. Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hH.apply i j]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← this]`. Simplify using the standard rewrite rules.
-/
theorem reForm_symm {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ} (hH : H.IsHermitian)
    (z w : Fin g → ℂ) : reForm H z w = reForm H w z := by
  simp only [reForm_apply]
  have : star (z ⬝ᵥ H *ᵥ star w) = w ⬝ᵥ H *ᵥ star z := by
    simp only [dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, star_star]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hH.apply i j]; ring
  rw [← this]; simp

/- English proof (translation)
Rewrite using `[posDef_iff_dotProduct_mulVec]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use extensionality with `k l`. Simplify using `only [conjTranspose_apply, of_apply, star_trivial]`. Conclude with `reForm_symm hH (e l) (e k)`.

Introduce `x hx set v : Fin g → ℂ := ∑ k, x k • e k with hvdef`. Establish `hv : v ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises. Apply `e.equivFun.symm.injective` to reduce the goal to its premises.

Rewrite using `[map_zero, Module.Basis.equivFun_symm_apply]`. Conclude with `h0`. Establish `key : star x ⬝ᵥ (Matrix.of fun k l => (e k ⬝ᵥ H.mulVec (star (e l))).re) *ᵥ x = reForm H v v`. Rewrite using `[hvdef]`. Express the relevant statement in the definitionally equal form `star x ⬝ᵥ (Matrix.of fun k l => reForm H (e k) (e l)) *ᵥ x = _`.

Simplify using `only [star_trivial, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, dotProduct, mulVec, of_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[reForm_symm hH (e l) (e k)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, reForm_apply]`.

Conclude with `hpos v hv`.
-/
theorem gram_posDef {g n : ℕ} (e : Module.Basis (Fin n) ℝ (Fin g → ℂ))
    {H : Matrix (Fin g) (Fin g) ℂ} (hH : H.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H.mulVec (star z)).re) :
    (Matrix.of fun k l => (e k ⬝ᵥ H.mulVec (star (e l))).re).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · ext k l
    simp only [conjTranspose_apply, of_apply, star_trivial]
    exact reForm_symm hH (e l) (e k)
  · intro x hx
    set v : Fin g → ℂ := ∑ k, x k • e k with hvdef
    have hv : v ≠ 0 := by
      intro h0
      apply hx
      apply e.equivFun.symm.injective
      rw [map_zero, Module.Basis.equivFun_symm_apply]
      exact h0
    have key : star x ⬝ᵥ (Matrix.of fun k l => (e k ⬝ᵥ H.mulVec (star (e l))).re) *ᵥ x
        = reForm H v v := by
      rw [hvdef]
      change star x ⬝ᵥ (Matrix.of fun k l => reForm H (e k) (e l)) *ᵥ x = _
      simp only [star_trivial, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, dotProduct, mulVec, of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [reForm_symm hH (e l) (e k)]; ring
    rw [key, reForm_apply]
    exact hpos v hv

/- English proof (translation)
Use `⟨gram_posDef e h₁ p₁, ?_⟩` and prove the remaining obligations. Establish `hG : (Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re) * LinearMap.toMatrix e e (γ.restrictScalars ℝ) = Matrix.of fun k l => (e k ⬝ᵥ H₂.mulVec (star (e l))).re`. Use extensionality with `k l`. Rewrite using `[of_apply, hγ, mul_apply]`. Establish `hs : γ (e l) = ∑ m, e.repr (γ (e l)) m • e m` using `(e.sum_repr _).symm`.

Establish `: (e k ⬝ᵥ H₁.mulVec (star (γ (e l)))).re = reForm H₁ (e k) (γ (e l))` using `rfl`. Rewrite using `[this, hs]`. Simplify using `only [map_sum, map_smul, smul_eq_mul, LinearMap.toMatrix_apply, of_apply, LinearMap.restrictScalars_apply, reForm_apply]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hG]`. Conclude with `gram_posDef e h₂ p₂`.
-/
theorem gram_posDef_pair (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ)
    (h₁ : H₁.IsHermitian) (h₂ : H₂.IsHermitian)
    (p₁ : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re)
    (p₂ : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₂.mulVec (star z)).re)
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hγ : ∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) :
    (Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re).PosDef ∧
    ((Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re) *
      LinearMap.toMatrix e e (γ.restrictScalars ℝ)).PosDef := by
  refine ⟨gram_posDef e h₁ p₁, ?_⟩
  have hG : (Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re) *
      LinearMap.toMatrix e e (γ.restrictScalars ℝ) =
      Matrix.of fun k l => (e k ⬝ᵥ H₂.mulVec (star (e l))).re := by
    ext k l
    rw [of_apply, hγ, mul_apply]
    have hs : γ (e l) = ∑ m, e.repr (γ (e l)) m • e m := (e.sum_repr _).symm
    have : (e k ⬝ᵥ H₁.mulVec (star (γ (e l)))).re = reForm H₁ (e k) (γ (e l)) := rfl
    rw [this, hs]
    simp only [map_sum, map_smul, smul_eq_mul, LinearMap.toMatrix_apply, of_apply,
      LinearMap.restrictScalars_apply, reForm_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hG]
  exact gram_posDef e h₂ p₂

end GlobalTheory.HermGram
