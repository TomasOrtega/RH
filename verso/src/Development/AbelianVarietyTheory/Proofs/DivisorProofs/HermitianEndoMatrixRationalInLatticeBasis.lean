import Mathlib
open Matrix

namespace GlobalTheory

def imFormRight {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] ℝ where
  toFun w := (z ⬝ᵥ H *ᵥ star w).im
  map_add' a b := by simp [star_add, mulVec_add, dotProduct_add]
  map_smul' r w := by
    simp [star_smul, mulVec_smul, dotProduct_smul, Complex.smul_im]

def imFormLeft {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] ℝ where
  toFun z := (z ⬝ᵥ H *ᵥ star w).im
  map_add' a b := by simp [add_dotProduct]
  map_smul' r z := by
    simp [smul_dotProduct, Complex.smul_im]

/- English proof (translation)
Introduce `g n e H₁ H₂ hpos h1 h2 γ hγ`. Use `set T := LinearMap.toMatrix e e (γ.restrictScalars ℝ) with hT`. Set `A₁ : Matrix (Fin n) (Fin n) ℝ` to `fun k l => (e k ⬝ᵥ H₁ *ᵥ star (e l)).im`. Set `A₂ : Matrix (Fin n) (Fin n) ℝ` to `fun k l => (e k ⬝ᵥ H₂ *ᵥ star (e l)).im`. Establish `hγe : ∀ l, γ (e l) = ∑ m, T m l • e m`.

Introduce `l`. Use `e.sum_repr (γ (e l))` as an intermediate fact. Rewrite using `[← this]`. Simplify using `[hT, LinearMap.toMatrix_apply]`. Establish `key : A₁ * T = A₂`.

Use extensionality with `k l`. Rewrite using `[mul_apply]`. Use `show _ = (e k ⬝ᵥ H₂ *ᵥ star (e l)).im`. Rewrite using `[hγ, hγe l]`. Use `map_sum (imFormRight H₁ (e k)) (fun m : Fin n => T m l • e m) (Finset.univ : Finset (Fin n))` as an intermediate fact.

Simplify using `only [map_smul, smul_eq_mul] at this`. Express the relevant statement in the definitionally equal form `_ = imFormRight H₁ (e k) _`. Rewrite using `[this]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.

Both sides reduce to the same expression. Establish `hdet : A₁.det ≠ 0`. Introduce `h0`. Take `⟨x, hx0, hx⟩` from `(Matrix.exists_mulVec_eq_zero_iff).2 h0`. Use `set v := ∑ l, x l • e l with hv`.

Establish `hk : ∀ k, imFormRight H₁ (e k) v = 0`. Introduce `k`. Use `congrFun hx k` as an intermediate fact. Rewrite using `[hv, map_sum]`. Simplify using `only [map_smul, smul_eq_mul]`.

Simplify using `only [mulVec, dotProduct, Pi.zero_apply] at this`. Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Both sides reduce to the same expression.

Establish `hu : ∀ u, imFormLeft H₁ v u = 0`. Introduce `u`. Rewrite using `[← e.sum_repr u, map_sum]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`.

Use `hk k` as an intermediate fact. Simplify using `only [imFormRight, imFormLeft, LinearMap.coe_mk, AddHom.coe_mk] at this ⊢`. Rewrite using `[this, smul_zero]`. Establish `hre : (v ⬝ᵥ H₁ *ᵥ star v).re = 0`. Use `hu (Complex.I • v)` as an intermediate fact.

Simplify using `only [imFormLeft, LinearMap.coe_mk, AddHom.coe_mk, smul_dotProduct, smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im] at this`. Simplify using `using this`. Establish `hv0 : v = 0`. Assume the negation of the conclusion as `hne`. Use `hpos v hne` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Apply `hx0` to reduce the goal to its premises. Establish `: e.equivFun.symm x = 0` using `by rw [Module.Basis.equivFun_symm_apply]; exact hv0`. Conclude with `e.equivFun.symm.injective (by rw [this, map_zero])`. Use `choose m₁ hm₁ using h1`.

Use `choose m₂ hm₂ using h2`. Set `A₁q : Matrix (Fin n) (Fin n) ℚ` to `fun k l => (m₁ k l : ℚ)`. Set `A₂q : Matrix (Fin n) (Fin n) ℚ` to `fun k l => (m₂ k l : ℚ)`. Establish `hA₁ : A₁q.map (Rat.castHom ℝ) = A₁`. Use extensionality with `k l`.

Use `show ((m₁ k l : ℚ) : ℝ) = _`. Rewrite using `[Rat.cast_intCast, hm₁]`. Establish `hA₂ : A₂q.map (Rat.castHom ℝ) = A₂`. Use extensionality with `k l`. Use `show ((m₂ k l : ℚ) : ℝ) = _`.

Rewrite using `[Rat.cast_intCast, hm₂]`. Establish `hdetq : IsUnit A₁q.det`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Apply `hdet` to reduce the goal to its premises.

Use `(Rat.castHom ℝ).map_det A₁q` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Rewrite using `[← hA₁]`. Conclude with `this.symm`. Establish `hdetR : IsUnit A₁.det` using `isUnit_iff_ne_zero.2 hdet`.

Use `⟨A₁q⁻¹ * A₂q, ?_⟩` and prove the remaining obligations. Establish `h3 : A₁ * (A₁q⁻¹ * A₂q).map (Rat.castHom ℝ) = A₂`. Use `congrArg (fun M => M.map (Rat.castHom ℝ)) (Matrix.mul_nonsing_inv_cancel_left A₁q A₂q hdetq)` as an intermediate fact. Rewrite `this` using `[Matrix.map_mul, hA₁, hA₂]`. Conclude with `this`.

Establish `h4 : (A₁q⁻¹ * A₂q).map (Rat.castHom ℝ) = T`. Combine the equalities or inequalities in the displayed calculation. Simplify using `using h4`.
-/
theorem herm_endo_matrix_rat : ∀ (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ),
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    (∀ k l, ∃ m : ℤ, (m : ℝ) = (e k ⬝ᵥ H₁.mulVec (star (e l))).im) →
    (∀ k l, ∃ m : ℤ, (m : ℝ) = (e k ⬝ᵥ H₂.mulVec (star (e l))).im) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) →
    ∃ Tq : Matrix (Fin n) (Fin n) ℚ,
      Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) := by
  intro g n e H₁ H₂ hpos h1 h2 γ hγ
  classical
  set T := LinearMap.toMatrix e e (γ.restrictScalars ℝ) with hT
  let A₁ : Matrix (Fin n) (Fin n) ℝ := fun k l => (e k ⬝ᵥ H₁ *ᵥ star (e l)).im
  let A₂ : Matrix (Fin n) (Fin n) ℝ := fun k l => (e k ⬝ᵥ H₂ *ᵥ star (e l)).im

  have hγe : ∀ l, γ (e l) = ∑ m, T m l • e m := by
    intro l
    have := e.sum_repr (γ (e l))
    rw [← this]
    simp [hT, LinearMap.toMatrix_apply]

  have key : A₁ * T = A₂ := by
    ext k l
    rw [mul_apply]
    show _ = (e k ⬝ᵥ H₂ *ᵥ star (e l)).im
    rw [hγ, hγe l]
    have := map_sum (imFormRight H₁ (e k)) (fun m : Fin n => T m l • e m) (Finset.univ : Finset (Fin n))
    simp only [map_smul, smul_eq_mul] at this
    change _ = imFormRight H₁ (e k) _
    rw [this]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_comm]; rfl

  have hdet : A₁.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    set v := ∑ l, x l • e l with hv
    have hk : ∀ k, imFormRight H₁ (e k) v = 0 := by
      intro k
      have := congrFun hx k
      rw [hv, map_sum]
      simp only [map_smul, smul_eq_mul]
      simp only [mulVec, dotProduct, Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_comm]; rfl
    have hu : ∀ u, imFormLeft H₁ v u = 0 := by
      intro u
      rw [← e.sum_repr u, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [map_smul]
      have := hk k
      simp only [imFormRight, imFormLeft, LinearMap.coe_mk, AddHom.coe_mk] at this ⊢
      rw [this, smul_zero]
    have hre : (v ⬝ᵥ H₁ *ᵥ star v).re = 0 := by
      have := hu (Complex.I • v)
      simp only [imFormLeft, LinearMap.coe_mk, AddHom.coe_mk, smul_dotProduct, smul_eq_mul,
        Complex.mul_im, Complex.I_re, Complex.I_im] at this
      simpa using this
    have hv0 : v = 0 := by
      by_contra hne
      have := hpos v hne
      linarith
    apply hx0
    have : e.equivFun.symm x = 0 := by rw [Module.Basis.equivFun_symm_apply]; exact hv0
    exact e.equivFun.symm.injective (by rw [this, map_zero])

  choose m₁ hm₁ using h1
  choose m₂ hm₂ using h2
  let A₁q : Matrix (Fin n) (Fin n) ℚ := fun k l => (m₁ k l : ℚ)
  let A₂q : Matrix (Fin n) (Fin n) ℚ := fun k l => (m₂ k l : ℚ)
  have hA₁ : A₁q.map (Rat.castHom ℝ) = A₁ := by
    ext k l
    show ((m₁ k l : ℚ) : ℝ) = _
    rw [Rat.cast_intCast, hm₁]
  have hA₂ : A₂q.map (Rat.castHom ℝ) = A₂ := by
    ext k l
    show ((m₂ k l : ℚ) : ℝ) = _
    rw [Rat.cast_intCast, hm₂]
  have hdetq : IsUnit A₁q.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hdet
    have := (Rat.castHom ℝ).map_det A₁q
    rw [h0, map_zero] at this
    rw [← hA₁]
    exact this.symm
  have hdetR : IsUnit A₁.det := isUnit_iff_ne_zero.2 hdet
  refine ⟨A₁q⁻¹ * A₂q, ?_⟩
  have h3 : A₁ * (A₁q⁻¹ * A₂q).map (Rat.castHom ℝ) = A₂ := by
    have := congrArg (fun M => M.map (Rat.castHom ℝ)) (Matrix.mul_nonsing_inv_cancel_left A₁q A₂q hdetq)
    rw [Matrix.map_mul, hA₁, hA₂] at this
    exact this
  have h4 : (A₁q⁻¹ * A₂q).map (Rat.castHom ℝ) = T := by
    calc (A₁q⁻¹ * A₂q).map (Rat.castHom ℝ)
        = A₁⁻¹ * (A₁ * (A₁q⁻¹ * A₂q).map (Rat.castHom ℝ)) :=
          (Matrix.nonsing_inv_mul_cancel_left A₁ _ hdetR).symm
      _ = A₁⁻¹ * (A₁ * T) := by rw [h3, key]
      _ = T := Matrix.nonsing_inv_mul_cancel_left A₁ T hdetR
  simpa using h4

end GlobalTheory
