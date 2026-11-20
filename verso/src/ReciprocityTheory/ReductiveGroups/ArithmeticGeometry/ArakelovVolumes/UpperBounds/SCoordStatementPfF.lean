import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.SCoG

noncomputable section

/- English proof (translation)
Use `set L := (((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).comp (ContinuousLinearMap.pi fun i => den⁻¹ • ∑ j, t (i.succ, j) • Dv j)) with hL`. Establish `hinj : Function.Injective L`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `ξ hξ`. Apply `key` to reduce the goal to its premises.

Establish `hmv : M.mulVec (fun k => w k ξ) = 0`. Use function extensionality and compare the values at `i`. Establish `h1` using `congrArg (fun v : EuclideanSpace ℂ (Fin n) => v i) hξ`. Simplify using `only [hL, ContinuousLinearMap.comp_apply] at h1`. Establish `h2 : den⁻¹ * (∑ j, t (i.succ, j) • Dv j) ξ = 0` using `by simpa using h1`.

Establish `h3` using `(mul_eq_zero.mp h2).resolve_left (inv_ne_zero hden)`. Rewrite `h3` using `[hrow i]`. Simplify `h3` using `[Matrix.mulVec, dotProduct]`. Conclude with `congrFun (Matrix.eq_zero_of_mulVec_eq_zero hM hmv)`. Establish `hU : IsUnit (L : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))`.

Rewrite using `[LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot]`. Conclude with `hinj`. Conclude with `(LinearMap.isUnit_det _ hU).ne_zero`.
-/
theorem finale {n N : ℕ} (Dv : Fin (N + 1) → (EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ))
    (t : Fin (n + 1) × Fin (N + 1) → ℂ) (M : Matrix (Fin n) (Fin n) ℂ)
    (w : Fin n → (EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ)) (hM : M.det ≠ 0)
    (key : ∀ ξ, (∀ k, w k ξ = 0) → ξ = 0)
    (hrow : ∀ i, ∑ j, t (i.succ, j) • Dv j = ∑ k, M i k • w k) (den : ℂ) (hden : den ≠ 0) :
    (((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).comp
      (ContinuousLinearMap.pi fun i => den⁻¹ • ∑ j, t (i.succ, j) • Dv j)).det ≠ 0 := by
  classical
  set L := (((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).comp
      (ContinuousLinearMap.pi fun i => den⁻¹ • ∑ j, t (i.succ, j) • Dv j)) with hL
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro ξ hξ
    apply key
    have hmv : M.mulVec (fun k => w k ξ) = 0 := by
      funext i
      have h1 := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v i) hξ
      simp only [hL, ContinuousLinearMap.comp_apply] at h1
      have h2 : den⁻¹ * (∑ j, t (i.succ, j) • Dv j) ξ = 0 := by simpa using h1
      have h3 := (mul_eq_zero.mp h2).resolve_left (inv_ne_zero hden)
      rw [hrow i] at h3
      simpa [Matrix.mulVec, dotProduct] using h3
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hM hmv)
  have hU : IsUnit (L : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
    rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot]
    exact hinj
  exact (LinearMap.isUnit_det _ hU).ne_zero

open Filter Topology in

/- English proof (translation)
Use `set Num : Fin n → EuclideanSpace ℂ (Fin n) → ℂ := fun i z => ∑ j, t (i.succ, j) * (W j (c z) / W j0 (c z)) with hNumd`. Use `set Den : EuclideanSpace ℂ (Fin n) → ℂ := fun z => ∑ j, t (0, j) * (W j (c z) / W j0 (c z)) with hDend`. Establish `hNum : ∀ i, HasFDerivAt (Num i) (∑ j, t (i.succ, j) • Dv j) 0` using `fun i => HasFDerivAt.fun_sum fun j _ => (hDv j).const_mul _`. Establish `hDen : HasFDerivAt Den (∑ j, t (0, j) • Dv j) 0` using `HasFDerivAt.fun_sum fun j _ => (hDv j).const_mul _`. Establish `hNum0 : ∀ i, Num i 0 = 0`.

Introduce `i`. Simplify using `only [hNumd, mul_div_assoc']`. Rewrite using `[← Finset.sum_div, hs i, zero_div]`. Establish `hDen0' : Den 0 = (∑ j, t (0, j) * W j (c 0)) / W j0 (c 0)`. Simplify using `only [hDend, mul_div_assoc']`.

Rewrite using `[← Finset.sum_div]`. Establish `hDen0 : Den 0 ≠ 0` using `by rw [hDen0']; exact div_ne_zero hw hx0`. Establish `hQ : ∀ i, HasFDerivAt (fun z => Num i z * (Den z)⁻¹) ((Den 0)⁻¹ • ∑ j, t (i.succ, j) • Dv j) 0`. Introduce `i`. Establish `hinv` using `(hDen.differentiableAt.inv hDen0).hasFDerivAt`.

Establish `h` using `(hNum i).mul hinv`. Rewrite `h` using `[hNum0 i, zero_smul, zero_add]`. Conclude with `h`. Rewrite using `[← hDen0']`. Establish `h1` using `((EuclideanSpace.equiv (Fin n) ℂ).symm.hasFDerivAt).comp (0 : EuclideanSpace ℂ (Fin n)) (hasFDerivAt_pi.2 hQ)`.

Use `h1.congr_of_eventuallyEq (hev.mono fun z hz => ?_)` and prove the remaining obligations. Use `show (WithLp.toLp 2 fun i => _ : EuclideanSpace ℂ (Fin n)) = WithLp.toLp 2 fun i => _`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [hNumd, hDend, mul_div_assoc']`.

Rewrite using `[← Finset.sum_div, ← Finset.sum_div, inv_div, div_mul_div_cancel₀ hz]`.
-/
theorem target {Fr : Type*} [NormedAddCommGroup Fr] [NormedSpace ℂ Fr] {n N : ℕ}
    (W : Fin (N + 1) → Fr → ℂ) (c : EuclideanSpace ℂ (Fin n) → Fr) (j0 : Fin (N + 1))
    (hev : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℂ (Fin n)), W j0 (c z) ≠ 0)
    (Dv : Fin (N + 1) → (EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ))
    (hDv : ∀ j, HasFDerivAt (fun z => W j (c z) / W j0 (c z)) (Dv j) 0)
    (t : Fin (n + 1) × Fin (N + 1) → ℂ) (hx0 : W j0 (c 0) ≠ 0)
    (hs : ∀ i : Fin n, ∑ j, t (i.succ, j) * W j (c 0) = 0) (hw : ∑ j, t (0, j) * W j (c 0) ≠ 0) :
    HasFDerivAt (fun z : EuclideanSpace ℂ (Fin n) => (WithLp.toLp 2 fun i =>
      (∑ j, t (i.succ, j) * W j (c z)) / (∑ j, t (0, j) * W j (c z)) : EuclideanSpace ℂ (Fin n)))
      (((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).comp
        (ContinuousLinearMap.pi fun i =>
          ((∑ j, t (0, j) * W j (c 0)) / W j0 (c 0))⁻¹ • ∑ j, t (i.succ, j) • Dv j)) 0 := by
  set Num : Fin n → EuclideanSpace ℂ (Fin n) → ℂ := fun i z => ∑ j, t (i.succ, j) * (W j (c z) / W j0 (c z))
    with hNumd
  set Den : EuclideanSpace ℂ (Fin n) → ℂ := fun z => ∑ j, t (0, j) * (W j (c z) / W j0 (c z)) with hDend
  have hNum : ∀ i, HasFDerivAt (Num i) (∑ j, t (i.succ, j) • Dv j) 0 := fun i =>
    HasFDerivAt.fun_sum fun j _ => (hDv j).const_mul _
  have hDen : HasFDerivAt Den (∑ j, t (0, j) • Dv j) 0 :=
    HasFDerivAt.fun_sum fun j _ => (hDv j).const_mul _
  have hNum0 : ∀ i, Num i 0 = 0 := by
    intro i
    simp only [hNumd, mul_div_assoc']
    rw [← Finset.sum_div, hs i, zero_div]
  have hDen0' : Den 0 = (∑ j, t (0, j) * W j (c 0)) / W j0 (c 0) := by
    simp only [hDend, mul_div_assoc']
    rw [← Finset.sum_div]
  have hDen0 : Den 0 ≠ 0 := by rw [hDen0']; exact div_ne_zero hw hx0
  have hQ : ∀ i, HasFDerivAt (fun z => Num i z * (Den z)⁻¹) ((Den 0)⁻¹ • ∑ j, t (i.succ, j) • Dv j) 0 := by
    intro i
    have hinv := (hDen.differentiableAt.inv hDen0).hasFDerivAt
    have h := (hNum i).mul hinv
    rw [hNum0 i, zero_smul, zero_add] at h
    exact h
  rw [← hDen0']
  have h1 := ((EuclideanSpace.equiv (Fin n) ℂ).symm.hasFDerivAt).comp (0 : EuclideanSpace ℂ (Fin n))
    (hasFDerivAt_pi.2 hQ)
  refine h1.congr_of_eventuallyEq (hev.mono fun z hz => ?_)
  show (WithLp.toLp 2 fun i => _ : EuclideanSpace ℂ (Fin n)) = WithLp.toLp 2 fun i => _
  congr 1
  funext i
  simp only [hNumd, hDend, mul_div_assoc']
  rw [← Finset.sum_div, ← Finset.sum_div, inv_div, div_mul_div_cancel₀ hz]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.SCoG
