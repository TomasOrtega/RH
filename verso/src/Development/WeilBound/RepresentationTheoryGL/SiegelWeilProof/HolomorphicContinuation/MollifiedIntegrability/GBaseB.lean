import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBaseA

noncomputable section

open MeasureTheory Complex Matrix

namespace PositivityTheory.Rg.Sw.WR.G.GB

variable {n : ℕ}

/- English proof (translation)
Establish `h` using `congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.mp hU)`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]`. Establish `h2 : ((Complex.normSq U.det : ℝ) : ℂ) = 1`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Conclude with `h`.

Conclude with `h2` after adjusting the coercions.
-/
theorem normSq_det_unitary (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Complex.normSq U.det = 1 := by
  have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.mp hU)
  rw [Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose] at h
  have h2 : ((Complex.normSq U.det : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]; exact h
  exact_mod_cast h2

/- English proof (translation)
Establish `h1 : U * star U = 1` using `Matrix.mem_unitaryGroup_iff.mp hU`. Establish `h2 : star U * U = 1` using `Matrix.mem_unitaryGroup_iff'.mp hU`. Set `eC : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)` to `LinearEquiv.ofLinear (Matrix.toLin' U) (Matrix.toLin' (star U)) (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])`. Set `eR : (Fin n → ℂ) ≃ₗ[ℝ] (Fin n → ℂ)` to `eC.restrictScalars ℝ`. Set `e : (Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ)` to `eR.toContinuousLinearEquiv`.

Set `me : (Fin n → ℂ) ≃ᵐ (Fin n → ℂ)` to `e.toHomeomorph.toMeasurableEquiv`. Establish `hcoe : ∀ r, me r = U *ᵥ r` using `fun r => by`. Simplify using `[me, e, eR, eC, Matrix.toLin'_apply]`. Establish `hdet : LinearMap.det ((eC : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).restrictScalars ℝ) = 1`. Rewrite using `[LinearMap.det_restrictScalars]`.

Establish `: (eC : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = Matrix.toLin' U` using `rfl`. Rewrite using `[this, LinearMap.det_toLin', Algebra.norm_complex_apply, normSq_det_unitary U hU]`. Establish `hmap : Measure.map (((eC : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).restrictScalars ℝ)) volume = (volume : Measure (Fin n → ℂ))`. Rewrite using `[Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; exact one_ne_zero), hdet]`. Simplify using the standard rewrite rules.

Establish `hpres : MeasurePreserving me volume volume`. Use `⟨me.measurable, ?_⟩` and prove the remaining obligations. Establish `: (me : (Fin n → ℂ) → (Fin n → ℂ)) = (((eC : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).restrictScalars ℝ) : (Fin n → ℂ) → (Fin n → ℂ))`. Use function extensionality and compare the values at `r`. Rewrite using `[hcoe r]`.

Simplify using `[eC, Matrix.toLin'_apply]`. Rewrite using `[this, hmap]`. Use `hpres.integral_comp' g` as an intermediate fact. Simplify `this` using `[hcoe]`.
-/
theorem integral_unitary (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (g : (Fin n → ℂ) → ℂ) : ∫ r, g (U *ᵥ r) = ∫ r, g r := by
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  let eC : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
    LinearEquiv.ofLinear (Matrix.toLin' U) (Matrix.toLin' (star U))
      (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  let eR : (Fin n → ℂ) ≃ₗ[ℝ] (Fin n → ℂ) := eC.restrictScalars ℝ
  let e : (Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ) := eR.toContinuousLinearEquiv
  let me : (Fin n → ℂ) ≃ᵐ (Fin n → ℂ) := e.toHomeomorph.toMeasurableEquiv
  have hcoe : ∀ r, me r = U *ᵥ r := fun r => by
    simp [me, e, eR, eC, Matrix.toLin'_apply]
  have hdet : LinearMap.det ((eC : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars]
    have : (eC : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = Matrix.toLin' U := rfl
    rw [this, LinearMap.det_toLin', Algebra.norm_complex_apply, normSq_det_unitary U hU]
  have hmap : Measure.map (((eC : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).restrictScalars ℝ)) volume =
      (volume : Measure (Fin n → ℂ)) := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; exact one_ne_zero), hdet]
    simp
  have hpres : MeasurePreserving me volume volume := by
    refine ⟨me.measurable, ?_⟩
    have : (me : (Fin n → ℂ) → (Fin n → ℂ)) =
        (((eC : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).restrictScalars ℝ) : (Fin n → ℂ) → (Fin n → ℂ)) := by
      funext r; rw [hcoe r]; simp [eC, Matrix.toLin'_apply]
    rw [this, hmap]
  have := hpres.integral_comp' g
  simpa [hcoe] using this

/- English proof (translation)
Use `set U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef`. Establish `hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ` using `(hH.eigenvectorUnitary).2`. Use `set lam : Fin n → ℂ := RCLike.ofReal ∘ hH.eigenvalues with hlam`. Establish `hspec : H = U * Matrix.diagonal lam * star U`. Use `hH.spectral_theorem` as an intermediate fact.

Rewrite `this` using `[Unitary.conjStarAlgAut_apply]`. Conclude with `this`. Establish `h1 : U * star U = 1` using `Matrix.mem_unitaryGroup_iff.mp hU`. Establish `h2 : star U * U = 1` using `Matrix.mem_unitaryGroup_iff'.mp hU`. Establish `hV : star U ∈ Matrix.unitaryGroup (Fin n) ℂ` using `Matrix.mem_unitaryGroup_iff.mpr (by rw [star_star]; exact h2)`.

Use `set G : (Fin n → ℂ) → ℂ := fun r' => cexp (-∑ k, ((c : ℂ) - Complex.I * τ * lam k) * ((‖r' k‖ ^ 2 : ℝ) : ℂ)) with hG`. Establish `hpt : ∀ r : Fin n → ℂ, cexp (-(((c * ∑ k, ‖r k‖ ^ 2 : ℝ)) : ℂ) + Complex.I * τ * ∑ i, ∑ j, star (r i) * H i j * r j) = G (star U *ᵥ r)`. Introduce `r`. Simplify using `only [hG]`. Use `congr 1`.

Establish `hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z` using `fun z => by`. Rewrite using `[← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]`. Both sides reduce to the same expression. Establish `e1 : ∑ i, ∑ j, star (r i) * H i j * r j = star r ⬝ᵥ (H *ᵥ r)`. Simplify using `only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]`.

Establish `e2 : star r ⬝ᵥ (H *ᵥ r) = star (star U *ᵥ r) ⬝ᵥ (Matrix.diagonal lam *ᵥ (star U *ᵥ r))`. Rewrite using `[hspec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]`. Use `congr 1`. Rewrite using `[Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]`. Establish `e3 : star r ⬝ᵥ r = star (star U *ᵥ r) ⬝ᵥ (star U *ᵥ r)`.

Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose, h1, Matrix.one_mulVec]`. Establish `hn' : ∀ z : ℂ, ((‖z‖ : ℂ)) ^ 2 = star z * z` using `fun z => by rw [← hn z]; push_cast; ring`. Establish `e4 : (((c * ∑ k, ‖r k‖ ^ 2 : ℝ)) : ℂ) = (c : ℂ) * (star r ⬝ᵥ r)`. Use `push_cast`. Simplify using `only [dotProduct, Pi.star_apply, hn']`.

Rewrite using `[e4, e1, e2, e3]`. Simplify using `only [dotProduct, Pi.star_apply, Matrix.mulVec_diagonal, hn, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[hpt]`.

Rewrite using `[integral_unitary (star U) hV G]`. Simplify using `only [hG]`. Rewrite using `[gauss_diag (fun k => (c : ℂ) - Complex.I * τ * lam k) (fun k => by simp [hlam, hc])]`. Establish `hdet : ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * τ) • H).det = ∏ k, ((c : ℂ) - Complex.I * τ * lam k)`. Establish `: (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * τ) • H = U * Matrix.diagonal (fun k => (c : ℂ) - Complex.I * τ * lam k) * star U`.

Rewrite using `[hspec]`. Establish `hd : Matrix.diagonal (fun k => (c : ℂ) - Complex.I * τ * lam k) = (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * τ) • Matrix.diagonal lam`. Apply the tactic sequence `ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]`. Rewrite using `[hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, h1, Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[this, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]`.

Establish `hdu : U.det * (star U).det = 1` using `by rw [← Matrix.det_mul, h1, Matrix.det_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hdet, Finset.prod_div_distrib]`. Simplify using the standard rewrite rules.
-/
theorem gauss_row (c τ : ℝ) (hc : 0 < c) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    ∫ r : Fin n → ℂ, cexp (-(((c * ∑ k, ‖r k‖ ^ 2 : ℝ)) : ℂ) +
        Complex.I * τ * ∑ i, ∑ j, star (r i) * H i j * r j) =
      (Real.pi : ℂ) ^ n / ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * τ) • H).det := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ := (hH.eigenvectorUnitary).2
  set lam : Fin n → ℂ := RCLike.ofReal ∘ hH.eigenvalues with hlam
  have hspec : H = U * Matrix.diagonal lam * star U := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hV : star U ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff.mpr (by rw [star_star]; exact h2)

  set G : (Fin n → ℂ) → ℂ := fun r' => cexp (-∑ k, ((c : ℂ) - Complex.I * τ * lam k) * ((‖r' k‖ ^ 2 : ℝ) : ℂ))
    with hG
  have hpt : ∀ r : Fin n → ℂ, cexp (-(((c * ∑ k, ‖r k‖ ^ 2 : ℝ)) : ℂ) +
      Complex.I * τ * ∑ i, ∑ j, star (r i) * H i j * r j) = G (star U *ᵥ r) := by
    intro r
    simp only [hG]
    congr 1
    have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := fun z => by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]; rfl
    have e1 : ∑ i, ∑ j, star (r i) * H i j * r j = star r ⬝ᵥ (H *ᵥ r) := by
      simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
    have e2 : star r ⬝ᵥ (H *ᵥ r) = star (star U *ᵥ r) ⬝ᵥ (Matrix.diagonal lam *ᵥ (star U *ᵥ r)) := by
      rw [hspec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
      congr 1
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    have e3 : star r ⬝ᵥ r = star (star U *ᵥ r) ⬝ᵥ (star U *ᵥ r) := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose, h1, Matrix.one_mulVec]
    have hn' : ∀ z : ℂ, ((‖z‖ : ℂ)) ^ 2 = star z * z := fun z => by rw [← hn z]; push_cast; ring
    have e4 : (((c * ∑ k, ‖r k‖ ^ 2 : ℝ)) : ℂ) = (c : ℂ) * (star r ⬝ᵥ r) := by
      push_cast
      simp only [dotProduct, Pi.star_apply, hn']
    rw [e4, e1, e2, e3]
    simp only [dotProduct, Pi.star_apply, Matrix.mulVec_diagonal, hn, Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [hpt]
  rw [integral_unitary (star U) hV G]
  simp only [hG]
  rw [gauss_diag (fun k => (c : ℂ) - Complex.I * τ * lam k) (fun k => by simp [hlam, hc])]
  have hdet : ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * τ) • H).det =
      ∏ k, ((c : ℂ) - Complex.I * τ * lam k) := by
    have : (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * τ) • H =
        U * Matrix.diagonal (fun k => (c : ℂ) - Complex.I * τ * lam k) * star U := by
      rw [hspec]
      have hd : Matrix.diagonal (fun k => (c : ℂ) - Complex.I * τ * lam k) =
          (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * τ) • Matrix.diagonal lam := by
        ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
      rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, h1,
        Matrix.mul_smul, Matrix.smul_mul]
    rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hdu : U.det * (star U).det = 1 := by rw [← Matrix.det_mul, h1, Matrix.det_one]
    calc (U.det * ∏ k, ((c : ℂ) - Complex.I * τ * lam k)) * (star U).det
        = (U.det * (star U).det) * ∏ k, ((c : ℂ) - Complex.I * τ * lam k) := by ring
      _ = _ := by rw [hdu, one_mul]
  rw [hdet, Finset.prod_div_distrib]
  simp

end PositivityTheory.Rg.Sw.WR.G.GB
