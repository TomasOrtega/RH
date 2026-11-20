import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Use `set e : (E →L[ℝ] ℝ) ≃L[ℝ] (E →L[ℝ] ℝ) := c.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ) with he`. Establish `h1 : fderiv ℝ (φ ∘ c) = e ∘ fderiv ℝ φ ∘ c`. Use function extensionality and compare the values at `z`. Rewrite using `[c.comp_right_fderiv]`. Use extensionality with `w`.

Simplify using `[he]`. Rewrite using `[h1, e.comp_fderiv, c.comp_right_fderiv]`. Simplify using `[he]`.
-/
theorem madens_hess {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E ≃L[ℝ] E) (φ : E → ℝ) (y u v : E) :
    fderiv ℝ (fderiv ℝ (φ ∘ c)) y u v = fderiv ℝ (fderiv ℝ φ) (c y) (c u) (c v) := by
  set e : (E →L[ℝ] ℝ) ≃L[ℝ] (E →L[ℝ] ℝ) := c.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ) with he
  have h1 : fderiv ℝ (φ ∘ c) = e ∘ fderiv ℝ φ ∘ c := by
    funext z
    rw [c.comp_right_fderiv]
    ext w
    simp [he]
  rw [h1, e.comp_fderiv, c.comp_right_fderiv]
  simp [he]

/- English proof (translation)
Set `c : (Fin D → ℂ) ≃L[ℝ] (Fin D → ℂ)` to `ContinuousLinearEquiv.piCongrRight (fun _ => Complex.conjCLE)`. Establish `hc : ∀ z, c z = fun i => starRingEnd ℂ (z i)` using `fun z => rfl`. Establish `hf : (fun y' : Fin D → ℂ => φ (fun i => starRingEnd ℂ (y' i))) = φ ∘ c`. Use function extensionality and compare the values at `z`. Simplify using `[hc]`.

Establish `h1 : ∀ i : Fin D, c (Pi.single i 1) = Pi.single i 1`. Introduce `i`. Use function extensionality and compare the values at `k`. Rewrite using `[hc]`. Distinguish the cases in `h : k = i`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`. Establish `h2 : ∀ i : Fin D, c (Complex.I • Pi.single i 1) = -(Complex.I • Pi.single i 1)`. Introduce `i`.

Use function extensionality and compare the values at `k`. Rewrite using `[hc]`. Distinguish the cases in `h : k = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_apply, h]`. Use extensionality with `i j`. Simplify using `only [cxHessian, Matrix.map_apply, hf, madens_hess, h1, h2, map_neg, ContinuousLinearMap.neg_apply, neg_neg]`. Rewrite using `[hc y]`. Generalize the expression as in `fderiv ℝ (fderiv ℝ φ) (fun i => starRingEnd ℂ (y i)) = H`.

Simplify using `only [map_div₀, map_add, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, sub_neg_eq_add, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem madens_cx (D : ℕ) (φ : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ) :
    cxHessian (fun y' => φ (fun i => starRingEnd ℂ (y' i))) y =
      (cxHessian φ (fun i => starRingEnd ℂ (y i))).map (starRingEnd ℂ) := by
  let c : (Fin D → ℂ) ≃L[ℝ] (Fin D → ℂ) := ContinuousLinearEquiv.piCongrRight (fun _ => Complex.conjCLE)
  have hc : ∀ z, c z = fun i => starRingEnd ℂ (z i) := fun z => rfl
  have hf : (fun y' : Fin D → ℂ => φ (fun i => starRingEnd ℂ (y' i))) = φ ∘ c := by
    funext z; simp [hc]
  have h1 : ∀ i : Fin D, c (Pi.single i 1) = Pi.single i 1 := by
    intro i; funext k; rw [hc]; by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have h2 : ∀ i : Fin D, c (Complex.I • Pi.single i 1) = -(Complex.I • Pi.single i 1) := by
    intro i; funext k; rw [hc]; by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  ext i j
  simp only [cxHessian, Matrix.map_apply, hf, madens_hess, h1, h2, map_neg, ContinuousLinearMap.neg_apply, neg_neg]
  rw [hc y]
  generalize fderiv ℝ (fderiv ℝ φ) (fun i => starRingEnd ℂ (y i)) = H
  simp only [map_div₀, map_add, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, sub_neg_eq_add, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_neg]
  ring

/- English proof (translation)
Introduce `D φ y`. Establish `key : ∀ A : Fin D → Matrix (Fin D) (Fin D) ℂ, mixedDisc (fun k => (A k).map (starRingEnd ℂ)) = starRingEnd ℂ (mixedDisc A)`. Introduce `A`. Simplify using `only [mixedDisc, map_mul, map_div₀, map_one, map_natCast, map_sum, map_pow, map_neg]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun S _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `a b`.

Simplify using `[Matrix.sum_apply]`. Simplify using `only [maDensity, madens_cx, key, Complex.conj_re]`.
-/
theorem c_madens : ∀ (D : ℕ) (φ : Fin D → (Fin D → ℂ) → ℝ) (y : Fin D → ℂ), maDensity (fun j y' => φ j (fun i => starRingEnd ℂ (y' i))) y = maDensity φ (fun i => starRingEnd ℂ (y i)) := by
  intro D φ y
  have key : ∀ A : Fin D → Matrix (Fin D) (Fin D) ℂ,
      mixedDisc (fun k => (A k).map (starRingEnd ℂ)) = starRingEnd ℂ (mixedDisc A) := by
    intro A
    simp only [mixedDisc, map_mul, map_div₀, map_one, map_natCast, map_sum, map_pow, map_neg]
    congr 1
    refine Finset.sum_congr rfl fun S _ => ?_
    congr 1
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp [Matrix.sum_apply]
  simp only [maDensity, madens_cx, key, Complex.conj_re]

end PositivityTheory.UnitarySelfGeneration
