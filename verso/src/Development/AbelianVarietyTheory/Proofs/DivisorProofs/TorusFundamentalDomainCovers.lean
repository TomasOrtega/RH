import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory.FundDom

/- English proof (translation)
Establish `h : (fun i => (((x + y) (Sum.inl i) : ℝ) : ℂ)) = (fun i => (x (Sum.inl i) : ℂ)) + fun i => (y (Sum.inl i) : ℂ)`. Use extensionality with `i`. Simplify using the standard rewrite rules. Establish `h2 : (fun i => (((x + y) (Sum.inr i) : ℝ) : ℂ)) = (fun i => (x (Sum.inr i) : ℂ)) + fun i => (y (Sum.inr i) : ℂ)`. Use extensionality with `i`.

Simplify using the standard rewrite rules. Unfold `per`. Rewrite using `[h, h2, Matrix.add_vecMul]`. Normalize the expressions using the abelian group laws.
-/
theorem per_add {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (x y : Fl g) :
    per A (x + y) = per A x + per A y := by
  have h : (fun i => (((x + y) (Sum.inl i) : ℝ) : ℂ)) =
      (fun i => (x (Sum.inl i) : ℂ)) + fun i => (y (Sum.inl i) : ℂ) := by
    ext i; simp
  have h2 : (fun i => (((x + y) (Sum.inr i) : ℝ) : ℂ)) =
      (fun i => (x (Sum.inr i) : ℂ)) + fun i => (y (Sum.inr i) : ℂ) := by
    ext i; simp
  unfold per
  rw [h, h2, Matrix.add_vecMul]
  abel

/- English proof (translation)
Establish `hinv : (A.map Complex.im)⁻¹ * A.map Complex.im = 1` using `Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hA)`. Use `set p : Fin g → ℝ := (fun i => (z i).im) ᵥ* (A.map Complex.im)⁻¹ with hp`. Establish `hpi : p ᵥ* A.map Complex.im = fun i => (z i).im`. Rewrite using `[hp, Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]`. Use function extensionality and compare the values at `i`.

Apply `Complex.ext` to reduce the goal to its premises. Simplify using `only [per, flatOf, Sum.elim_inl, Sum.elim_inr, ← hp, Pi.add_apply, Complex.add_re, Complex.ofReal_re, Pi.sub_apply]`. Simplify using `only [Matrix.vecMul, dotProduct, Complex.re_sum, Complex.re_ofReal_mul, Matrix.map_apply]`. Expand and normalize the polynomial expressions, which then agree. Use `congrFun hpi i` as an intermediate fact.

Simplify using `only [per, flatOf, Sum.elim_inl, Sum.elim_inr, ← hp, Pi.add_apply, Complex.add_im, Complex.ofReal_im, add_zero]`. Simplify using `only [Matrix.vecMul, dotProduct, Complex.im_sum, Complex.im_ofReal_mul, Matrix.map_apply] at this ⊢`. Conclude with `this`.
-/
theorem per_flatOf {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (hA : (A.map Complex.im).det ≠ 0)
    (z : Fin g → ℂ) : per A (flatOf A z) = z := by
  have hinv : (A.map Complex.im)⁻¹ * A.map Complex.im = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hA)
  set p : Fin g → ℝ := (fun i => (z i).im) ᵥ* (A.map Complex.im)⁻¹ with hp
  have hpi : p ᵥ* A.map Complex.im = fun i => (z i).im := by
    rw [hp, Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
  funext i
  apply Complex.ext
  · simp only [per, flatOf, Sum.elim_inl, Sum.elim_inr, ← hp, Pi.add_apply, Complex.add_re,
      Complex.ofReal_re, Pi.sub_apply]
    simp only [Matrix.vecMul, dotProduct, Complex.re_sum, Complex.re_ofReal_mul,
      Matrix.map_apply]
    ring
  · have := congrFun hpi i
    simp only [per, flatOf, Sum.elim_inl, Sum.elim_inr, ← hp, Pi.add_apply, Complex.add_im,
      Complex.ofReal_im, add_zero]
    simp only [Matrix.vecMul, dotProduct, Complex.im_sum, Complex.im_ofReal_mul,
      Matrix.map_apply] at this ⊢
    exact this

/- English proof (translation)
Introduce `g A hA z`. Use `set y := flatOf A z`. Use `⟨fun i => Int.fract (y i), ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩, fun i => ((⌊y i⌋ : ℤ) : ℝ), ?_, ?_⟩` and prove the remaining obligations. Establish `: (fun i => ((⌊y i⌋ : ℤ) : ℝ)) = ∑ i, (⌊y i⌋ : ℤ) • Pi.basisFun ℝ (Fin g ⊕ Fin g) i`. Use extensionality with `j`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[← per_add]`. Establish `: (fun i => Int.fract (y i)) + (fun i => ((⌊y i⌋ : ℤ) : ℝ)) = y`.

Use extensionality with `i`. Simplify using `[Int.fract_add_floor]`. Rewrite using `[this, per_flatOf A hA]`.
-/
theorem fund_dom : ∀ {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ), (A.map Complex.im).det ≠ 0 →
    ∀ z : Fin g → ℂ, ∃ x ∈ Set.Icc (0 : Fl g) 1, ∃ l ∈ stdLat g, z = per A x + per A l := by
  intro g A hA z
  set y := flatOf A z
  refine ⟨fun i => Int.fract (y i), ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩,
    fun i => ((⌊y i⌋ : ℤ) : ℝ), ?_, ?_⟩
  · have : (fun i => ((⌊y i⌋ : ℤ) : ℝ)) = ∑ i, (⌊y i⌋ : ℤ) • Pi.basisFun ℝ (Fin g ⊕ Fin g) i := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩)
  · rw [← per_add]
    have : (fun i => Int.fract (y i)) + (fun i => ((⌊y i⌋ : ℤ) : ℝ)) = y := by
      ext i; simp [Int.fract_add_floor]
    rw [this, per_flatOf A hA]

end GlobalTheory.FundDom
