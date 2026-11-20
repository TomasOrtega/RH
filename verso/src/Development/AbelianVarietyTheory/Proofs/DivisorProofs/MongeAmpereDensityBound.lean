import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LinearIndependentRealOfIntOfDiscrete

open ReciprocityTheory.AnForm

namespace GlobalTheory

open scoped ComplexOrder
open Matrix

/- English proof (translation)
Use `set H := hessC f z with hH`. Establish `hform : ∀ w : Fin e → ℂ, ((levi f z w : ℝ) : ℂ) = HermFrame.form H w w`. Introduce `w`. Rewrite using `[← HermFrame.leviForm_self_eq_levi hf, HermFrame.leviForm_eq_form_hessC hf]`. Establish `hpsd : H.PosSemidef`.

Use `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (ReciprocityTheory.AnForm.A.hessC_isHermitian f z hf) fun x => ?_` and prove the remaining obligations. Establish `h1 : star x ⬝ᵥ (H *ᵥ x) = ((levi f z (star x) : ℝ) : ℂ)`. Rewrite using `[hform]`. Simplify using `[HermFrame.form]`. Rewrite using `[h1]`.

Conclude with `hpos (star x)` after adjusting the coercions. Establish `hdiag : ∀ k, (H k k).re = levi f z (Pi.single k 1)`. Introduce `k`. Establish `h1` using `hform (Pi.single k 1)`. Establish `h2 : HermFrame.form H (Pi.single k 1) (Pi.single k 1) = H k k`.

Simplify using `[HermFrame.form, Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite `h1` using `[h2]`. Rewrite using `[← h1, Complex.ofReal_re]`. Establish `hck : ∀ k, levi f z (Pi.single k 1) ≤ c k`. Introduce `k`.

Establish `h` using `hle (Pi.single k 1)`. Establish `hs : ∑ j, c j * ‖(Pi.single k (1 : ℂ) : Fin e → ℂ) j‖ ^ 2 = c k`. Rewrite using `[Finset.sum_eq_single k]`. Simplify using the standard rewrite rules. Introduce `j _ hj`.

Simplify using `[Pi.single_apply, hj]`. Simplify using the standard rewrite rules. Rewrite `h` using `[hs]`. Then use the resulting hypothesis. Establish `hdet : (H.det).re ≤ ∏ k, c k`. Establish `h` using `GlobalTheory.posSemidef_re_det_le_prod_diag hpsd`.

Use `h.trans ?_` and prove the remaining obligations. Use `Finset.prod_le_prod (fun k _ => ?_) fun k _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `0 ≤ (H k k).re`. Rewrite using `[hdiag]`. Conclude with `hpos _`.

Express the relevant statement in the definitionally equal form `(H k k).re ≤ c k`. Rewrite using `[hdiag]`. Conclude with `hck k`. Establish `hfac : (0 : ℝ) ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e` using `by positivity`. Unfold `maDens`.

Rewrite using `[ReciprocityTheory.AnForm.A.mdisc_const]`. Conclude with `mul_le_mul_of_nonneg_left hdet hfac`.
-/
theorem maDens_le_prod_of_levi_le_diag {e : ℕ} (f : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ)
    (c : Fin e → ℝ) (hf : ContDiffAt ℝ 2 f z) (hpos : ∀ w, 0 ≤ levi f z w)
    (hle : ∀ w, levi f z w ≤ ∑ k, c k * ‖w k‖ ^ 2) :
    maDens (fun _ => f) z ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e * ∏ k, c k := by
  set H := hessC f z with hH

  have hform : ∀ w : Fin e → ℂ, ((levi f z w : ℝ) : ℂ) = HermFrame.form H w w := by
    intro w
    rw [← HermFrame.leviForm_self_eq_levi hf, HermFrame.leviForm_eq_form_hessC hf]
  have hpsd : H.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (ReciprocityTheory.AnForm.A.hessC_isHermitian f z hf)
      fun x => ?_
    have h1 : star x ⬝ᵥ (H *ᵥ x) = ((levi f z (star x) : ℝ) : ℂ) := by
      rw [hform]; simp [HermFrame.form]
    rw [h1]
    exact_mod_cast hpos (star x)
  have hdiag : ∀ k, (H k k).re = levi f z (Pi.single k 1) := by
    intro k
    have h1 := hform (Pi.single k 1)
    have h2 : HermFrame.form H (Pi.single k 1) (Pi.single k 1) = H k k := by
      simp [HermFrame.form, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h2] at h1
    rw [← h1, Complex.ofReal_re]
  have hck : ∀ k, levi f z (Pi.single k 1) ≤ c k := by
    intro k
    have h := hle (Pi.single k 1)
    have hs : ∑ j, c j * ‖(Pi.single k (1 : ℂ) : Fin e → ℂ) j‖ ^ 2 = c k := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hj; simp [Pi.single_apply, hj]
      · simp
    rwa [hs] at h
  have hdet : (H.det).re ≤ ∏ k, c k := by
    have h := GlobalTheory.posSemidef_re_det_le_prod_diag hpsd
    refine h.trans ?_
    refine Finset.prod_le_prod (fun k _ => ?_) fun k _ => ?_
    · change 0 ≤ (H k k).re
      rw [hdiag]; exact hpos _
    · change (H k k).re ≤ c k
      rw [hdiag]; exact hck k
  have hfac : (0 : ℝ) ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e := by positivity
  unfold maDens
  rw [ReciprocityTheory.AnForm.A.mdisc_const]
  exact mul_le_mul_of_nonneg_left hdet hfac

end GlobalTheory
