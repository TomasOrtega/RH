import Mathlib
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt

open Matrix

namespace GlobalTheory.Mem.InvDer

/- English proof (translation)
Establish `hd` using `ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det M M' 0 hM`. Rewrite `hd` using `[h0, adjugate_one, Matrix.one_mul]`. Establish `hdet0 : (M 0).det = 1` using `by rw [h0, det_one]`. Establish `hne : (M 0).det ≠ 0` using `by rw [hdet0]; exact one_ne_zero`. Establish `hinv : HasDerivAt (fun t => ((M t).det)⁻¹) (-M'.trace) 0`.

Establish `h1 : HasDerivAt (fun z : ℂ => z⁻¹) (-((M 0).det ^ 2)⁻¹) (M 0).det` using `hasDerivAt_inv hne`. Establish `h2` using `h1.comp_of_eq (0 : ℝ) hd rfl`. Use `HasDerivAt.congr_deriv h2 ?_` and prove the remaining obligations. Rewrite using `[hdet0]`. Simplify using the standard rewrite rules.

Use `⟨hinv, ?_⟩` and prove the remaining obligations. Establish `hdiff : ∀ i j, DifferentiableAt ℝ (fun t => (M t)⁻¹ i j) 0`. Introduce `i j`. Establish `hadj : DifferentiableAt ℝ (fun t => (M t).adjugate i j) 0`. Use `ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun t => (M t).updateRow j (Pi.single i 1)) (M'.updateRow j 0) 0 (by` as an intermediate fact.

Introduce `a b`. Distinguish the cases in `h : a = j`. Simplify using `only [updateRow_apply, h, if_true]`. Conclude with `hasDerivAt_const _ _`. Simplify using `only [updateRow_apply, h, if_false]`.

Conclude with `hM a b)`. Simplify `this.differentiableAt` using `only [adjugate_apply]`. Use `hinv.differentiableAt.mul hadj` as an intermediate fact. Use `this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `[Matrix.inv_def, Ring.inverse_eq_inv']`.

Introduce `i j`. Establish `hev : ∀ᶠ t in nhds (0 : ℝ), (M t).det ≠ 0` using `hd.continuousAt.eventually_ne hne`. Establish `hprod : HasDerivAt (fun t => ∑ k, (M t)⁻¹ i k * M t k j) (∑ k, (deriv (fun t => (M t)⁻¹ i k) 0 * M 0 k j + (M 0)⁻¹ i k * M' k j)) 0` using `HasDerivAt.fun_sum fun k _ => ((hdiff i k).hasDerivAt.fun_mul (hM k j))`. Establish `hconst : HasDerivAt (fun t => ∑ k, (M t)⁻¹ i k * M t k j) 0 0`. Use `(hasDerivAt_const (0 : ℝ) ((1 : Matrix (Fin n) (Fin n) ℂ) i j)).congr_of_eventuallyEq ?_` and prove the remaining obligations.

Use `filter_upwards [hev] with t ht`. Rewrite using `[← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht)]`. Establish `huniq` using `hprod.unique hconst`. Rewrite `huniq` using `[h0, inv_one, Finset.sum_add_distrib]`. Simplify using `[Matrix.one_apply] at huniq`.

Establish `hfin : deriv (fun t => (M t)⁻¹ i j) 0 = -M' i j` using `eq_neg_of_add_eq_zero_left huniq`. Rewrite using `[← hfin]`. Conclude with `(hdiff i j).hasDerivAt`.
-/
theorem hasDerivAt_inv_det_and_inv (n : ℕ) (M : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (M' : Matrix (Fin n) (Fin n) ℂ) (h0 : M 0 = 1)
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) 0) :
    HasDerivAt (fun t => ((M t).det)⁻¹) (-M'.trace) 0 ∧
      ∀ i j, HasDerivAt (fun t => (M t)⁻¹ i j) (-M' i j) 0 := by
  have hd := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det M M' 0 hM
  rw [h0, adjugate_one, Matrix.one_mul] at hd
  have hdet0 : (M 0).det = 1 := by rw [h0, det_one]
  have hne : (M 0).det ≠ 0 := by rw [hdet0]; exact one_ne_zero
  have hinv : HasDerivAt (fun t => ((M t).det)⁻¹) (-M'.trace) 0 := by
    have h1 : HasDerivAt (fun z : ℂ => z⁻¹) (-((M 0).det ^ 2)⁻¹) (M 0).det := hasDerivAt_inv hne
    have h2 := h1.comp_of_eq (0 : ℝ) hd rfl
    refine HasDerivAt.congr_deriv h2 ?_
    rw [hdet0]; simp
  refine ⟨hinv, ?_⟩
  have hdiff : ∀ i j, DifferentiableAt ℝ (fun t => (M t)⁻¹ i j) 0 := by
    intro i j
    have hadj : DifferentiableAt ℝ (fun t => (M t).adjugate i j) 0 := by
      have := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun t => (M t).updateRow j (Pi.single i 1))
        (M'.updateRow j 0) 0 (by
          intro a b
          by_cases h : a = j
          · simp only [updateRow_apply, h, if_true]
            exact hasDerivAt_const _ _
          · simp only [updateRow_apply, h, if_false]
            exact hM a b)
      simpa only [adjugate_apply] using this.differentiableAt
    have := hinv.differentiableAt.mul hadj
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp [Matrix.inv_def, Ring.inverse_eq_inv']
  intro i j
  have hev : ∀ᶠ t in nhds (0 : ℝ), (M t).det ≠ 0 := hd.continuousAt.eventually_ne hne
  have hprod : HasDerivAt (fun t => ∑ k, (M t)⁻¹ i k * M t k j)
      (∑ k, (deriv (fun t => (M t)⁻¹ i k) 0 * M 0 k j + (M 0)⁻¹ i k * M' k j)) 0 :=
    HasDerivAt.fun_sum fun k _ => ((hdiff i k).hasDerivAt.fun_mul (hM k j))
  have hconst : HasDerivAt (fun t => ∑ k, (M t)⁻¹ i k * M t k j) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) ((1 : Matrix (Fin n) (Fin n) ℂ) i j)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht)]
  have huniq := hprod.unique hconst
  rw [h0, inv_one, Finset.sum_add_distrib] at huniq
  simp [Matrix.one_apply] at huniq
  have hfin : deriv (fun t => (M t)⁻¹ i j) 0 = -M' i j := eq_neg_of_add_eq_zero_left huniq
  rw [← hfin]
  exact (hdiff i j).hasDerivAt

end GlobalTheory.Mem.InvDer
