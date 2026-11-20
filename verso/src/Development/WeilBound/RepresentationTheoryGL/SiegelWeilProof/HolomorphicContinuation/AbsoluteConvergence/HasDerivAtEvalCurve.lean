import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousEvX

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def scal (α : Fin n → ℝ) (x : Fin m → Fin n → ℂ) : Fin m → Fin n → ℂ := fun a j => (α j : ℂ) * x a j

def aH (X : Fin n → ℝ) (h : ℝ) : Fin n → ℝ := fun j => Real.exp (h * X j)

/- English proof (translation)
Use function extensionality and compare the values at `k`. Unfold `ept scal`. Use `split_ifs`. Simplify using `[star_mul', Complex.conj_ofReal]`. Both sides reduce to the same expression.
-/
theorem ept_scal (α : Fin n → ℝ) (x : Fin m → Fin n → ℂ) :
    ept (scal α x) = fun k => (α k.2.1 : ℂ) * ept x k := by
  funext k
  unfold ept scal
  split_ifs
  · simp [star_mul', Complex.conj_ofReal]
  · rfl

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C a => simpa using hasDerivAt_const h a`. Consider the case `add p q hp hq`. Establish `e : (∑ k, eval (w h) (pderiv k (p + q)) * w' k) = (∑ k, eval (w h) (pderiv k p) * w' k) + ∑ k, eval (w h) (pderiv k q) * w' k`. Simplify using `[map_add, add_mul, Finset.sum_add_distrib]`.

Rewrite using `[e]`. Conclude with `(hp.add hq).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp)`. Consider the case `mul_X p i hp`. Establish `e : ∑ k, eval (w h) (pderiv k (p * X i)) * w' k = (∑ k, eval (w h) (pderiv k p) * w' k) * w h i + eval (w h) p * w' i`. Establish `e1 : ∀ k, eval (w h) (pderiv k (p * X i)) * w' k = eval (w h) (pderiv k p) * w' k * w h i + (if k = i then eval (w h) p * w' i else 0)`.

Introduce `k`. Rewrite using `[Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, eval_X]`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[Pi.single_apply, hk]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]`. Rewrite using `[e]`.

Conclude with `(hp.mul (hw i)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp)`.
-/
theorem hasDerivAt_eval_curve {σ : Type*} [Fintype σ] [DecidableEq σ] (Q : MvPolynomial σ ℂ) (w : ℝ → σ → ℂ)
    (w' : σ → ℂ) (h : ℝ) (hw : ∀ k, HasDerivAt (fun s => w s k) (w' k) h) :
    HasDerivAt (fun s => eval (w s) Q) (∑ k, eval (w h) (pderiv k Q) * w' k) h := by
  induction Q using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const h a
  | add p q hp hq =>
    have e : (∑ k, eval (w h) (pderiv k (p + q)) * w' k) =
        (∑ k, eval (w h) (pderiv k p) * w' k) + ∑ k, eval (w h) (pderiv k q) * w' k := by
      simp [map_add, add_mul, Finset.sum_add_distrib]
    rw [e]
    exact (hp.add hq).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp)
  | mul_X p i hp =>
    have e : ∑ k, eval (w h) (pderiv k (p * X i)) * w' k =
        (∑ k, eval (w h) (pderiv k p) * w' k) * w h i + eval (w h) p * w' i := by
      have e1 : ∀ k, eval (w h) (pderiv k (p * X i)) * w' k =
          eval (w h) (pderiv k p) * w' k * w h i + (if k = i then eval (w h) p * w' i else 0) := by
        intro k
        rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, eval_X]
        by_cases hk : k = i
        · subst hk; simp; ring
        · simp [Pi.single_apply, hk]; ring
      simp only [e1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
    rw [e]
    exact (hp.mul (hw i)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp)

/- English proof (translation)
Simplify using `only [ept_scal, aH]`. Establish `h1 : HasDerivAt (fun s : ℝ => Real.exp (s * X k.2.1)) (Real.exp (h * X k.2.1) * X k.2.1) h`. Simplify using `using ((hasDerivAt_id h).mul_const (X k.2.1)).exp`. Establish `h2` using `(h1.ofReal_comp).mul_const (ept y k)`. Use `h2.congr_deriv ?_` and prove the remaining obligations.

Rewrite using `[Complex.ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_scal_coord (X : Fin n → ℝ) (y : Fin m → Fin n → ℂ) (h : ℝ) (k : Fin m × Fin n × Bool) :
    HasDerivAt (fun s => ept (scal (aH X s) y) k) ((X k.2.1 : ℂ) * ept (scal (aH X h) y) k) h := by
  simp only [ept_scal, aH]
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (s * X k.2.1)) (Real.exp (h * X k.2.1) * X k.2.1) h := by
    simpa using ((hasDerivAt_id h).mul_const (X k.2.1)).exp
  have h2 := (h1.ofReal_comp).mul_const (ept y k)
  refine h2.congr_deriv ?_
  rw [Complex.ofReal_mul]; ring

/- English proof (translation)
Set `Li : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ)` to `LinearMap.pi fun j => (α j • LinearMap.id).comp (LinearMap.proj j)`. Set `L : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ)` to `LinearMap.pi fun a => Li.comp (LinearMap.proj a)`. Establish `hL : ∀ y, L y = scal α y`. Introduce `y`. Use function extensionality and compare the values at `a j`.

Simplify using `[L, Li, scal, Complex.real_smul]`. Establish `hdetLi : LinearMap.det Li = ∏ j, α j ^ 2`. Simplify using `only [Li, LinearMap.det_pi, LinearMap.det_smul, LinearMap.det_id, Complex.finrank_real_complex, mul_one]`. Establish `hdet : LinearMap.det L = ∏ j, α j ^ (2 * m)`. Simplify using `only [L, LinearMap.det_pi, hdetLi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.

Rewrite using `[← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun j _ => by rw [← pow_mul, mul_comm]` and prove the remaining obligations. Establish `hD : 0 < ∏ j, α j ^ (2 * m)` using `Finset.prod_pos fun j _ => pow_pos (hα j) _`. Set `Linv : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ)` to `LinearMap.pi fun a => (LinearMap.pi fun j => ((α j)⁻¹ • LinearMap.id).comp (LinearMap.proj j)).comp (LinearMap.proj a)`. Set `Le : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] (Fin m → Fin n → ℂ)` to `LinearEquiv.ofLinear L Linv (LinearMap.ext fun y => funext fun a => funext fun j => by`.

Establish `h0 : (α j : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr (hα j).ne'`. Simplify using `only [L, Li, Linv, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.id_coe, id_eq, Complex.real_smul, Complex.ofReal_inv]`. Use the proof step `field_simp)`. Use the proof step `(LinearMap.ext fun y => funext fun a => funext fun j => by`. Establish `h0 : (α j : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr (hα j).ne'`.

Simplify using `only [L, Li, Linv, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.id_coe, id_eq, Complex.real_smul, Complex.ofReal_inv]`. Use the proof step `field_simp)`. Establish `hH1 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure` using `by infer_instance`. Establish `hH2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`. Set `e` to `Le.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv`.

Establish `he : ∀ y, e y = scal α y` using `fun y => hL y`. Establish `hmap : Measure.map e (volume : Measure (Fin m → Fin n → ℂ)) = ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume`. Establish `: (e : (Fin m → Fin n → ℂ) → (Fin m → Fin n → ℂ)) = L` using `by funext y; rfl`. Rewrite using `[this]`. Conclude with `Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; exact hD.ne')`.

Establish `h1 : ∫ y, f (scal α y) = (∏ j, α j ^ (2 * m))⁻¹ * ∫ x, f x`. Use `integral_map_equiv e f (μ := volume)` as an intermediate fact. Simplify using `only [he] at this`. Rewrite using `[← this, hmap, integral_smul_measure, hdet, ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.2 hD)]`. Simplify using `[Complex.real_smul]`.

Rewrite using `[h1, ← mul_assoc]`. Use `push_cast`. Rewrite using `[mul_inv_cancel₀ (by exact_mod_cast hD.ne'), one_mul]`.
-/
theorem integral_scal (α : Fin n → ℝ) (hα : ∀ j, 0 < α j) (f : (Fin m → Fin n → ℂ) → ℂ) :
    ∫ x, f x = (∏ j, α j ^ (2 * m) : ℝ) * ∫ y, f (scal α y) := by
  let Li : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := LinearMap.pi fun j => (α j • LinearMap.id).comp (LinearMap.proj j)
  let L : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearMap.pi fun a => Li.comp (LinearMap.proj a)
  have hL : ∀ y, L y = scal α y := by
    intro y; funext a j; simp [L, Li, scal, Complex.real_smul]
  have hdetLi : LinearMap.det Li = ∏ j, α j ^ 2 := by
    simp only [Li, LinearMap.det_pi, LinearMap.det_smul, LinearMap.det_id, Complex.finrank_real_complex, mul_one]
  have hdet : LinearMap.det L = ∏ j, α j ^ (2 * m) := by
    simp only [L, LinearMap.det_pi, hdetLi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => by rw [← pow_mul, mul_comm]
  have hD : 0 < ∏ j, α j ^ (2 * m) := Finset.prod_pos fun j _ => pow_pos (hα j) _
  let Linv : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearMap.pi fun a =>
    (LinearMap.pi fun j => ((α j)⁻¹ • LinearMap.id).comp (LinearMap.proj j)).comp (LinearMap.proj a)
  let Le : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearEquiv.ofLinear L Linv
    (LinearMap.ext fun y => funext fun a => funext fun j => by
      have h0 : (α j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα j).ne'
      simp only [L, Li, Linv, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply, LinearMap.smul_apply,
        LinearMap.id_apply, LinearMap.id_coe, id_eq, Complex.real_smul, Complex.ofReal_inv]
      field_simp)
    (LinearMap.ext fun y => funext fun a => funext fun j => by
      have h0 : (α j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα j).ne'
      simp only [L, Li, Linv, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply, LinearMap.smul_apply,
        LinearMap.id_apply, LinearMap.id_coe, id_eq, Complex.real_smul, Complex.ofReal_inv]
      field_simp)
  have hH1 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := by infer_instance
  have hH2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e := Le.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = scal α y := fun y => hL y
  have hmap : Measure.map e (volume : Measure (Fin m → Fin n → ℂ)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume := by
    have : (e : (Fin m → Fin n → ℂ) → (Fin m → Fin n → ℂ)) = L := by funext y; rfl
    rw [this]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; exact hD.ne')
  have h1 : ∫ y, f (scal α y) = (∏ j, α j ^ (2 * m))⁻¹ * ∫ x, f x := by
    have := integral_map_equiv e f (μ := volume)
    simp only [he] at this
    rw [← this, hmap, integral_smul_measure, hdet, ENNReal.toReal_ofReal (abs_nonneg _),
      abs_of_pos (inv_pos.2 hD)]
    simp [Complex.real_smul]
  rw [h1, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hD.ne'), one_mul]

end PositivityTheory.Rg.Sw.AbsSt.DF
