import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussS

noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G.GI

open PositivityTheory.Rg.Sw

/- English proof (translation)
Establish `h` using `integrable_rpow_mul_exp_neg_mul_sq hb (s := (k : ℝ)) (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)`. Rewrite `h` using `[Real.rpow_natCast]`. Use `h.norm.congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `[Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]`.
-/
lemma abs_pow_exp (b : ℝ) (hb : 0 < b) (k : ℕ) :
    Integrable fun x : ℝ => |x| ^ k * Real.exp (-b * x ^ 2) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq hb (s := (k : ℝ))
    (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
  simp_rw [Real.rpow_natCast] at h
  refine h.norm.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/- English proof (translation)
Break down `le_total a b with h | h` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Use `pow_nonneg ha k` as an intermediate fact. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation. Use `pow_nonneg hb k` as an intermediate fact. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma add_pow_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) : (a + b) ^ k ≤ 2 ^ k * (a ^ k + b ^ k) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ k ≤ (2 * b) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * b ^ k := mul_pow 2 b k
      _ ≤ 2 ^ k * (a ^ k + b ^ k) := by
          have := pow_nonneg ha k
          gcongr; linarith
  · calc (a + b) ^ k ≤ (2 * a) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * a ^ k := mul_pow 2 a k
      _ ≤ 2 ^ k * (a ^ k + b ^ k) := by
          have := pow_nonneg hb k
          gcongr; linarith

/- English proof (translation)
Establish `hP : Integrable (fun p : ℝ × ℝ => (2 : ℝ) ^ k * ((|p.1| ^ k * Real.exp (-c * p.1 ^ 2)) * Real.exp (-c * p.2 ^ 2) + Real.exp (-c * p.1 ^ 2) * (|p.2| ^ k * Real.exp (-c * p.2 ^ 2))))`. Use `Integrable.const_mul (Integrable.add ?_ ?_) _` and prove the remaining obligations. Conclude with `(abs_pow_exp c hc k).mul_prod (integrable_exp_neg_mul_sq hc)`. Conclude with `(integrable_exp_neg_mul_sq hc).mul_prod (abs_pow_exp c hc k)`. Establish `hC : Integrable (fun z : ℂ => (2 : ℝ) ^ k * ((|z.re| ^ k * Real.exp (-c * z.re ^ 2)) * Real.exp (-c * z.im ^ 2) + Real.exp (-c * z.re ^ 2) * (|z.im| ^ k * Real.exp (-c * z.im ^ 2))))`.

Use `(Complex.volume_preserving_equiv_real_prod.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding).mpr hP` as an intermediate fact. Simplify `this` using `[Function.comp_def, Complex.measurableEquivRealProd]`. Use `hC.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Establish `hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2`. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `he : Real.exp (-c * ‖z‖ ^ 2) = Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2)`. Rewrite using `[hz, ← Real.exp_add]`. Put the polynomial expressions in normal form. Establish `h1 : ‖z‖ ^ k ≤ 2 ^ k * (|z.re| ^ k + |z.im| ^ k)` using `(pow_le_pow_left₀ (norm_nonneg z) (Complex.norm_le_abs_re_add_abs_im z) k).trans (add_pow_le _ _ (abs_nonneg _) (abs_nonneg _) k)`.

Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (by positivity), he]`. Establish `e1` using `Real.exp_pos (-c * z.re ^ 2)`. Establish `e2` using `Real.exp_pos (-c * z.im ^ 2)`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma cplx (c : ℝ) (hc : 0 < c) (k : ℕ) :
    Integrable fun z : ℂ => ‖z‖ ^ k * Real.exp (-c * ‖z‖ ^ 2) := by
  have hP : Integrable (fun p : ℝ × ℝ => (2 : ℝ) ^ k * ((|p.1| ^ k * Real.exp (-c * p.1 ^ 2)) *
      Real.exp (-c * p.2 ^ 2) + Real.exp (-c * p.1 ^ 2) * (|p.2| ^ k * Real.exp (-c * p.2 ^ 2)))) := by
    refine Integrable.const_mul (Integrable.add ?_ ?_) _
    · exact (abs_pow_exp c hc k).mul_prod (integrable_exp_neg_mul_sq hc)
    · exact (integrable_exp_neg_mul_sq hc).mul_prod (abs_pow_exp c hc k)
  have hC : Integrable (fun z : ℂ => (2 : ℝ) ^ k * ((|z.re| ^ k * Real.exp (-c * z.re ^ 2)) *
      Real.exp (-c * z.im ^ 2) + Real.exp (-c * z.re ^ 2) * (|z.im| ^ k * Real.exp (-c * z.im ^ 2)))) := by
    have := (Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
      Complex.measurableEquivRealProd.measurableEmbedding).mpr hP
    simpa [Function.comp_def, Complex.measurableEquivRealProd] using this
  refine hC.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have he : Real.exp (-c * ‖z‖ ^ 2) = Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2) := by
    rw [hz, ← Real.exp_add]; ring_nf
  have h1 : ‖z‖ ^ k ≤ 2 ^ k * (|z.re| ^ k + |z.im| ^ k) :=
    (pow_le_pow_left₀ (norm_nonneg z) (Complex.norm_le_abs_re_add_abs_im z) k).trans
      (add_pow_le _ _ (abs_nonneg _) (abs_nonneg _) k)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), he]
  have e1 := Real.exp_pos (-c * z.re ^ 2)
  have e2 := Real.exp_pos (-c * z.im ^ 2)
  calc ‖z‖ ^ k * (Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2))
      ≤ 2 ^ k * (|z.re| ^ k + |z.im| ^ k) * (Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2)) := by
        gcongr
    _ = _ := by ring

/- English proof (translation)
Use `Integrable.fintype_prod (f := fun a (r : Fin n → ℂ) => ∏ i, (‖r i‖ ^ D a i * Real.exp (-c * ‖r i‖ ^ 2))) (μ := fun _ => volume) (fun a => ?_)` and prove the remaining obligations. Conclude with `Integrable.fintype_prod (f := fun i (z : ℂ) => ‖z‖ ^ D a i * Real.exp (-c * ‖z‖ ^ 2)) (μ := fun _ => volume) (fun i => cplx c hc _)`.
-/
lemma prodG (m n : ℕ) (c : ℝ) (hc : 0 < c) (D : Fin m → Fin n → ℕ) :
    Integrable fun x : Fin m → Fin n → ℂ => ∏ a, ∏ i, (‖x a i‖ ^ D a i * Real.exp (-c * ‖x a i‖ ^ 2)) := by
  refine Integrable.fintype_prod (f := fun a (r : Fin n → ℂ) => ∏ i, (‖r i‖ ^ D a i * Real.exp (-c * ‖r i‖ ^ 2)))
    (μ := fun _ => volume) (fun a => ?_)
  exact Integrable.fintype_prod (f := fun i (z : ℂ) => ‖z‖ ^ D a i * Real.exp (-c * ‖z‖ ^ 2))
    (μ := fun _ => volume) (fun i => cplx c hc _)

abbrev fx {m n : ℕ} (x : Fin m → Fin n → ℂ) : Fin m × Fin n × Bool → ℂ :=
  fun k => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1

/- English proof (translation)
Establish `: Continuous fun x : Fin m → Fin n → ℂ => fx x`. Use `continuous_pi fun k => ?_` and prove the remaining obligations. Distinguish the cases in `h : k.2.2`. Simplify using `only [fx, h, if_true]`. Use `fun_prop`.

Simplify using `only [fx, h, if_false, Bool.false_eq_true]`. Use `fun_prop`. Conclude with `(MvPolynomial.continuous_eval P).comp this`.
-/
lemma continuous_evX {m n : ℕ} (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x := by
  have : Continuous fun x : Fin m → Fin n → ℂ => fx x := by
    refine continuous_pi fun k => ?_
    by_cases h : k.2.2
    · simp only [fx, h, if_true]; fun_prop
    · simp only [fx, h, if_false, Bool.false_eq_true]; fun_prop
  exact (MvPolynomial.continuous_eval P).comp this

/- English proof (translation)
Unfold `gs`. Use `fun_prop`.
-/
lemma continuous_gs {m n : ℕ} (c : ℝ) : Continuous fun x : Fin m → Fin n → ℂ => gs c x := by
  unfold gs; fun_prop

/- English proof (translation)
Unfold `gs`. Rewrite using `[← Complex.ofReal_neg, Complex.norm_exp_ofReal]`. Establish `: -(c * ∑ a, ∑ i, ‖x a i‖ ^ 2) = ∑ a, ∑ i, (-c * ‖x a i‖ ^ 2)`. Simplify using `[Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]`. Rewrite using `[this, Real.exp_sum]`.

Conclude with `Finset.prod_congr rfl fun a _ => Real.exp_sum _ _`.
-/
lemma norm_gs {m n : ℕ} (c : ℝ) (x : Fin m → Fin n → ℂ) :
    ‖gs c x‖ = ∏ a, ∏ i, Real.exp (-c * ‖x a i‖ ^ 2) := by
  unfold gs
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
  have : -(c * ∑ a, ∑ i, ‖x a i‖ ^ 2) = ∑ a, ∑ i, (-c * ‖x a i‖ ^ 2) := by
    simp [Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
  rw [this, Real.exp_sum]
  exact Finset.prod_congr rfl fun a _ => Real.exp_sum _ _

/- English proof (translation)
Unfold `evX`. Rewrite using `[MvPolynomial.eval_monomial, one_mul, Finsupp.prod, norm_prod]`. Repeatedly rewrite using `[norm_pow]`. Rewrite using `[Finset.prod_subset (Finset.subset_univ _) (fun k _ hk => by`. Simplify using `[Finsupp.notMem_support_iff.mp hk])]`.

Rewrite using `[Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_bool]`.

Simplify using `[pow_add, mul_comm]`.
-/
lemma norm_mono {m n : ℕ} (d : (Fin m × Fin n × Bool) →₀ ℕ) (x : Fin m → Fin n → ℂ) :
    ‖evX (monomial d 1) x‖ = ∏ a, ∏ i, ‖x a i‖ ^ (d (a, i, false) + d (a, i, true)) := by
  unfold evX
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod, norm_prod]
  simp_rw [norm_pow]
  rw [Finset.prod_subset (Finset.subset_univ _) (fun k _ hk => by
    simp [Finsupp.notMem_support_iff.mp hk])]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_bool]
  simp [pow_add, mul_comm]

/- English proof (translation)
Introduce `m n c hc P`. Establish `key : ∀ d : (Fin m × Fin n × Bool) →₀ ℕ, Integrable fun x : Fin m → Fin n → ℂ => evX (monomial d 1) x * gs c x`. Introduce `d`. Use `(prodG m n c hc (fun a i => d (a, i, false) + d (a, i, true))).mono' ((continuous_evX _).mul (continuous_gs c)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mono, norm_gs, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`. Establish `hP : (fun x => evX P x * gs c x) = fun x => ∑ d ∈ P.support, coeff d P * (evX (monomial d 1) x * gs c x)`. Use function extensionality and compare the values at `x`. Simplify using `only [evX]`.

Rewrite using `[MvPolynomial.eval_eq, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.eval_monomial, one_mul, Finsupp.prod, mul_assoc]`. Rewrite using `[hP]`. Conclude with `integrable_finsetSum _ fun d _ => (key d).const_mul _`.
-/
theorem integP : IntegP := by
  intro m n c hc P
  have key : ∀ d : (Fin m × Fin n × Bool) →₀ ℕ,
      Integrable fun x : Fin m → Fin n → ℂ => evX (monomial d 1) x * gs c x := by
    intro d
    refine (prodG m n c hc (fun a i => d (a, i, false) + d (a, i, true))).mono'
      ((continuous_evX _).mul (continuous_gs c)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => le_of_eq ?_)
    rw [norm_mul, norm_mono, norm_gs, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← Finset.prod_mul_distrib]
  have hP : (fun x => evX P x * gs c x) =
      fun x => ∑ d ∈ P.support, coeff d P * (evX (monomial d 1) x * gs c x) := by
    funext x
    simp only [evX]
    rw [MvPolynomial.eval_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod, mul_assoc]
  rw [hP]
  exact integrable_finsetSum _ fun d _ => (key d).const_mul _

end PositivityTheory.Rg.Sw.WR.G.GI
