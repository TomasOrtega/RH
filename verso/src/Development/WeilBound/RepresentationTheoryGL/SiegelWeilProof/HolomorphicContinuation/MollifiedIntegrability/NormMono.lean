import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussS

noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G.GI

open PositivityTheory.Rg.Sw

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses repeatedly using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
lemma abs_pow_exp (b : ℝ) (hb : 0 < b) (k : ℕ) :
    Integrable fun x : ℝ => |x| ^ k * Real.exp (-b * x ^ 2) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq hb (s := (k : ℝ))
    (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
  simp_rw [Real.rpow_natCast] at h
  refine h.norm.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Chain the equalities or inequalities of the calculation.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
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
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Put the polynomial expressions in normal form. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
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
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
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
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
lemma continuous_evX {m n : ℕ} (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x := by
  have : Continuous fun x : Fin m → Fin n → ℂ => fx x := by
    refine continuous_pi fun k => ?_
    by_cases h : k.2.2
    · simp only [fx, h, if_true]; fun_prop
    · simp only [fx, h, if_false, Bool.false_eq_true]; fun_prop
  exact (MvPolynomial.continuous_eval P).comp this

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
lemma continuous_gs {m n : ℕ} (c : ℝ) : Continuous fun x : Fin m → Fin n → ℂ => gs c x := by
  unfold gs; fun_prop

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
