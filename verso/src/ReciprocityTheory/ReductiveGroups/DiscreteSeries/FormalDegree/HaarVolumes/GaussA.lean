import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens

noncomputable section

section
open Finset MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Rewrite using `[← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod_dep hf) (ae_of_all _ fun x => Finset.prod_nonneg fun i _ => h0 i _), integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (h0 i))]`.
-/
theorem gaussA_lint_pi_ofReal {ι : Type*} [Fintype ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : ∀ i, E i → ℝ)
    (hf : ∀ i, Integrable (f i) (μ i)) (h0 : ∀ i x, 0 ≤ f i x) :
    ∫⁻ x, ENNReal.ofReal (∏ i, f i (x i)) ∂(Measure.pi μ) = ∏ i, ENNReal.ofReal (∫ x, f i x ∂(μ i)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod_dep hf)
    (ae_of_all _ fun x => Finset.prod_nonneg fun i _ => h0 i _), integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (h0 i))]

/- English proof (translation)
Simplify using `using integrable_exp_neg_mul_sq (b := 1) one_pos`.
-/
theorem gaussA_real_int : Integrable (fun x : ℝ => Real.exp (-x ^ 2)) := by
  simpa using integrable_exp_neg_mul_sq (b := 1) one_pos

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [Function.comp_apply, Complex.measurableEquivRealProd_apply, ← Real.exp_add]`. Use `congr 1`. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gaussA_cfun_eq : (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) =
    (fun p : ℝ × ℝ => Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2)) ∘ Complex.measurableEquivRealProd := by
  funext z
  simp only [Function.comp_apply, Complex.measurableEquivRealProd_apply, ← Real.exp_add]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/- English proof (translation)
Rewrite using `[gaussA_cfun_eq, Complex.volume_preserving_equiv_real_prod.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding]`. Conclude with `Integrable.mul_prod gaussA_real_int gaussA_real_int`.
-/
theorem gaussA_cint : Integrable (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) := by
  rw [gaussA_cfun_eq, Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
    Complex.measurableEquivRealProd.measurableEmbedding]
  exact Integrable.mul_prod gaussA_real_int gaussA_real_int

/- English proof (translation)
Establish `h` using `Complex.volume_preserving_equiv_real_prod.integral_comp Complex.measurableEquivRealProd.measurableEmbedding (fun p : ℝ × ℝ => Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2))`. Establish `h2 : ∫ p : ℝ × ℝ, Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2) = Real.pi`. Rewrite using `[show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl, integral_prod_mul (fun x : ℝ => Real.exp (-x ^ 2)) (fun x : ℝ => Real.exp (-x ^ 2))]`. Establish `hg : ∫ x : ℝ, Real.exp (-x ^ 2) = Real.sqrt Real.pi`. Simplify using `using integral_gaussian 1`.

Rewrite using `[hg, Real.mul_self_sqrt Real.pi_pos.le]`. Rewrite using `[gaussA_cfun_eq]`. Simplify `h.trans h2` using `[Function.comp_def]`.
-/
theorem gaussA_cintegral : ∫ z : ℂ, Real.exp (-‖z‖ ^ 2) = Real.pi := by
  have h := Complex.volume_preserving_equiv_real_prod.integral_comp
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2))
  have h2 : ∫ p : ℝ × ℝ, Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2) = Real.pi := by
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
      integral_prod_mul (fun x : ℝ => Real.exp (-x ^ 2)) (fun x : ℝ => Real.exp (-x ^ 2))]
    have hg : ∫ x : ℝ, Real.exp (-x ^ 2) = Real.sqrt Real.pi := by
      simpa using integral_gaussian 1
    rw [hg, Real.mul_self_sqrt Real.pi_pos.le]
  rw [gaussA_cfun_eq]
  simpa [Function.comp_def] using h.trans h2

/- English proof (translation)
Establish `h` using `integral_rpow_mul_exp_neg_rpow (p := 2) (q := ((2 * a + 1 : ℕ) : ℝ)) two_pos (by have := (Nat.cast_nonneg (2*a+1) : (0:ℝ) ≤ _); linarith)`. Establish `hc : ∫ r in Ioi (0:ℝ), Real.exp (-r ^ 2) * |r| ^ (2 * a + 1) = ∫ x in Ioi (0:ℝ), x ^ (((2 * a + 1 : ℕ) : ℝ)) * Real.exp (-x ^ (2:ℝ))`. Use `setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)` and prove the remaining obligations. Simplify using `only [Real.rpow_natCast, abs_of_pos (mem_Ioi.mp hx)]`. Rewrite using `[show x ^ (2:ℝ) = x ^ (2:ℕ) by exact_mod_cast Real.rpow_natCast x 2, mul_comm]`.

Rewrite using `[hc, h]`. Establish `: ((((2 * a + 1 : ℕ) : ℝ)) + 1) / 2 = (a : ℝ) + 1` using `by push_cast; ring`. Rewrite using `[this, Real.Gamma_nat_eq_factorial]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gaussA_rad (a : ℕ) :
    ∫ r in Ioi (0:ℝ), Real.exp (-r ^ 2) * |r| ^ (2 * a + 1) = (a.factorial : ℝ) / 2 := by
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := ((2 * a + 1 : ℕ) : ℝ)) two_pos (by have := (Nat.cast_nonneg (2*a+1) : (0:ℝ) ≤ _); linarith)
  have hc : ∫ r in Ioi (0:ℝ), Real.exp (-r ^ 2) * |r| ^ (2 * a + 1) =
      ∫ x in Ioi (0:ℝ), x ^ (((2 * a + 1 : ℕ) : ℝ)) * Real.exp (-x ^ (2:ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Real.rpow_natCast, abs_of_pos (mem_Ioi.mp hx)]
    rw [show x ^ (2:ℝ) = x ^ (2:ℕ) by exact_mod_cast Real.rpow_natCast x 2, mul_comm]
  rw [hc, h]
  have : ((((2 * a + 1 : ℕ) : ℝ)) + 1) / 2 = (a : ℝ) + 1 := by push_cast; ring
  rw [this, Real.Gamma_nat_eq_factorial]
  ring

/- English proof (translation)
Establish `h` using `integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := ((2 * a + 1 : ℕ) : ℝ)) (by have := (Nat.cast_nonneg (2*a+1) : (0:ℝ) ≤ _); linarith)`. Use `h.congr_fun (fun x hx => ?_) measurableSet_Ioi` and prove the remaining obligations. Simplify using `only [Real.rpow_natCast, abs_of_pos (mem_Ioi.mp hx)]`. Put the polynomial expressions in normal form.
-/
theorem gaussA_rad_int (a : ℕ) :
    IntegrableOn (fun r : ℝ => Real.exp (-r ^ 2) * |r| ^ (2 * a + 1)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := ((2 * a + 1 : ℕ) : ℝ)) (by have := (Nat.cast_nonneg (2*a+1) : (0:ℝ) ≤ _); linarith)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, abs_of_pos (mem_Ioi.mp hx)]
  ring_nf

end ReciprocityTheory.ChartRestriction.DS

end

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

/- English proof (translation)
Simplify using `only [hs, trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `norm_cast`.
-/
theorem gaussB_hs_eq_re_trace (M : Matrix (Fin N) (Fin N) ℂ) : hs M = (trace (Mᴴ * M)).re := by
  simp only [hs, trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

/- English proof (translation)
Establish `hk : inUJ (fun _ : Fin N => true) (toM k)` using `k.2`. Establish `hJ : Jm (fun _ : Fin N => true) = 1`. Unfold `Jm`. Simplify using the standard rewrite rules. Unfold `inUJ at hk`.

Rewrite `hk` using `[hJ, Matrix.mul_one]`. Rewrite using `[gaussB_hs_eq_re_trace, gaussB_hs_eq_re_trace, conjTranspose_mul, show Mᴴ * (toM k)ᴴ * (toM k * M) = Mᴴ * ((toM k)ᴴ * toM k) * M by simp only [Matrix.mul_assoc], hk, Matrix.mul_one]`.
-/
theorem gaussB_hs_unitary_mul (k : UNgrp N) (M : Matrix (Fin N) (Fin N) ℂ) : hs (toM k * M) = hs M := by
  have hk : inUJ (fun _ : Fin N => true) (toM k) := k.2
  have hJ : Jm (fun _ : Fin N => true) = 1 := by
    unfold Jm; simp
  unfold inUJ at hk
  rw [hJ, Matrix.mul_one] at hk
  rw [gaussB_hs_eq_re_trace, gaussB_hs_eq_re_trace, conjTranspose_mul,
    show Mᴴ * (toM k)ᴴ * (toM k * M) = Mᴴ * ((toM k)ᴴ * toM k) * M by simp only [Matrix.mul_assoc],
    hk, Matrix.mul_one]

/- English proof (translation)
Rewrite using `[Fintype.card_subtype, Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]`. Establish `h1 : ∀ i : Fin N, (∑ j : Fin N, if i < j then 1 else 0) = N - 1 - i`. Introduce `i`. Rewrite using `[← Finset.card_filter, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]`. Repeatedly rewrite using `[h1]`.

Establish `h2 : (∑ i : Fin N, (N - 1 - (i : ℕ))) = ∑ i : Fin N, (i : ℕ)`. Use `Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)` and prove the remaining obligations. Simplify using `only [Fin.revPerm_apply, Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h2, Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]`.
-/
theorem gaussB_card_lt : Fintype.card {ab : Fin N × Fin N // ab.1 < ab.2} = N * (N - 1) / 2 := by
  rw [Fintype.card_subtype, Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
  have h1 : ∀ i : Fin N, (∑ j : Fin N, if i < j then 1 else 0) = N - 1 - i := by
    intro i
    rw [← Finset.card_filter, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  simp_rw [h1]
  have h2 : (∑ i : Fin N, (N - 1 - (i : ℕ))) = ∑ i : Fin N, (i : ℕ) := by
    refine Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)
    simp only [Fin.revPerm_apply, Fin.val_rev]
    omega
  rw [h2, Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

/- English proof (translation)
Rewrite using `[Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Use `congr 1`. Rewrite using `[← Fin.prod_univ_eq_prod_range (fun i => (i.factorial : ℝ)) N]`. Use `Fintype.prod_equiv Fin.revPerm _ _ (fun i => ?_)` and prove the remaining obligations. Simplify using `only [Fin.revPerm_apply, Fin.val_rev]`.

Conclude with `congrArg (fun m : ℕ => ((m.factorial : ℕ) : ℝ)) (by omega)`.
-/
theorem gaussB_prod_fact :
    (∏ j : Fin N, (((N - 1 - (j : ℕ)).factorial : ℝ) / 2)) = (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N := by
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun i => (i.factorial : ℝ)) N]
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun i => ?_)
  simp only [Fin.revPerm_apply, Fin.val_rev]
  exact congrArg (fun m : ℕ => ((m.factorial : ℕ) : ℝ)) (by omega)

end ReciprocityTheory.ChartRestriction.DS
