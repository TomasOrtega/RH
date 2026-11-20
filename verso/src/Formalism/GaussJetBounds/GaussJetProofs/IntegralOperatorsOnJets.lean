import Formalism.GaussJetBounds.GenLogInverse
import Formalism.GaussJetBounds.StatementQ
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffQuadSer
import Formalism.GaussJetBounds.GaussJetProofs.OneRow
import Formalism.GaussJetBounds.GaussJetProofs.ThmAOp

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

/- English proof (translation)
Introduce `K _ _ ι Th hTh P hP`. Unfold `jetPair`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun κ _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, norm_mul]`. Conclude with `mul_le_one₀ (hP κ) (norm_nonneg _) (hTh κ)`.
-/
theorem integral_operators_on_jets : IntOp.{u} := by
  intro K _ _ ι Th hTh P hP
  unfold jetPair
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun κ _ => ?_
  rw [mul_assoc, norm_mul]
  exact mul_le_one₀ (hP κ) (norm_nonneg _) (hTh κ)

/- English proof (translation)
Unfold `linForm`. Use `Subring.sum_mem _ fun x _ => ?_` and prove the remaining obligations. Introduce `κ`. Rewrite using `[MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, norm_mul]`. Use `mul_le_one₀ (hL x) (norm_nonneg _) ?_` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma linForm_mem_opInt {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type} [Fintype ι]
    (L : ι → K) (hL : ∀ x, ‖L x‖ ≤ 1) : linForm L ∈ opInt K ι := by
  classical
  unfold linForm
  refine Subring.sum_mem _ fun x _ => ?_
  intro κ
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, norm_mul]
  refine mul_le_one₀ (hL x) (norm_nonneg _) ?_
  split_ifs <;> simp

/- English proof (translation)
Unfold `polar`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_` and prove the remaining obligations. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun y _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Use `mul_le_one₀ (hc x y) (norm_nonneg _) ?_` and prove the remaining obligations.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hL x) (norm_nonneg _) (hL' y)`. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hL y) (norm_nonneg _) (hL' x)`.
-/
lemma norm_polar_le {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type} [Fintype ι]
    (c : ι → ι → K) (hc : ∀ x y, ‖c x y‖ ≤ 1) (L L' : ι → K) (hL : ∀ x, ‖L x‖ ≤ 1)
    (hL' : ∀ x, ‖L' x‖ ≤ 1) : ‖polar c L L'‖ ≤ 1 := by
  unfold polar
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun y _ => ?_
  rw [norm_mul]
  refine mul_le_one₀ (hc x y) (norm_nonneg _) ?_
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact mul_le_one₀ (hL x) (norm_nonneg _) (hL' y)
  · rw [norm_mul]
    exact mul_le_one₀ (hL y) (norm_nonneg _) (hL' x)

/- English proof (translation)
Introduce `K _ _ _ pi hpi0 hpi1 ι _ c S sg n L hc hS hsg hL M hM`. Establish `hB1 : (1 : ℝ) ≤ pi ^ (-(1 / 2 : ℝ))` using `Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpi0 hpi1.le (by norm_num)`. Establish `hB0 : (0 : ℝ) ≤ pi ^ (-(1 / 2 : ℝ))` using `zero_le_one.trans hB1`. Rewrite using `[matching_existence K ι c S sg n L]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hpi0.le _) fun σ hσ => ?_` and prove the remaining obligations.

Establish `hσ2 : σ * σ = 1` using `(Finset.mem_filter.mp hσ).2`. Distinguish the cases in `h : ∀ i, i < σ i → polar c (L i) (L (σ i)) ≠ 0`. Establish `hcard` using `hM σ hσ2 h`. Rewrite using `[norm_mul, norm_prod]`. Establish `h1 : (∏ i ∈ Finset.univ.filter (fun i => i < σ i), ‖-S * polar c (L i) (L (σ i))‖) ≤ (pi ^ (-(1 / 2 : ℝ))) ^ (Finset.univ.filter (fun i => i < σ i)).card`.

Rewrite using `[← Finset.prod_const]`. Use `Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_neg]`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : (pi ^ (-(1 / 2 : ℝ))) ^ (Finset.univ.filter (fun i => i < σ i)).card ≤ (pi ^ (-(1 / 2 : ℝ))) ^ M` using `pow_le_pow_right₀ hB1 hcard`.

Establish `h3 : (pi ^ (-(1 / 2 : ℝ))) ^ M = pi ^ (-(1 / 2 : ℝ) * M)`. Rewrite using `[Real.rpow_mul_natCast hpi0.le]`. Establish `h4 : ‖jetPair (∏ i ∈ Finset.univ.filter (fun i => σ i = i), linForm (L i)) sg‖ ≤ 1`. Use `integral_operators_on_jets K ι sg hsg _ ?_` and prove the remaining obligations. Establish `: (∏ i ∈ Finset.univ.filter (fun i => σ i = i), linForm (L i)) ∈ opInt K ι` using `Subring.prod_mem _ fun i _ => linForm_mem_opInt (L i) (hL i)`.

Conclude with `this`. Combine the equalities or inequalities in the displayed calculation. Use `push Not at h`. Take `⟨i, hi, h0⟩` from `h`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩) (by rw [h0, mul_zero]), zero_mul, norm_zero]`.

Conclude with `Real.rpow_nonneg hpi0.le _`.
-/
theorem matching_bound : MatchBound.{u} := by
  intro K _ _ _ pi hpi0 hpi1 ι _ c S sg n L hc hS hsg hL M hM
  have hB1 : (1 : ℝ) ≤ pi ^ (-(1 / 2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpi0 hpi1.le (by norm_num)
  have hB0 : (0 : ℝ) ≤ pi ^ (-(1 / 2 : ℝ)) := zero_le_one.trans hB1
  rw [matching_existence K ι c S sg n L]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hpi0.le _)
    fun σ hσ => ?_
  have hσ2 : σ * σ = 1 := (Finset.mem_filter.mp hσ).2
  by_cases h : ∀ i, i < σ i → polar c (L i) (L (σ i)) ≠ 0
  · have hcard := hM σ hσ2 h
    rw [norm_mul, norm_prod]
    have h1 : (∏ i ∈ Finset.univ.filter (fun i => i < σ i), ‖-S * polar c (L i) (L (σ i))‖) ≤
        (pi ^ (-(1 / 2 : ℝ))) ^ (Finset.univ.filter (fun i => i < σ i)).card := by
      rw [← Finset.prod_const]
      refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
      rw [norm_mul, norm_neg]
      calc ‖S‖ * ‖polar c (L i) (L (σ i))‖ ≤ pi ^ (-(1 / 2 : ℝ)) * 1 :=
            mul_le_mul hS (norm_polar_le c hc _ _ (hL i) (hL (σ i))) (norm_nonneg _) hB0
        _ = pi ^ (-(1 / 2 : ℝ)) := mul_one _
    have h2 : (pi ^ (-(1 / 2 : ℝ))) ^ (Finset.univ.filter (fun i => i < σ i)).card ≤
        (pi ^ (-(1 / 2 : ℝ))) ^ M := pow_le_pow_right₀ hB1 hcard
    have h3 : (pi ^ (-(1 / 2 : ℝ))) ^ M = pi ^ (-(1 / 2 : ℝ) * M) := by
      rw [Real.rpow_mul_natCast hpi0.le]
    have h4 : ‖jetPair (∏ i ∈ Finset.univ.filter (fun i => σ i = i), linForm (L i)) sg‖ ≤ 1 := by
      refine integral_operators_on_jets K ι sg hsg _ ?_
      have : (∏ i ∈ Finset.univ.filter (fun i => σ i = i), linForm (L i)) ∈ opInt K ι :=
        Subring.prod_mem _ fun i _ => linForm_mem_opInt (L i) (hL i)
      exact this
    calc _ ≤ pi ^ (-(1 / 2 : ℝ) * M) * 1 :=
          mul_le_mul ((h1.trans h2).trans h3.le) h4 (norm_nonneg _) (Real.rpow_nonneg hpi0.le _)
      _ = _ := mul_one _
  · push Not at h
    obtain ⟨i, hi, h0⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩) (by rw [h0, mul_zero]),
      zero_mul, norm_zero]
    exact Real.rpow_nonneg hpi0.le _

/- English proof (translation)
Introduce `H _ _ TT c wt wt' f k b b' hf hk hb hb' hc0 hc1 hc2 hwt hwt'`. Take `⟨h1, h2⟩` from `base_size_bounds H TT c wt wt' f k b b' hf hk hb hb' hc1 hc2 hwt hwt'`. Establish `h3 : 0 ≤ ∑ t, c t` using `Finset.sum_nonneg fun t _ => hc0 t`. Establish `h4 : |(1 / 2) * ∑ t, c t| ≤ (TT.card : ℝ) * b + f * k * b'`. Rewrite using `[abs_of_nonneg (by positivity)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `(abs_add_le _ _).trans ?_` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exponent_size_bounds : SizesE := by
  intro H _ _ TT c wt wt' f k b b' hf hk hb hb' hc0 hc1 hc2 hwt hwt'
  obtain ⟨h1, h2⟩ := base_size_bounds H TT c wt wt' f k b b' hf hk hb hb' hc1 hc2 hwt hwt'
  have h3 : 0 ≤ ∑ t, c t := Finset.sum_nonneg fun t _ => hc0 t
  have h4 : |(1 / 2) * ∑ t, c t| ≤ (TT.card : ℝ) * b + f * k * b' := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  refine (abs_add_le _ _).trans ?_
  linarith

end Formalism.DworkPowerSeriesWeights
