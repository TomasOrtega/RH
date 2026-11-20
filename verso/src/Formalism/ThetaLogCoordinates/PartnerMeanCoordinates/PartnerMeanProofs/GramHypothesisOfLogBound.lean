import Formalism.PolynomialDimension.ChainOrderLetters
import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.PartnerMeanProofs.TheoremMCKap7
import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.PartnerMeanProofs.NatLogLeOfLe
import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.PartnerMeanProofs.GammaZeroIntegral
import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.PartnerMeanProofs.TheoremMXBOfPoint

namespace Formalism.InvariantFactorPaths.MC

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW Formalism.InvariantFactorPaths.L4 MvPolynomial Finset

/- English proof (translation)
The claim follows from `meanGamX_of (by first | exact Formalism.GM.gamma_degree_bound | exact Formalism.GM.Top.gamDeg) (by first | exact Formalism.GM.gamma_leading_term | exact Formalism.GM.Top.gamLead) (by first | exact Formalism.InvariantFactorPaths.MC.gamma_integral_holds | exact Formalism.InvariantF …`.
-/
theorem meanGamX : MeanGamX :=
  meanGamX_of (by first | exact Formalism.GM.gamma_degree_bound | exact Formalism.GM.Top.gamDeg)
    (by first | exact Formalism.GM.gamma_leading_term | exact Formalism.GM.Top.gamLead)
    (by first | exact Formalism.InvariantFactorPaths.MC.gamma_integral_holds | exact Formalism.InvariantFactorPaths.MC.Top.gamIntC)
    (by first | exact Formalism.GM.Top.windowFullAP | exact Top.windowFullAP)

/- English proof (translation)
The claim follows from `theoremMXB_of_point meanGamX (by first | exact DimensionMonotonicity.highest_weight_dim_monotone | exact Formalism.GM.DimensionMonotonicity.highest_weight_dim_monotone | exact Formalism.GM.M.DimensionMonotonicity.highest_weight_dim_monotone | exact Formalism.GM.TM.DimensionMonoto …`.
-/
theorem theoremMXB : TheoremMXB :=
  theoremMXB_of_point meanGamX
    (by first | exact DimensionMonotonicity.highest_weight_dim_monotone | exact Formalism.GM.DimensionMonotonicity.highest_weight_dim_monotone | exact Formalism.GM.M.DimensionMonotonicity.highest_weight_dim_monotone | exact Formalism.GM.TM.DimensionMonotonicity.highest_weight_dim_monotone)
    (by first | exact monomial_count | exact Formalism.GM.monomial_count | exact Formalism.GM.M.monomial_count | exact Formalism.GM.TM.monomial_count)
    (by first | exact Formalism.GM.Top.smithZp | exact Formalism.GM.smith_form_p_adic_integers | exact Formalism.GM.TM.smith_form_p_adic_integers | exact Formalism.GM.M.smith_form_p_adic_integers)
    (by first | exact Formalism.GM.TM.existsAdaptedBasis | exact Formalism.GM.existsAdaptedBasis | exact Formalism.GM.Top.adaptedBasis)
    (pointMX_of_partner
      (by first | exact bad_criterion_holds | exact Formalism.InvariantFactorPaths.MC.bad_criterion_holds | exact Formalism.GM.bad_criterion_holds | exact Formalism.InvariantFactorPaths.MC.Top.badCrit | exact Formalism.GM.Top.badCrit)
      (partnerMX_of_parts tieOpsX_main (by first | exact partner_condition_holds | exact Formalism.InvariantFactorPaths.MC.Top.yPartnerC | exact Formalism.InvariantFactorPaths.MC.Top.yPartner)))

/- English proof (translation)
Unfold `lgSeg`. Establish `hp : 1 < (p : ℝ)` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Establish `hr' : (1 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hy : (1 : ℝ) ≤ 8 * a + r` using `by linarith`. Establish `hl : 0 ≤ Real.logb p (8 * a + r)` using `Real.logb_nonneg hp hy`.

Break down `Nat.eq_zero_or_pos x with hx0 | hx0` into its components or cases. Substitute `hx0` using the available equality. Simplify using `only [Nat.log_zero_right, Nat.cast_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : ((p ^ Nat.log p x : ℕ) : ℝ) ≤ (x : ℝ)`.

Conclude with `Nat.pow_log_le_self p hx0.ne'` after adjusting the coercions. Move the coercions through the operations in `at h1`. Establish `hpy : (0 : ℝ) < p * (8 * a + r)` using `mul_pos (by linarith) (by linarith)`. Establish `h2 : (Nat.log p x : ℝ) ≤ Real.logb p (p * (8 * a + r))`. Rewrite using `[Real.le_logb_iff_rpow_le hp hpy, Real.rpow_natCast]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `h2` using `[Real.logb_mul (by positivity) (by linarith), Real.logb_self_eq_one hp]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem natLog_le_lgSeg (p : ℕ) [Fact p.Prime] (a : ℝ) (r x : ℕ) (ha : 0 ≤ a) (hr : 1 ≤ r)
    (hx : (x : ℝ) ≤ p * (8 * a + r)) : (Nat.log p x : ℝ) ≤ lgSeg p a r := by
  unfold lgSeg
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hy : (1 : ℝ) ≤ 8 * a + r := by linarith
  have hl : 0 ≤ Real.logb p (8 * a + r) := Real.logb_nonneg hp hy
  rcases Nat.eq_zero_or_pos x with hx0 | hx0
  · subst hx0
    simp only [Nat.log_zero_right, Nat.cast_zero]
    linarith
  · have h1 : ((p ^ Nat.log p x : ℕ) : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self p hx0.ne'
    push_cast at h1
    have hpy : (0 : ℝ) < p * (8 * a + r) := mul_pos (by linarith) (by linarith)
    have h2 : (Nat.log p x : ℝ) ≤ Real.logb p (p * (8 * a + r)) := by
      rw [Real.le_logb_iff_rpow_le hp hpy, Real.rpow_natCast]
      linarith
    rw [Real.logb_mul (by positivity) (by linarith), Real.logb_self_eq_one hp] at h2
    linarith

/- English proof (translation)
Unfold `lgSeg`. Establish `hp : 1 < (p : ℝ)` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Establish `hr' : (1 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hl : 0 ≤ Real.logb p (8 * a + r)` using `Real.logb_nonneg hp (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_lgSeg (p : ℕ) [Fact p.Prime] (a : ℝ) (r : ℕ) (ha : 0 ≤ a) (hr : 1 ≤ r) : 1 ≤ lgSeg p a r := by
  unfold lgSeg
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hl : 0 ≤ Real.logb p (8 * a + r) := Real.logb_nonneg hp (by linarith)
  linarith

/- English proof (translation)
Unfold `lgSeg`. Establish `hp : 1 < (p : ℝ)` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Establish `hr' : (1 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hy : (1 : ℝ) ≤ 8 * a + r` using `by linarith`. Establish `hfl : 1 ≤ ⌊8 * a + (r : ℝ)⌋₊` using `Nat.le_floor (by rw [Nat.cast_one]; exact hy)`.

Establish `h3 : ((p ^ Nat.log p ⌊8 * a + (r : ℝ)⌋₊ : ℕ) : ℝ) ≤ (⌊8 * a + (r : ℝ)⌋₊ : ℝ)`. Conclude with `Nat.pow_log_le_self p (by omega)` after adjusting the coercions. Establish `h4` using `Nat.floor_le (by linarith : (0 : ℝ) ≤ 8 * a + r)`. Move the coercions through the operations in `at h3`. Establish `h2 : (Nat.log p ⌊8 * a + (r : ℝ)⌋₊ : ℝ) ≤ Real.logb p (8 * a + r)`.

Rewrite using `[Real.le_logb_iff_rpow_le hp (by linarith), Real.rpow_natCast]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem natLog_floor_lgSeg (p : ℕ) [Fact p.Prime] (a : ℝ) (r : ℕ) (ha : 0 ≤ a) (hr : 1 ≤ r) :
    (Nat.log p ⌊8 * a + r⌋₊ : ℝ) + 1 ≤ lgSeg p a r := by
  unfold lgSeg
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hy : (1 : ℝ) ≤ 8 * a + r := by linarith
  have hfl : 1 ≤ ⌊8 * a + (r : ℝ)⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; exact hy)
  have h3 : ((p ^ Nat.log p ⌊8 * a + (r : ℝ)⌋₊ : ℕ) : ℝ) ≤ (⌊8 * a + (r : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self p (by omega)
  have h4 := Nat.floor_le (by linarith : (0 : ℝ) ≤ 8 * a + r)
  push_cast at h3
  have h2 : (Nat.log p ⌊8 * a + (r : ℝ)⌋₊ : ℝ) ≤ Real.logb p (8 * a + r) := by
    rw [Real.le_logb_iff_rpow_le hp (by linarith), Real.rpow_natCast]
    linarith
  linarith

/- English proof (translation)
Establish `h : 2 * r.choose 2 ≤ r ^ 2`. Rewrite using `[Nat.choose_two_right]`. Establish `h1` using `Nat.div_mul_le_self (r * (r - 1)) 2`. Establish `h2 : r * (r - 1) ≤ r ^ 2`. Rewrite using `[sq]`.

Conclude with `Nat.mul_le_mul_left r (Nat.sub_le r 1)`. Combine the equalities or inequalities in the displayed calculation. Establish `h' : (2 : ℝ) * (r.choose 2 : ℝ) ≤ (r : ℝ) ^ 2` using `by exact_mod_cast h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem choose_two_le (r : ℕ) : ((r.choose 2 : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 / 2 := by
  have h : 2 * r.choose 2 ≤ r ^ 2 := by
    rw [Nat.choose_two_right]
    have h1 := Nat.div_mul_le_self (r * (r - 1)) 2
    have h2 : r * (r - 1) ≤ r ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul_left r (Nat.sub_le r 1)
    calc 2 * (r * (r - 1) / 2) = r * (r - 1) / 2 * 2 := mul_comm _ _
      _ ≤ r * (r - 1) := h1
      _ ≤ r ^ 2 := h2
  have h' : (2 : ℝ) * (r.choose 2 : ℝ) ≤ (r : ℝ) ^ 2 := by exact_mod_cast h
  linarith

/- English proof (translation)
Establish `hc` using `choose_two_le r`. Establish `hl1 : (0 : ℝ) ≤ (Nat.log p (LLw.total + r - 1) : ℝ)` using `Nat.cast_nonneg _`. Establish `hl2 : (0 : ℝ) ≤ (Nat.log p (4 * LLw.total + r - 1) : ℝ)` using `Nat.cast_nonneg _`. Establish `hlg : 0 ≤ lgv` using `hl1.trans h1`. Establish `hQ : 0 ≤ (r : ℝ) ^ 2 / 2 * lgv` using `by positivity`.

Establish `g1 : ((kapC p r LLw.total : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 / 2 * lgv`. Unfold `kapC`. Rewrite using `[Nat.cast_mul]`. Conclude with `mul_le_mul hc h1 hl1 (by positivity)`. Establish `g2 : ((r.choose 2 * Nat.log p (4 * LLw.total + r - 1) : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 / 2 * lgv`.

Rewrite using `[Nat.cast_mul]`. Conclude with `mul_le_mul hc h2 hl2 (by positivity)`. Establish `hK0 : (0 : ℝ) ≤ K` using `Nat.cast_nonneg _`. Break down `Nat.eq_zero_or_pos K with rfl | hK` into its components or cases. Use `graded_bound_saturation_holds p 0 r LLw J M ρ (kapC p r LLw.total) 0 κ4 hr hρ hv (hypPE_setLast LLw ρ) (fun e _ => restricted_saturation_zero p r _ J _ ρ hr hρ hv) ?_` and prove the remaining obligations.

Rewrite using `[Nat.mul_zero, Nat.add_zero, Nat.cast_mul]`. Move the coercions through the operations in `at hκ ⊢`. Use the polynomial consequences of the given equalities and inequalities. Use `graded_bound_pos_of_proj highest_vector_projection_holds p K r LLw J M ρ (kapC p r LLw.total) (2 * (r.choose 2 * Nat.log p (4 * LLw.total + r - 1))) κ4 hK hr hρ hv (hypPE_setLast LLw ρ) ?_ (le_trans ?_ hκ)` and prove the remaining obligations. Introduce `e _`.

Establish `ht'` using `setLast_total_le LLw (LLw.deg (Fin.last K) - e) (Nat.sub_le _ _)`. Conclude with `resSatL_mono _ J _ ρ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega)))) (restricted_saturation_holds p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ hr hρ hv)`. Establish `h3 : ((K : ℝ) + 3) * ((kapC p r LLw.total : ℕ) : ℝ) ≤ ((K : ℝ) + 3) * ((r : ℝ) ^ 2 / 2 * lgv)` using `mul_le_mul_of_nonneg_left g1 (by positivity)`. Rewrite using `[Nat.cast_add, Nat.cast_mul, Nat.cast_mul (2 : ℕ), Nat.cast_mul (2 : ℕ)]`. Move the coercions through the operations in `at g2 h3 ⊢`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gram_hypothesis_of_log_bound (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (lgv κ4 : ℝ) (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1)
    (hv : LLw.vec (Fin.last K) = true) (h1 : (Nat.log p (LLw.total + r - 1) : ℝ) ≤ lgv)
    (h2 : (Nat.log p (4 * LLw.total + r - 1) : ℝ) ≤ lgv)
    (hκ : ((K : ℝ) + 7) * ((r : ℝ) ^ 2 / 2 * lgv) ≤ κ4) : GramDeterminantGradedHypothesis p LLw J M ρ κ4 := by
  have hc := choose_two_le r
  have hl1 : (0 : ℝ) ≤ (Nat.log p (LLw.total + r - 1) : ℝ) := Nat.cast_nonneg _
  have hl2 : (0 : ℝ) ≤ (Nat.log p (4 * LLw.total + r - 1) : ℝ) := Nat.cast_nonneg _
  have hlg : 0 ≤ lgv := hl1.trans h1
  have hQ : 0 ≤ (r : ℝ) ^ 2 / 2 * lgv := by positivity
  have g1 : ((kapC p r LLw.total : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 / 2 * lgv := by
    unfold kapC
    rw [Nat.cast_mul]
    exact mul_le_mul hc h1 hl1 (by positivity)
  have g2 : ((r.choose 2 * Nat.log p (4 * LLw.total + r - 1) : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 / 2 * lgv := by
    rw [Nat.cast_mul]
    exact mul_le_mul hc h2 hl2 (by positivity)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · refine graded_bound_saturation_holds p 0 r LLw J M ρ (kapC p r LLw.total) 0 κ4 hr hρ hv (hypPE_setLast LLw ρ)
      (fun e _ => restricted_saturation_zero p r _ J _ ρ hr hρ hv) ?_
    rw [Nat.mul_zero, Nat.add_zero, Nat.cast_mul]
    push_cast at hκ ⊢
    nlinarith
  · refine graded_bound_pos_of_proj highest_vector_projection_holds p K r LLw J M ρ (kapC p r LLw.total)
      (2 * (r.choose 2 * Nat.log p (4 * LLw.total + r - 1))) κ4 hK hr hρ hv (hypPE_setLast LLw ρ) ?_ (le_trans ?_ hκ)
    · intro e _
      have ht' := setLast_total_le LLw (LLw.deg (Fin.last K) - e) (Nat.sub_le _ _)
      exact resSatL_mono _ J _ ρ
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))))
        (restricted_saturation_holds p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ hr hρ hv)
    · have h3 : ((K : ℝ) + 3) * ((kapC p r LLw.total : ℕ) : ℝ) ≤ ((K : ℝ) + 3) * ((r : ℝ) ^ 2 / 2 * lgv) :=
        mul_le_mul_of_nonneg_left g1 (by positivity)
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul (2 : ℕ), Nat.cast_mul (2 : ℕ)]
      push_cast at g2 h3 ⊢
      nlinarith

/- English proof (translation)
Unfold `Letters.total`. Conclude with `Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ x)`.
-/
theorem deg_le_total' {N : ℕ} (LL : Letters N) (x : Fin N) : LL.deg x ≤ LL.total := by
  unfold Letters.total
  exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ x)

/- English proof (translation)
Unfold `TheoremMV7Of`. Introduce `p _ s r _ LL T a E Yl n₀ dd ρ hp2 hr hρ hadm hch hcond ha hE hY hS hsize hH`. Use `haveI : NeZero (2 * s + 1) := ⟨by omega⟩`. Establish `hr1 : 1 ≤ r` using `by omega`. Establish `hrR : (2 : ℝ) ≤ r` using `by exact_mod_cast hr`.

Establish `hlg1 : 1 ≤ lgSeg p a r` using `one_le_lgSeg p a r (by linarith) hr1`. Establish `hfl` using `natLog_floor_lgSeg p a r (by linarith) hr1`. Establish `hpos : 0 ≤ (r : ℝ) ^ 2 * lgSeg p a r` using `mul_nonneg (sq_nonneg _) (by linarith)`. Establish `hsR : (0 : ℝ) ≤ s` using `Nat.cast_nonneg s`. Establish `hspos : 0 ≤ (s : ℝ) * ((r : ℝ) ^ 2 * lgSeg p a r)` using `mul_nonneg hsR hpos`.

Establish `hflo : ∀ m : ℕ, (m : ℝ) ≤ 8 * a + r → m ≤ ⌊8 * a + (r : ℝ)⌋₊` using `fun m hm => Nat.le_floor hm`. Take `⟨htot, hsz⟩` from `hsize`. Unfold `epsSeg`. Use `theoremMXB p (2 * s + 1) r LL T ⌊8 * a + (r : ℝ)⌋₊ E (kapSeg p a r s) (((s : ℝ) + 4) * ((r : ℝ) ^ 2 * lgSeg p a r)) (lgSeg p a r) ⌊(r : ℝ) ^ 2 * lgSeg p a r⌋₊ Yl n₀ dd ρ hp2 hr hρ hadm hE hY hS ?_ ?_ ?_ hfl ?_ ?_ ?_ hH` and prove the remaining obligations. Introduce `x`.

Apply `hflo` to reduce the goal to its premises. Establish `h1` using `deg_le_total' (LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)) x`. Establish `h2 : ((LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)).deg x : ℝ) ≤ ((LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)).total : ℝ)` using `by exact_mod_cast h1`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `i`.

Take `⟨h1, h2, h3⟩` from `hsz i`. Use `⟨?_, hflo _ h2, ?_⟩` and prove the remaining obligations. Apply `hflo` to reduce the goal to its premises. Move the coercions through the operations in `at h3 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `h`. Apply `hflo` to reduce the goal to its premises. Establish `hdA : degreeAtPosition (LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)) (T.pos i) = (LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)).deg ⟨T.pos i, h⟩`. Unfold `degreeAtPosition`. Rewrite using `[dif_pos h]`.

Rewrite `h1` using `[hdA]`. Move the coercions through the operations in `at h1 ⊢`. Establish `h4` using `(Nat.cast_nonneg (degreeAtPosition (LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)) (T.pos i + 1)) : (0 : ℝ) ≤ _)`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hflo r (by linarith)`.

Unfold `kapSeg`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `kapSeg`. Use `push_cast`.

Establish `h1 : ((⌊(r : ℝ) ^ 2 * lgSeg p a r⌋₊ : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 * lgSeg p a r` using `Nat.floor_le hpos`. Establish `h2` using `mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 2 * (s : ℝ) + 1 + 2)`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `kapSeg`. Establish `hr4 : (4 : ℝ) ≤ (r : ℝ) ^ 2` using `by nlinarith`.

Establish `h1` using `mul_le_mul_of_nonneg_right hr4 (by linarith : (0 : ℝ) ≤ lgSeg p a r)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem theoremMV7Of : TheoremMV7Of := by
  unfold TheoremMV7Of
  intro p _ s r _ LL T a E Yl n₀ dd ρ hp2 hr hρ hadm hch hcond ha hE hY hS hsize hH
  haveI : NeZero (2 * s + 1) := ⟨by omega⟩
  have hr1 : 1 ≤ r := by omega
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hlg1 : 1 ≤ lgSeg p a r := one_le_lgSeg p a r (by linarith) hr1
  have hfl := natLog_floor_lgSeg p a r (by linarith) hr1
  have hpos : 0 ≤ (r : ℝ) ^ 2 * lgSeg p a r := mul_nonneg (sq_nonneg _) (by linarith)
  have hsR : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hspos : 0 ≤ (s : ℝ) * ((r : ℝ) ^ 2 * lgSeg p a r) := mul_nonneg hsR hpos
  have hflo : ∀ m : ℕ, (m : ℝ) ≤ 8 * a + r → m ≤ ⌊8 * a + (r : ℝ)⌋₊ := fun m hm => Nat.le_floor hm
  obtain ⟨htot, hsz⟩ := hsize
  unfold epsSeg
  refine theoremMXB p (2 * s + 1) r LL T ⌊8 * a + (r : ℝ)⌋₊ E (kapSeg p a r s)
    (((s : ℝ) + 4) * ((r : ℝ) ^ 2 * lgSeg p a r)) (lgSeg p a r) ⌊(r : ℝ) ^ 2 * lgSeg p a r⌋₊
    Yl n₀ dd ρ hp2 hr hρ hadm hE hY hS ?_ ?_ ?_ hfl ?_ ?_ ?_ hH
  · intro x
    apply hflo
    have h1 := deg_le_total' (LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)) x
    have h2 : ((LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)).deg x : ℝ) ≤
        ((LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)).total : ℝ) := by exact_mod_cast h1
    linarith
  · intro i
    obtain ⟨h1, h2, h3⟩ := hsz i
    refine ⟨?_, hflo _ h2, ?_⟩
    · apply hflo
      push_cast at h3 ⊢
      linarith
    · intro h
      apply hflo
      have hdA : degreeAtPosition (LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)) (T.pos i) =
          (LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)).deg ⟨T.pos i, h⟩ := by
        unfold degreeAtPosition
        rw [dif_pos h]
      rw [hdA] at h1
      push_cast at h1 ⊢
      have h4 := (Nat.cast_nonneg (degreeAtPosition (LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)) (T.pos i + 1)) : (0 : ℝ) ≤ _)
      linarith
  · exact hflo r (by linarith)
  · unfold kapSeg
    push_cast
    linarith
  · unfold kapSeg
    push_cast
    have h1 : ((⌊(r : ℝ) ^ 2 * lgSeg p a r⌋₊ : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 * lgSeg p a r := Nat.floor_le hpos
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 2 * (s : ℝ) + 1 + 2)
    linarith
  · unfold kapSeg
    have hr4 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right hr4 (by linarith : (0 : ℝ) ≤ lgSeg p a r)
    nlinarith

/- English proof (translation)
Unfold `Letters.total`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`. Unfold `Letters.setTies`. Simplify using `only`.

Use `split_ifs with hh`. Conclude with `h _`. Conclude with `le_rfl`.
-/
theorem setTies_total_le {N : ℕ} (LL : Letters N) (T : TieData) (n n' : Fin T.t → ℕ) (h : ∀ i, n i ≤ n' i) :
    (LL.setTies T n).total ≤ (LL.setTies T n').total := by
  unfold Letters.total
  apply Finset.sum_le_sum
  intro i _
  unfold Letters.setTies
  dsimp only
  split_ifs with hh
  · exact h _
  · exact le_rfl

/- English proof (translation)
Introduce `p _ s r _ LL T a E Yl n₀ dd ρ hp hr hρ hadm hch hco ha hE hY hS hsz`. Use `theoremMV7Of p s r LL T a E Yl n₀ dd ρ hp hr hρ hadm hch hco ha hE hY hS hsz ?_` and prove the remaining obligations. Take `⟨htot, hsz⟩` from `hsz`. Establish `ha0 : 0 ≤ a` using `by linarith`. Establish `hlg1` using `one_le_lgSeg p a r ha0 (by omega)`.

Establish `hr' : (2 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hp3 : (3 : ℝ) ≤ p`. Establish `h2` using `(Fact.out : p.Prime).two_le`. Establish `: 3 ≤ p` using `by omega`. Conclude with `this` after adjusting the coercions.

Establish `hy : (0 : ℝ) ≤ 8 * a + r` using `by linarith`. Establish `hQ : 0 ≤ (r : ℝ) ^ 2 / 2 * lgSeg p a r` using `by positivity`. Introduce `n hn`. Establish `hle` using `grid_le T Yl n₀ dd n hn`. Establish `hk : kapC p r (LL.setTies T n).total ≤ ⌊(r : ℝ) ^ 2 * lgSeg p a r⌋₊`.

Apply `Nat.le_floor` to reduce the goal to its premises. Establish `ht : ((LL.setTies T n).total : ℝ) ≤ 8 * a + r` using `le_trans (by exact_mod_cast setTies_total_le LL T n _ hle) htot`. Establish `hx : (((LL.setTies T n).total + r - 1 : ℕ) : ℝ) ≤ p * (8 * a + r)`. Establish `h1 : (((LL.setTies T n).total + r - 1 : ℕ) : ℝ) ≤ ((LL.setTies T n).total : ℝ) + r`. Establish `: (LL.setTies T n).total + r - 1 ≤ (LL.setTies T n).total + r` using `Nat.sub_le _ _`.

Conclude with `this` after adjusting the coercions. Use the polynomial consequences of the given equalities and inequalities. Establish `hl` using `natLog_le_lgSeg p a r _ ha0 (by omega) hx`. Unfold `kapC`. Rewrite using `[Nat.cast_mul]`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨Formalism.InvariantFactorPaths.PW.Top.dischargeP p _ r _ ρ _ hk, Formalism.InvariantFactorPaths.PW.Top.dischargeW p _ r _ _ hk, fun i => ?_⟩` and prove the remaining obligations. Take `⟨hlt, _, _⟩` from `hadm.2.1 i`. Take `⟨-, -, h2S⟩` from `hsz i`. Establish `hSle : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i`.

Rewrite using `[takeD_total_eq (LL.setTies T n) T i hlt]`. Conclude with `S_mono LL T n _ hle i`. Establish `hSr : 2 * (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ) + 1 ≤ 8 * a + r`. Establish `: (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ) ≤ (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ)` using `by exact_mod_cast hSle`. Move the coercions through the operations in `at h2S`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hS0 : (0 : ℝ) ≤ (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ)` using `Nat.cast_nonneg _`. Use `gram_hypothesis_of_log_bound p (T.pos i) r _ T.J (T.thrUpTo i) ρ (lgSeg p a r) _ hr hρ (takeD_vec_last LL T hadm n i) ?_ ?_ ?_` and prove the remaining obligations. Apply `natLog_le_lgSeg p a r _ ha0 (by omega)` to reduce the goal to its premises. Establish `h1 : ((((LL.setTies T n).takeD (T.pos i + 1)).total + r - 1 : ℕ) : ℝ) ≤ (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ) + r`.

Establish `: ((LL.setTies T n).takeD (T.pos i + 1)).total + r - 1 ≤ ((LL.setTies T n).takeD (T.pos i + 1)).total + r` using `Nat.sub_le _ _`. Conclude with `this` after adjusting the coercions. Use the polynomial consequences of the given equalities and inequalities. Apply `natLog_le_lgSeg p a r _ ha0 (by omega)` to reduce the goal to its premises. Establish `h1 : ((4 * ((LL.setTies T n).takeD (T.pos i + 1)).total + r - 1 : ℕ) : ℝ) ≤ 4 * (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ) + r`.

Establish `: 4 * ((LL.setTies T n).takeD (T.pos i + 1)).total + r - 1 ≤ 4 * ((LL.setTies T n).takeD (T.pos i + 1)).total + r` using `Nat.sub_le _ _`. Conclude with `this` after adjusting the coercions. Use the polynomial consequences of the given equalities and inequalities. Establish `hK : ((T.pos i : ℕ) : ℝ) + 7 ≤ 2 * ((s : ℝ) + 4)`. Establish `: T.pos i + 7 ≤ 2 * (s + 4)` using `by omega`.

Conclude with `this` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation.
-/
theorem theoremMV7 : TheoremMV7 := by
  intro p _ s r _ LL T a E Yl n₀ dd ρ hp hr hρ hadm hch hco ha hE hY hS hsz
  refine theoremMV7Of p s r LL T a E Yl n₀ dd ρ hp hr hρ hadm hch hco ha hE hY hS hsz ?_
  obtain ⟨htot, hsz⟩ := hsz
  have ha0 : 0 ≤ a := by linarith
  have hlg1 := one_le_lgSeg p a r ha0 (by omega)
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hp3 : (3 : ℝ) ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hy : (0 : ℝ) ≤ 8 * a + r := by linarith
  have hQ : 0 ≤ (r : ℝ) ^ 2 / 2 * lgSeg p a r := by positivity
  intro n hn
  have hle := grid_le T Yl n₀ dd n hn
  have hk : kapC p r (LL.setTies T n).total ≤ ⌊(r : ℝ) ^ 2 * lgSeg p a r⌋₊ := by
    apply Nat.le_floor
    have ht : ((LL.setTies T n).total : ℝ) ≤ 8 * a + r :=
      le_trans (by exact_mod_cast setTies_total_le LL T n _ hle) htot
    have hx : (((LL.setTies T n).total + r - 1 : ℕ) : ℝ) ≤ p * (8 * a + r) := by
      have h1 : (((LL.setTies T n).total + r - 1 : ℕ) : ℝ) ≤ ((LL.setTies T n).total : ℝ) + r := by
        have : (LL.setTies T n).total + r - 1 ≤ (LL.setTies T n).total + r := Nat.sub_le _ _
        exact_mod_cast this
      nlinarith
    have hl := natLog_le_lgSeg p a r _ ha0 (by omega) hx
    unfold kapC
    rw [Nat.cast_mul]
    calc ((r.choose 2 : ℕ) : ℝ) * (Nat.log p ((LL.setTies T n).total + r - 1) : ℝ)
        ≤ (r : ℝ) ^ 2 / 2 * lgSeg p a r := mul_le_mul (choose_two_le r) hl (Nat.cast_nonneg _) (by positivity)
      _ ≤ (r : ℝ) ^ 2 * lgSeg p a r := by nlinarith
  refine ⟨Formalism.InvariantFactorPaths.PW.Top.dischargeP p _ r _ ρ _ hk, Formalism.InvariantFactorPaths.PW.Top.dischargeW p _ r _ _ hk, fun i => ?_⟩
  obtain ⟨hlt, _, _⟩ := hadm.2.1 i
  obtain ⟨-, -, h2S⟩ := hsz i
  have hSle : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤
      T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i := by
    rw [takeD_total_eq (LL.setTies T n) T i hlt]; exact S_mono LL T n _ hle i
  have hSr : 2 * (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ) + 1 ≤ 8 * a + r := by
    have : (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ) ≤
        (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) := by exact_mod_cast hSle
    push_cast at h2S
    linarith
  have hS0 : (0 : ℝ) ≤ (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ) := Nat.cast_nonneg _
  refine gram_hypothesis_of_log_bound p (T.pos i) r _ T.J (T.thrUpTo i) ρ (lgSeg p a r) _ hr hρ (takeD_vec_last LL T hadm n i) ?_ ?_ ?_
  · apply natLog_le_lgSeg p a r _ ha0 (by omega)
    have h1 : ((((LL.setTies T n).takeD (T.pos i + 1)).total + r - 1 : ℕ) : ℝ) ≤
        (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ) + r := by
      have : ((LL.setTies T n).takeD (T.pos i + 1)).total + r - 1 ≤ ((LL.setTies T n).takeD (T.pos i + 1)).total + r :=
        Nat.sub_le _ _
      exact_mod_cast this
    nlinarith
  · apply natLog_le_lgSeg p a r _ ha0 (by omega)
    have h1 : ((4 * ((LL.setTies T n).takeD (T.pos i + 1)).total + r - 1 : ℕ) : ℝ) ≤
        4 * (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ) + r := by
      have : 4 * ((LL.setTies T n).takeD (T.pos i + 1)).total + r - 1 ≤
          4 * ((LL.setTies T n).takeD (T.pos i + 1)).total + r := Nat.sub_le _ _
      exact_mod_cast this
    nlinarith
  · have hK : ((T.pos i : ℕ) : ℝ) + 7 ≤ 2 * ((s : ℝ) + 4) := by
      have : T.pos i + 7 ≤ 2 * (s + 4) := by omega
      exact_mod_cast this
    calc (((T.pos i : ℕ) : ℝ) + 7) * ((r : ℝ) ^ 2 / 2 * lgSeg p a r)
        ≤ (2 * ((s : ℝ) + 4)) * ((r : ℝ) ^ 2 / 2 * lgSeg p a r) := mul_le_mul_of_nonneg_right hK hQ
      _ = ((s : ℝ) + 4) * ((r : ℝ) ^ 2 * lgSeg p a r) := by ring

end Formalism.InvariantFactorPaths.MC
