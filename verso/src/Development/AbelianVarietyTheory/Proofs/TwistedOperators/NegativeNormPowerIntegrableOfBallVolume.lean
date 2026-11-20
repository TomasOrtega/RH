import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

noncomputable section

namespace GlobalTheory.SepReal.powerIntegrability

/- English proof (translation)
Use `set a : Fin m := ⟨0, hm⟩`. Establish `h : (umat g)ᴴ * Jm ε * umat g = Jm ε` using `g.2`. Establish `h2` using `congrFun (congrFun h a) a`. Simplify using `only [Jm, Matrix.mul_diagonal, Matrix.diagonal_apply_eq] at h2`. Simplify using `only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.conjTranspose_apply] at h2`.

Establish `hn : (1 : ℝ) ≤ ∑ l, ‖umat g l a‖ ^ 2`. Apply the tactic sequence `have e1 : ‖((if ε a = true then 1 else -1 : ℂ))‖ = 1 := by split_ifs <;> simp`. Rewrite using `[← e1, ← h2]`. Use `(norm_sum_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> simp [sq]`. Establish `hc : ∑ l, ‖umat g l a‖ ^ 2 ≤ ∑ l, ∑ b, ‖umat g l b‖ ^ 2` using `Finset.sum_le_sum fun l _ => Finset.single_le_sum (f := fun b => ‖umat g l b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ a)`. Unfold `hsn`. Conclude with `Real.one_le_sqrt.mpr (hn.trans hc)`.
-/
theorem one_le_hsn {m : ℕ} {ε : Fin m → Bool} (hm : 1 ≤ m) (g : UJ ε) : 1 ≤ hsn (umat g) := by
  set a : Fin m := ⟨0, hm⟩
  have h : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2
  have h2 := congrFun (congrFun h a) a
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_apply_eq] at h2
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.conjTranspose_apply] at h2
  have hn : (1 : ℝ) ≤ ∑ l, ‖umat g l a‖ ^ 2 := by
    have e1 : ‖((if ε a = true then 1 else -1 : ℂ))‖ = 1 := by split_ifs <;> simp
    rw [← e1, ← h2]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp [sq]
  have hc : ∑ l, ‖umat g l a‖ ^ 2 ≤ ∑ l, ∑ b, ‖umat g l b‖ ^ 2 :=
    Finset.sum_le_sum fun l _ => Finset.single_le_sum (f := fun b => ‖umat g l b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ a)
  unfold hsn
  exact Real.one_le_sqrt.mpr (hn.trans hc)

/- English proof (translation)
Unfold `hsn`. Establish `hu : Continuous fun g : UJ ε => umat g` using `Units.continuous_val.comp continuous_subtype_val`. Use `Real.continuous_sqrt.comp ?_` and prove the remaining obligations. Use `continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_` and prove the remaining obligations. Conclude with `((continuous_apply b).comp ((continuous_apply a).comp hu)).norm.pow 2`.
-/
theorem continuous_hsn_umat {m : ℕ} (ε : Fin m → Bool) : Continuous fun g : UJ ε => hsn (umat g) := by
  unfold hsn
  have hu : Continuous fun g : UJ ε => umat g := Units.continuous_val.comp continuous_subtype_val
  refine Real.continuous_sqrt.comp ?_
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_
  exact ((continuous_apply b).comp ((continuous_apply a).comp hu)).norm.pow 2

end GlobalTheory.SepReal.powerIntegrability

namespace GlobalTheory.SepReal.powerIntegrability

/- English proof (translation)
Establish `hk : 1 ≤ m ^ 2` using `Nat.one_le_pow _ _ hm`. Establish `e1 : Real.exp (10 * (m : ℝ) ^ 2) = Real.exp 10 ^ (m ^ 2)`. Rewrite using `[← Real.exp_nat_mul]`. Use `push_cast`. Put the polynomial expressions in normal form.

Establish `e10 : (2178 : ℝ) ≤ Real.exp 10`. Establish `h1` using `Real.exp_one_gt_d9`. Establish `: Real.exp 10 = Real.exp 1 ^ 10` using `by rw [← Real.exp_nat_mul]; norm_num`. Rewrite using `[this]`. Combine the equalities or inequalities in the displayed calculation.

Establish `e2 : (33 : ℝ) ^ (2 * m ^ 2) = 1089 ^ (m ^ 2)` using `by rw [pow_mul]; norm_num`. Rewrite using `[e1, e2]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem const_le (m : ℕ) (hm : 1 ≤ m) : 2 * (33 : ℝ) ^ (2 * m ^ 2) ≤ Real.exp (10 * (m : ℝ) ^ 2) := by
  have hk : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
  have e1 : Real.exp (10 * (m : ℝ) ^ 2) = Real.exp 10 ^ (m ^ 2) := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have e10 : (2178 : ℝ) ≤ Real.exp 10 := by
    have h1 := Real.exp_one_gt_d9
    have : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (2178 : ℝ) ≤ 2.7182818283 ^ 10 := by norm_num
      _ ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) h1.le 10
  have e2 : (33 : ℝ) ^ (2 * m ^ 2) = 1089 ^ (m ^ 2) := by rw [pow_mul]; norm_num
  rw [e1, e2]
  calc 2 * (1089 : ℝ) ^ (m ^ 2) ≤ 2 ^ (m ^ 2) * 1089 ^ (m ^ 2) := by
        gcongr; exact le_self_pow₀ (by norm_num) (by omega)
    _ = 2178 ^ (m ^ 2) := by rw [← mul_pow]; norm_num
    _ ≤ Real.exp 10 ^ (m ^ 2) := pow_le_pow_left₀ (by norm_num) e10 _

/- English proof (translation)
Establish `h4 : (1 : ℝ) ≤ 4 ^ j` using `one_le_pow₀ (by norm_num)`. Establish `hb : 1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4) ≤ 33 * 4 ^ j`. Establish `: ((2 : ℝ) ^ (j + 1)) ^ 2 = 4 * 4 ^ j`. Rewrite using `[← pow_mul, pow_mul', show (2 : ℝ) ^ 2 = 4 by norm_num, pow_succ]; ring`. Rewrite using `[this]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hr0 : 0 ≤ (2 : ℝ) ^ (-A)` using `by positivity`. Establish `hq : (2 : ℝ) ^ (-A) * 4 ^ (2 * m ^ 2) ≤ 1 / 2`. Establish `e : (4 : ℝ) ^ (2 * m ^ 2) = (2 : ℝ) ^ ((4 * m ^ 2 : ℕ) : ℝ)`. Rewrite using `[Real.rpow_natCast, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf`.

Rewrite using `[e, ← Real.rpow_add (by norm_num)]`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm j]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ 33 ^ (2 * m ^ 2) * (1 / 2) ^ j := by gcongr`.
-/
theorem term_le (m : ℕ) (A : ℝ) (hA : 4 * (m : ℝ) ^ 2 + 1 ≤ A) (j : ℕ) :
    ((2 : ℝ) ^ (-A)) ^ j * (1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2) ≤ 33 ^ (2 * m ^ 2) * (1 / 2) ^ j := by
  have h4 : (1 : ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
  have hb : 1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4) ≤ 33 * 4 ^ j := by
    have : ((2 : ℝ) ^ (j + 1)) ^ 2 = 4 * 4 ^ j := by
      rw [← pow_mul, pow_mul', show (2 : ℝ) ^ 2 = 4 by norm_num, pow_succ]; ring
    rw [this]; linarith
  have hr0 : 0 ≤ (2 : ℝ) ^ (-A) := by positivity
  have hq : (2 : ℝ) ^ (-A) * 4 ^ (2 * m ^ 2) ≤ 1 / 2 := by
    have e : (4 : ℝ) ^ (2 * m ^ 2) = (2 : ℝ) ^ ((4 * m ^ 2 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
    rw [e, ← Real.rpow_add (by norm_num)]
    calc (2 : ℝ) ^ (-A + ((4 * m ^ 2 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  calc ((2 : ℝ) ^ (-A)) ^ j * (1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2)
      ≤ ((2 : ℝ) ^ (-A)) ^ j * (33 * 4 ^ j) ^ (2 * m ^ 2) := by
        gcongr
    _ = 33 ^ (2 * m ^ 2) * ((2 : ℝ) ^ (-A) * 4 ^ (2 * m ^ 2)) ^ j := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm j]; ring
    _ ≤ 33 ^ (2 * m ^ 2) * (1 / 2) ^ j := by
        gcongr

end GlobalTheory.SepReal.powerIntegrability

namespace GlobalTheory.SepReal

open GlobalTheory.SepReal.powerIntegrability in

/- English proof (translation)
Introduce `hV m ε A hm hA`. Take `⟨-, hfin, -⟩` from `hV m ε (1 / 4) 1 (by norm_num) one_pos`. Use `set μN := muG ε (nbh ε (1 / 4)) with hμN`. Use `set r : ℝ := (2 : ℝ) ^ (-A) with hr`. Establish `hcont` using `continuous_hsn_umat ε`.

Establish `hpos : ∀ g : UJ ε, 0 < hsn (umat g)` using `fun g => lt_of_lt_of_le one_pos (one_le_hsn hm g)`. Establish `hf_cont : Continuous fun g : UJ ε => hsn (umat g) ^ (-A)` using `hcont.rpow_const fun g => Or.inl (hpos g).ne'`. Establish `hf_nn : ∀ g : UJ ε, 0 ≤ hsn (umat g) ^ (-A)` using `fun g => (Real.rpow_pos_of_pos (hpos g) _).le`. Set `S : ℕ → Set (UJ ε)` to `fun j => {g | hsn (umat g) ≤ (2 : ℝ) ^ (j + 1)}`. Establish `hS : ∀ j, MeasurableSet (S j)` using `fun j => measurableSet_le hcont.measurable measurable_const`.

Establish `hpt : ∀ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ≤ ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (r ^ j)) g`. Introduce `g`. Take `⟨j, hj1, hj2⟩` from `exists_nat_pow_near (one_le_hsn hm g) (one_lt_two : (1 : ℝ) < 2)`. Use `le_trans ?_ (ENNReal.le_tsum j)` and prove the remaining obligations. Rewrite using `[Set.indicator_of_mem (show g ∈ S j from hj2.le)]`.

Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `key : r ^ j = ((2 : ℝ) ^ j) ^ (-A)`. Rewrite using `[hr, ← Real.rpow_natCast, ← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]`. Rewrite using `[key]`. Conclude with `Real.rpow_le_rpow_of_nonpos (by positivity) hj1 (by linarith [sq_nonneg (m : ℝ)])`.

Establish `hL : ∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε ≤ ENNReal.ofReal (2 * 33 ^ (2 * m ^ 2)) * μN`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `j`. Conclude with `lintegral_indicator_const (hS j) _`.

Use `_ ≤ ∑' j, ENNReal.ofReal (33 ^ (2 * m ^ 2)) * 2⁻¹ ^ j * μN := by`. Use `ENNReal.tsum_le_tsum fun j => ?_` and prove the remaining obligations. Establish `hb` using `(hV m ε (1 / 4) ((2 : ℝ) ^ (j + 1)) (by norm_num) (by positivity)).2.2`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]`.

Use `_ ≤ ENNReal.ofReal (33 ^ (2 * m ^ 2) * (1 / 2) ^ j) * μN := by`. Conclude with `mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (term_le m A hA j)) (zero_le')`. Use `_ = ENNReal.ofReal (33 ^ (2 * m ^ 2)) * 2⁻¹ ^ j * μN := by`. Establish `h2 : ENNReal.ofReal ((1 / 2 : ℝ) ^ j) = 2⁻¹ ^ j`. Rewrite using `[ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]`.

Rewrite using `[ENNReal.ofReal_mul (by positivity), h2]`. Use `_ = ENNReal.ofReal (33 ^ (2 * m ^ 2)) * (∑' j : ℕ, (2⁻¹ : ENNReal) ^ j) * μN := by`. Rewrite using `[ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]`. Use `_ = ENNReal.ofReal (2 * 33 ^ (2 * m ^ 2)) * μN := by`. Rewrite using `[ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_comm (2 : ENNReal)]`.

Establish `hLfin : ∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε < ⊤` using `lt_of_le_of_lt hL (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)`. Establish `hnn : 0 ≤ᵐ[muG ε] fun g => hsn (umat g) ^ (-A)` using `Filter.Eventually.of_forall hf_nn`. Use `⟨⟨hf_cont.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 hLfin⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_eq_lintegral_of_nonneg_ae hnn hf_cont.aestronglyMeasurable]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]`. Use `_ ≤ Real.exp (10 * (m : ℝ) ^ 2) * μN.toReal := mul_le_mul_of_nonneg_right (const_le m hm) ENNReal.toReal_nonneg`.
-/
theorem powInt_of_volBall : VolBall → PowInt := by
  intro hV m ε A hm hA
  obtain ⟨-, hfin, -⟩ := hV m ε (1 / 4) 1 (by norm_num) one_pos
  set μN := muG ε (nbh ε (1 / 4)) with hμN
  set r : ℝ := (2 : ℝ) ^ (-A) with hr
  have hcont := continuous_hsn_umat ε
  have hpos : ∀ g : UJ ε, 0 < hsn (umat g) := fun g => lt_of_lt_of_le one_pos (one_le_hsn hm g)
  have hf_cont : Continuous fun g : UJ ε => hsn (umat g) ^ (-A) :=
    hcont.rpow_const fun g => Or.inl (hpos g).ne'
  have hf_nn : ∀ g : UJ ε, 0 ≤ hsn (umat g) ^ (-A) := fun g => (Real.rpow_pos_of_pos (hpos g) _).le
  let S : ℕ → Set (UJ ε) := fun j => {g | hsn (umat g) ≤ (2 : ℝ) ^ (j + 1)}
  have hS : ∀ j, MeasurableSet (S j) := fun j => measurableSet_le hcont.measurable measurable_const
  have hpt : ∀ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ≤ ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (r ^ j)) g := by
    intro g
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near (one_le_hsn hm g) (one_lt_two : (1 : ℝ) < 2)
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [Set.indicator_of_mem (show g ∈ S j from hj2.le)]
    apply ENNReal.ofReal_le_ofReal
    have key : r ^ j = ((2 : ℝ) ^ j) ^ (-A) := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_mul (by norm_num), mul_comm]
    rw [key]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hj1 (by linarith [sq_nonneg (m : ℝ)])
  have hL : ∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε ≤ ENNReal.ofReal (2 * 33 ^ (2 * m ^ 2)) * μN := by
    calc ∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε
        ≤ ∫⁻ g, ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (r ^ j)) g ∂muG ε := lintegral_mono hpt
      _ = ∑' j, ∫⁻ g, (S j).indicator (fun _ => ENNReal.ofReal (r ^ j)) g ∂muG ε :=
          lintegral_tsum fun j => (measurable_const.indicator (hS j)).aemeasurable
      _ = ∑' j, ENNReal.ofReal (r ^ j) * muG ε (S j) := by
          congr 1; funext j; exact lintegral_indicator_const (hS j) _
      _ ≤ ∑' j, ENNReal.ofReal (33 ^ (2 * m ^ 2)) * 2⁻¹ ^ j * μN := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          have hb := (hV m ε (1 / 4) ((2 : ℝ) ^ (j + 1)) (by norm_num) (by positivity)).2.2
          calc ENNReal.ofReal (r ^ j) * muG ε (S j)
              ≤ ENNReal.ofReal (r ^ j) * (ENNReal.ofReal ((1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2)) * μN) :=
                by gcongr
            _ = ENNReal.ofReal (r ^ j * (1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2)) * μN := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            _ ≤ ENNReal.ofReal (33 ^ (2 * m ^ 2) * (1 / 2) ^ j) * μN := by
                exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (term_le m A hA j)) (zero_le')
            _ = ENNReal.ofReal (33 ^ (2 * m ^ 2)) * 2⁻¹ ^ j * μN := by
                have h2 : ENNReal.ofReal ((1 / 2 : ℝ) ^ j) = 2⁻¹ ^ j := by
                  rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
                rw [ENNReal.ofReal_mul (by positivity), h2]
      _ = ENNReal.ofReal (33 ^ (2 * m ^ 2)) * (∑' j : ℕ, (2⁻¹ : ENNReal) ^ j) * μN := by
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal (2 * 33 ^ (2 * m ^ 2)) * μN := by
          rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv, ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_ofNat, mul_comm (2 : ENNReal)]
  have hLfin : ∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε < ⊤ :=
    lt_of_le_of_lt hL (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  have hnn : 0 ≤ᵐ[muG ε] fun g => hsn (umat g) ^ (-A) := Filter.Eventually.of_forall hf_nn
  refine ⟨⟨hf_cont.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 hLfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf_cont.aestronglyMeasurable]
  calc (∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε).toReal
      ≤ (ENNReal.ofReal (2 * 33 ^ (2 * m ^ 2)) * μN).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) hL
    _ = 2 * 33 ^ (2 * m ^ 2) * μN.toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    _ ≤ Real.exp (10 * (m : ℝ) ^ 2) * μN.toReal :=
        mul_le_mul_of_nonneg_right (const_le m hm) ENNReal.toReal_nonneg

end GlobalTheory.SepReal

end
