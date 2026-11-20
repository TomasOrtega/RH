import Formalism.HermitianCurvature.StatementPB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JointInstanceTheoremA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PullLatticeTypedUnit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PeriodLatticeFactsSplitOfGeneral
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalisationScaledIdealMemIff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwistedIsRealOrderLattice

namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator

section Num1

open Formalism.FourierDecayAlt.PB Finset

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[Finset.Icc_eq_empty_of_lt (show (0:ℕ) < 1 by norm_num), Finset.prod_empty]`. Use `⟨?_, le_refl _⟩` and prove the remaining obligations. Evaluate the numerical expressions.

Consider the case `succ n ih`. Take `⟨h1, h2⟩` from `ih`. Rewrite using `[Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]`. Establish `hx1 : x ≤ 1` using `by linarith`. Establish `hy : x ^ (n + 1) ≤ x` using `pow_le_of_le_one hx0.le hx1 (Nat.succ_ne_zero n)`.

Establish `hy0 : 0 ≤ x ^ (n + 1)` using `pow_nonneg hx0.le _`. Establish `hyx : x ^ (n + 1 + 1) = x ^ (n + 1) * x` using `pow_succ x (n + 1)`. Establish `hP0 : 0 ≤ ∏ i ∈ Icc 1 n, (1 - x ^ i)` using `by linarith`. Prove the components needed by the constructor for the conclusion. Establish `e1` using `mul_le_mul_of_nonneg_right h1 (show (0:ℝ) ≤ 1 - x ^ (n + 1) by linarith)`.

Establish `e2` using `mul_nonneg hy0 (show (0:ℝ) ≤ 1 / 3 - x ^ (n + 1) by linarith)`. Rewrite using `[hyx]`. Use polynomial arithmetic with `[e1, e2]`. Establish `e3` using `mul_le_mul h2 (show 1 - x ^ (n + 1) ≤ 1 by linarith) (by linarith) zero_le_one`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma euler_product_bounds (x : ℝ) (hx0 : 0 < x) (hx : x ≤ 1 / 3) (k : ℕ) :
    1 - 3 / 2 * x + 3 / 2 * x ^ (k + 1) ≤ ∏ i ∈ Icc 1 k, (1 - x ^ i) ∧
      ∏ i ∈ Icc 1 k, (1 - x ^ i) ≤ 1 := by
  induction k with
  | zero =>
    rw [Finset.Icc_eq_empty_of_lt (show (0:ℕ) < 1 by norm_num), Finset.prod_empty]
    refine ⟨?_, le_refl _⟩
    norm_num
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have hx1 : x ≤ 1 := by linarith
    have hy : x ^ (n + 1) ≤ x := pow_le_of_le_one hx0.le hx1 (Nat.succ_ne_zero n)
    have hy0 : 0 ≤ x ^ (n + 1) := pow_nonneg hx0.le _
    have hyx : x ^ (n + 1 + 1) = x ^ (n + 1) * x := pow_succ x (n + 1)
    have hP0 : 0 ≤ ∏ i ∈ Icc 1 n, (1 - x ^ i) := by linarith
    constructor
    · have e1 := mul_le_mul_of_nonneg_right h1 (show (0:ℝ) ≤ 1 - x ^ (n + 1) by linarith)
      have e2 := mul_nonneg hy0 (show (0:ℝ) ≤ 1 / 3 - x ^ (n + 1) by linarith)
      rw [hyx]
      nlinarith [e1, e2]
    · have e3 := mul_le_mul h2 (show 1 - x ^ (n + 1) ≤ 1 by linarith) (by linarith) zero_le_one
      linarith

/- English proof (translation)
Introduce `k g hg`. Establish `hg0 : 0 < g` using `by linarith`. Establish `hx0 : 0 < g⁻¹` using `inv_pos.mpr hg0`. Establish `hgx : g⁻¹ * g = 1` using `inv_mul_cancel₀ hg0.ne'`. Establish `hx3 : g⁻¹ ≤ 1 / 3` using `by nlinarith [mul_le_mul_of_nonneg_left hg hx0.le]`.

Establish `hprod : ∏ i ∈ Icc 1 k, (1 - (g ^ i)⁻¹)⁻¹ = (∏ i ∈ Icc 1 k, (1 - g⁻¹ ^ i))⁻¹`. Rewrite using `[Finset.prod_inv_distrib]`. Use `congr 1`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[inv_pow]`.

Establish `e3 : (3:ℝ) / g = 3 * g⁻¹` using `div_eq_mul_inv 3 g`. Rewrite using `[hprod, e3]`. Take `⟨h1, -⟩` from `euler_product_bounds g⁻¹ hx0 hx3 k`. Establish `hpos : 0 < 1 - 3 / 2 * g⁻¹` using `by linarith`. Establish `hP : 1 - 3 / 2 * g⁻¹ ≤ ∏ i ∈ Icc 1 k, (1 - g⁻¹ ^ i)`.

Use `pow_nonneg hx0.le (k + 1)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hab : 1 ≤ (1 - 3 / 2 * g⁻¹) * (1 + 3 * g⁻¹)`. Use polynomial arithmetic with `[mul_nonneg hx0.le (show (0:ℝ) ≤ 1 / 3 - g⁻¹ by linarith)]`. Combine the equalities or inequalities in the displayed calculation.

Consider the case `exact inv_anti₀ hpos hP`. Consider the case `exact inv_le_inv_of_le hpos hP`. Use `_ = (1 - 3 / 2 * g⁻¹)⁻¹ * 1 := (mul_one _).symm`. Use `_ ≤ (1 - 3 / 2 * g⁻¹)⁻¹ * ((1 - 3 / 2 * g⁻¹) * (1 + 3 * g⁻¹)) := mul_le_mul_of_nonneg_left hab (inv_nonneg.mpr hpos.le)`. Use `_ = 1 + 3 * g⁻¹ := by rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]`.
-/
theorem t_GGNumeric : GGNumeric := by
  intro k g hg
  have hg0 : 0 < g := by linarith
  have hx0 : 0 < g⁻¹ := inv_pos.mpr hg0
  have hgx : g⁻¹ * g = 1 := inv_mul_cancel₀ hg0.ne'
  have hx3 : g⁻¹ ≤ 1 / 3 := by nlinarith [mul_le_mul_of_nonneg_left hg hx0.le]
  have hprod : ∏ i ∈ Icc 1 k, (1 - (g ^ i)⁻¹)⁻¹ = (∏ i ∈ Icc 1 k, (1 - g⁻¹ ^ i))⁻¹ := by
    rw [Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [inv_pow]
  have e3 : (3:ℝ) / g = 3 * g⁻¹ := div_eq_mul_inv 3 g
  rw [hprod, e3]
  obtain ⟨h1, -⟩ := euler_product_bounds g⁻¹ hx0 hx3 k
  have hpos : 0 < 1 - 3 / 2 * g⁻¹ := by linarith
  have hP : 1 - 3 / 2 * g⁻¹ ≤ ∏ i ∈ Icc 1 k, (1 - g⁻¹ ^ i) := by
    have := pow_nonneg hx0.le (k + 1)
    linarith
  have hab : 1 ≤ (1 - 3 / 2 * g⁻¹) * (1 + 3 * g⁻¹) := by
    nlinarith [mul_nonneg hx0.le (show (0:ℝ) ≤ 1 / 3 - g⁻¹ by linarith)]
  calc (∏ i ∈ Icc 1 k, (1 - g⁻¹ ^ i))⁻¹ ≤ (1 - 3 / 2 * g⁻¹)⁻¹ := by
        first
          | exact inv_anti₀ hpos hP
          | exact inv_le_inv_of_le hpos hP
    _ = (1 - 3 / 2 * g⁻¹)⁻¹ * 1 := (mul_one _).symm
    _ ≤ (1 - 3 / 2 * g⁻¹)⁻¹ * ((1 - 3 / 2 * g⁻¹) * (1 + 3 * g⁻¹)) :=
        mul_le_mul_of_nonneg_left hab (inv_nonneg.mpr hpos.le)
    _ = 1 + 3 * g⁻¹ := by rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

/- English proof (translation)
Introduce `k b hb hk`. Establish `h : Real.exp (-(14 * Real.log b)) = (b ^ 14)⁻¹`. Rewrite using `[Real.exp_neg]`. Use `congr 1`. Rewrite using `[show (14:ℝ) * Real.log b = Real.log (b ^ 14) by rw [Real.log_pow]; norm_num]`.

Conclude with `Real.exp_log (pow_pos hb 14)`. Rewrite using `[← h]`. Conclude with `Real.exp_le_exp.mpr (by linarith)`.
-/
theorem t_NumExp : NumExp := by
  intro k b hb hk
  have h : Real.exp (-(14 * Real.log b)) = (b ^ 14)⁻¹ := by
    rw [Real.exp_neg]
    congr 1
    rw [show (14:ℝ) * Real.log b = Real.log (b ^ 14) by rw [Real.log_pow]; norm_num]
    exact Real.exp_log (pow_pos hb 14)
  rw [← h]
  exact Real.exp_le_exp.mpr (by linarith)

/- English proof (translation)
Introduce `k f c h`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `hk : (0:ℝ) ≤ k` using `Nat.cast_nonneg k`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h hk]`.
-/
theorem t_NumLoops : NumLoops := by
  intro k f c h
  apply Real.exp_le_exp.mpr
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [mul_le_mul_of_nonneg_left h hk]

end Num1

section Num2

open Formalism.FourierDecayAlt.PB Finset

/- English proof (translation)
Rewrite using `[Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]`.
-/
lemma inv_two_pow (n : ℕ) : ((2 : ℝ) ^ n)⁻¹ = (2 : ℝ) ^ (-(n : ℝ)) := by
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]

/- English proof (translation)
Introduce `k r h`. Take `⟨j, rfl⟩ : ∃ j, k = 2 * r + 5 + j` from `⟨k - (2 * r + 5), by omega⟩`. Establish `hj : 2 * r + 5 + j - 2 * r - 5 = j` using `by omega`. Rewrite using `[hj, inv_two_pow]`. Apply `Real.rpow_le_rpow_of_exponent_le (by norm_num)` to reduce the goal to its premises.

Establish `h2 : ((4 * r + 10 : ℕ) : ℝ) ≤ ((2 * r + 5 + j : ℕ) : ℝ)` using `by exact_mod_cast h`. Move the coercions through the operations in `at h2 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem t_NGExponent : NGExponent := by
  intro k r h
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * r + 5 + j := ⟨k - (2 * r + 5), by omega⟩
  have hj : 2 * r + 5 + j - 2 * r - 5 = j := by omega
  rw [hj, inv_two_pow]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h2 : ((4 * r + 10 : ℕ) : ℝ) ≤ ((2 * r + 5 + j : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h2 ⊢
  linarith

/- English proof (translation)
Introduce `k m f C b h`. Establish `hk : (0:ℝ) ≤ k` using `Nat.cast_nonneg k`. Establish `hl : (0.69:ℝ) < Real.log 2`. Use `Real.log_two_gt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), ← Real.exp_add]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hl.le hk]`.
-/
theorem t_NumNG : NumNG := by
  intro k m f C b h
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hl : (0.69:ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hl.le hk]

/- English proof (translation)
Introduce `k r f hf hk32 hr`. Establish `hkR : (32:ℝ) ≤ k` using `by exact_mod_cast hk32`. Establish `hk0 : (0:ℝ) < k` using `by linarith`. Establish `hfk : (f:ℝ) ≤ k` using `by exact_mod_cast hf`. Establish `hf0 : (0:ℝ) ≤ f` using `Nat.cast_nonneg f`.

Establish `key : 12 * ((2:ℝ) ^ (k - 2 * r - 2))⁻¹ ≤ (2:ℝ) ^ (-(k:ℝ) / 2)`. Take `⟨j, rfl⟩ : ∃ j, k = 2 * r + 2 + j` from `⟨k - (2 * r + 2), by omega⟩`. Establish `hj : 2 * r + 2 + j - 2 * r - 2 = j` using `by omega`. Rewrite using `[hj, inv_two_pow]`. Establish `e : -((2 * r + 2 + j : ℕ) : ℝ) / 2 = -(j:ℝ) + ((j:ℝ) - 2 * r - 2) / 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Real.rpow_add (by norm_num : (0:ℝ) < 2)]`. Establish `h4 : (4:ℝ) ≤ ((j:ℝ) - 2 * r - 2) / 2`. Establish `: ((4 * r + 12 : ℕ) : ℝ) ≤ ((2 * r + 2 + j : ℕ) : ℝ)` using `by exact_mod_cast hr`.

Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h16 : (16:ℝ) ≤ (2:ℝ) ^ (((j:ℝ) - 2 * r - 2) / 2)`. Combine the equalities or inequalities in the displayed calculation. Establish `hp : 0 < (2:ℝ) ^ (-(j:ℝ))` using `Real.rpow_pos_of_pos (by norm_num) _`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h16 hp.le]`. Prove the components needed by the constructor for the conclusion. Use `mul_le_mul_of_nonneg_left key hf0` as an intermediate fact. Use polynomial arithmetic with `[this]`. Establish `hL1` using `Real.log_two_gt_d9`.

Establish `hL2` using `Real.log_two_lt_d9`. Establish `hlog : Real.log k ≤ 5 * Real.log 2 + k / 32 - 1`. Establish `h1` using `Real.log_le_sub_one_of_pos (show (0:ℝ) < k / 32 by positivity)`. Rewrite `h1` using `[Real.log_div hk0.ne' (by norm_num)]`. Establish `h32 : Real.log (32:ℝ) = 5 * Real.log 2`.

Rewrite using `[show (32:ℝ) = 2 ^ 5 by norm_num, Real.log_pow]`. Evaluate the numerical expressions. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Real.exp_add, Real.exp_log hk0]`. Use `_ ≤ Real.exp (-(k:ℝ) / 5) := by`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hL1.le hk0.le]`.
-/
theorem t_NumDens : NumDens := by
  intro k r f hf hk32 hr
  have hkR : (32:ℝ) ≤ k := by exact_mod_cast hk32
  have hk0 : (0:ℝ) < k := by linarith
  have hfk : (f:ℝ) ≤ k := by exact_mod_cast hf
  have hf0 : (0:ℝ) ≤ f := Nat.cast_nonneg f
  have key : 12 * ((2:ℝ) ^ (k - 2 * r - 2))⁻¹ ≤ (2:ℝ) ^ (-(k:ℝ) / 2) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 * r + 2 + j := ⟨k - (2 * r + 2), by omega⟩
    have hj : 2 * r + 2 + j - 2 * r - 2 = j := by omega
    rw [hj, inv_two_pow]
    have e : -((2 * r + 2 + j : ℕ) : ℝ) / 2 = -(j:ℝ) + ((j:ℝ) - 2 * r - 2) / 2 := by
      push_cast
      ring
    rw [e, Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    have h4 : (4:ℝ) ≤ ((j:ℝ) - 2 * r - 2) / 2 := by
      have : ((4 * r + 12 : ℕ) : ℝ) ≤ ((2 * r + 2 + j : ℕ) : ℝ) := by exact_mod_cast hr
      push_cast at this
      linarith
    have h16 : (16:ℝ) ≤ (2:ℝ) ^ (((j:ℝ) - 2 * r - 2) / 2) := by
      calc (16:ℝ) = (2:ℝ) ^ ((4:ℕ):ℝ) := by rw [Real.rpow_natCast]; norm_num
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
    have hp : 0 < (2:ℝ) ^ (-(j:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    nlinarith [mul_le_mul_of_nonneg_left h16 hp.le]
  constructor
  · have := mul_le_mul_of_nonneg_left key hf0
    nlinarith [this]
  · have hL1 := Real.log_two_gt_d9
    have hL2 := Real.log_two_lt_d9
    have hlog : Real.log k ≤ 5 * Real.log 2 + k / 32 - 1 := by
      have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < k / 32 by positivity)
      rw [Real.log_div hk0.ne' (by norm_num)] at h1
      have h32 : Real.log (32:ℝ) = 5 * Real.log 2 := by
        rw [show (32:ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
        norm_num
      linarith
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    calc (f:ℝ) * Real.exp (Real.log 2 * (-(k:ℝ) / 2))
        ≤ (k:ℝ) * Real.exp (Real.log 2 * (-(k:ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right hfk (Real.exp_pos _).le
      _ = Real.exp (Real.log k + Real.log 2 * (-(k:ℝ) / 2)) := by
          rw [Real.exp_add, Real.exp_log hk0]
      _ ≤ Real.exp (-(k:ℝ) / 5) := by
          apply Real.exp_le_exp.mpr
          nlinarith [mul_le_mul_of_nonneg_left hL1.le hk0.le]

/- English proof (translation)
Establish `hkR : (1:ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hfk : (f:ℝ) ≤ k` using `by exact_mod_cast hf`. Establish `hb0 : 0 < b` using `by linarith`. Establish `hkb : b ≤ k * b` using `by nlinarith`. Establish `hkb' : (k:ℝ) ≤ k * b` using `by nlinarith`.

Establish `hkb0 : 0 ≤ (k:ℝ) * b` using `by linarith`. Establish `h7 : b ^ 7 ≤ (k * b) ^ 7` using `pow_le_pow_left₀ hb0.le hkb 7`. Establish `hb7 : 0 < b ^ 7` using `pow_pos hb0 7`. Establish `hb71 : (1:ℝ) ≤ b ^ 7`. Use `pow_le_pow_left₀ zero_le_one hb 7` as an intermediate fact.

Simplify using `using this`. Establish `e8 : ((k:ℝ) * b) ^ 8 = (k * b) ^ 7 * (k * b)` using `by ring`. Establish `hk8 : (k:ℝ) * b ^ 7 ≤ (k * b) ^ 8`. Use polynomial arithmetic with `[mul_le_mul h7 hkb' (by linarith) (pow_nonneg hkb0 7)]`. Establish `hkb7 : b ^ 7 ≤ (k:ℝ) * b ^ 7` using `by nlinarith [mul_le_mul_of_nonneg_right hkR hb7.le]`.

Establish `hg0 : 0 < g` using `by linarith`. Establish `hfg : (f:ℝ) * b ^ 7 ≤ g`. Use `mul_le_mul_of_nonneg_right hfk hb7.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfb : (f:ℝ) ≤ (b ^ 7)⁻¹ * g`.

Combine the equalities or inequalities in the displayed calculation. Establish `hdiv : (f:ℝ) / g ≤ (b ^ 7)⁻¹` using `by first`. Consider the case `exact (div_le_iff₀ hg0).mpr hfb`. Consider the case `exact (div_le_iff hg0).mpr hfb`. Establish `hpos0 : 0 ≤ 1 + 3 / g`.

Use `div_pos (show (0:ℝ) < 3 by norm_num) hg0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : 1 + 3 / g ≤ Real.exp (3 / g)` using `by linarith [Real.add_one_le_exp (3 / g)]`. Establish `h2 : (1 + 3 / g) ^ f ≤ Real.exp (3 / g) ^ f` using `pow_le_pow_left₀ hpos0 h1 f`. Rewrite `h2` using `[← Real.exp_nat_mul]`.

Establish `h3 : (f:ℝ) * (3 / g) ≤ 3 * (b ^ 7)⁻¹`. Establish `: (f:ℝ) * (3 / g) = 3 * (f / g)` using `by ring`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `⟨hg0, hdiv, pow_nonneg hpos0 f, h2.trans (Real.exp_le_exp.mpr h3)⟩`.
-/
lemma price_exponential_bound (f k : ℕ) (b g : ℝ) (hb : 1 ≤ b) (hk : 1 ≤ k) (hf : f ≤ k)
    (hg : ((k : ℝ) * b) ^ 8 ≤ g) :
    0 < g ∧ (f : ℝ) / g ≤ (b ^ 7)⁻¹ ∧ 0 ≤ (1 + 3 / g) ^ f ∧
      (1 + 3 / g) ^ f ≤ Real.exp (3 * (b ^ 7)⁻¹) := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hfk : (f:ℝ) ≤ k := by exact_mod_cast hf
  have hb0 : 0 < b := by linarith
  have hkb : b ≤ k * b := by nlinarith
  have hkb' : (k:ℝ) ≤ k * b := by nlinarith
  have hkb0 : 0 ≤ (k:ℝ) * b := by linarith
  have h7 : b ^ 7 ≤ (k * b) ^ 7 := pow_le_pow_left₀ hb0.le hkb 7
  have hb7 : 0 < b ^ 7 := pow_pos hb0 7
  have hb71 : (1:ℝ) ≤ b ^ 7 := by
    have := pow_le_pow_left₀ zero_le_one hb 7
    simpa using this
  have e8 : ((k:ℝ) * b) ^ 8 = (k * b) ^ 7 * (k * b) := by ring
  have hk8 : (k:ℝ) * b ^ 7 ≤ (k * b) ^ 8 := by
    nlinarith [mul_le_mul h7 hkb' (by linarith) (pow_nonneg hkb0 7)]
  have hkb7 : b ^ 7 ≤ (k:ℝ) * b ^ 7 := by nlinarith [mul_le_mul_of_nonneg_right hkR hb7.le]
  have hg0 : 0 < g := by linarith
  have hfg : (f:ℝ) * b ^ 7 ≤ g := by
    have := mul_le_mul_of_nonneg_right hfk hb7.le
    linarith
  have hfb : (f:ℝ) ≤ (b ^ 7)⁻¹ * g := by
    calc (f:ℝ) = (f * b ^ 7) * (b ^ 7)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hb7.ne', mul_one]
      _ ≤ g * (b ^ 7)⁻¹ := mul_le_mul_of_nonneg_right hfg (inv_nonneg.mpr hb7.le)
      _ = (b ^ 7)⁻¹ * g := mul_comm _ _
  have hdiv : (f:ℝ) / g ≤ (b ^ 7)⁻¹ := by
    first
      | exact (div_le_iff₀ hg0).mpr hfb
      | exact (div_le_iff hg0).mpr hfb
  have hpos0 : 0 ≤ 1 + 3 / g := by
    have := div_pos (show (0:ℝ) < 3 by norm_num) hg0
    linarith
  have h1 : 1 + 3 / g ≤ Real.exp (3 / g) := by linarith [Real.add_one_le_exp (3 / g)]
  have h2 : (1 + 3 / g) ^ f ≤ Real.exp (3 / g) ^ f := pow_le_pow_left₀ hpos0 h1 f
  rw [← Real.exp_nat_mul] at h2
  have h3 : (f:ℝ) * (3 / g) ≤ 3 * (b ^ 7)⁻¹ := by
    have : (f:ℝ) * (3 / g) = 3 * (f / g) := by ring
    rw [this]
    linarith
  exact ⟨hg0, hdiv, pow_nonneg hpos0 f, h2.trans (Real.exp_le_exp.mpr h3)⟩

/- English proof (translation)
Introduce `f k b g1 g2 hb hk hf h1 h2`. Take `⟨-, a1, b1, c1⟩` from `price_exponential_bound f k b g1 hb hk hf h1`. Take `⟨-, a2, b2, c2⟩` from `price_exponential_bound f k b g2 hb hk hf h2`. Use `⟨a1, a2, mul_nonneg b1 b2, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem t_NumPrice : NumPrice := by
  intro f k b g1 g2 hb hk hf h1 h2
  obtain ⟨-, a1, b1, c1⟩ := price_exponential_bound f k b g1 hb hk hf h1
  obtain ⟨-, a2, b2, c2⟩ := price_exponential_bound f k b g2 hb hk hf h2
  refine ⟨a1, a2, mul_nonneg b1 b2, ?_⟩
  calc (1 + 3 / g1) ^ f * (1 + 3 / g2) ^ f
      ≤ Real.exp (3 * (b ^ 7)⁻¹) * Real.exp (3 * (b ^ 7)⁻¹) :=
        mul_le_mul c1 c2 b2 (Real.exp_pos _).le
    _ = Real.exp (6 * (b ^ 7)⁻¹) := by
        rw [← Real.exp_add]
        congr 1
        ring

end Num2

section Num3

open Formalism.FourierDecayAlt.PB Finset

/- English proof (translation)
Establish `h` using `Real.add_one_le_exp (-y)`. Establish `hp` using `Real.exp_pos y`. Establish `e : Real.exp y * Real.exp (-y) = 1` using `by rw [← Real.exp_add]; simp`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h hp.le]`.
-/
lemma exp_mul_one_sub_le (y : ℝ) : Real.exp y * (1 - y) ≤ 1 := by
  have h := Real.add_one_le_exp (-y)
  have hp := Real.exp_pos y
  have e : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [mul_le_mul_of_nonneg_left h hp.le]

/- English proof (translation)
Establish `h` using `exp_mul_one_sub_le x`. Establish `hp` using `Real.exp_pos x`. Use polynomial arithmetic with `[mul_nonneg (sq_nonneg x) (show (0:ℝ) ≤ 1 / 2 - x by linarith), mul_nonneg h0 (show (0:ℝ) ≤ 1 / 2 - x by linarith), mul_nonneg hp.le h0]`.
-/
private theorem exp_le_quad_lemma (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + x + 2 * x ^ 2 := by
  have h := exp_mul_one_sub_le x
  have hp := Real.exp_pos x
  nlinarith [mul_nonneg (sq_nonneg x) (show (0:ℝ) ≤ 1 / 2 - x by linarith),
    mul_nonneg h0 (show (0:ℝ) ≤ 1 / 2 - x by linarith), mul_nonneg hp.le h0]

/- English proof (translation)
Introduce `b Pg A ε ε' hb hPg0 hPg hA hε hε'`. Establish `hb0 : 0 < b` using `by linarith`. Take `⟨u, hu⟩ : ∃ u, u = (b ^ 7)⁻¹` from `⟨_, rfl⟩`. Establish `hu0 : 0 < u` using `by rw [hu]; exact inv_pos.mpr (pow_pos hb0 7)`. Establish `hb7 : (1000:ℝ) ≤ b ^ 7`.

Establish `h16 : (16:ℝ) ^ 7 ≤ b ^ 7` using `pow_le_pow_left₀ (by norm_num) hb 7`. Establish `: (1000:ℝ) ≤ 16 ^ 7` using `by norm_num`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hu1 : u ≤ 1 / 1000`. Rewrite using `[hu, inv_eq_one_div]`.

Conclude with `one_div_le_one_div_of_le (by norm_num) hb7`. Establish `hw : (0:ℝ) ≤ 1 / 1000 - u` using `by linarith`. Establish `h14 : (b ^ 14)⁻¹ = u ^ 2`. Apply the tactic sequence `rw [hu, inv_pow, ← pow_mul] <;> norm_num`. Establish `h6 : 16 * u ≤ (b ^ 6)⁻¹`.

Establish `e : (b ^ 6)⁻¹ = b * u`. Establish `hbne : b ≠ 0` using `hb0.ne'`. Rewrite using `[hu]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`.

Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite `hPg`, `hA` using `[← hu]`. Rewrite `hA`, `hε`, `hε'` using `[h14]`. Establish `hE : Real.exp (6 * u) ≤ 1 + 7 * u`.

Use `exp_le_quad_lemma (6 * u) (by linarith) (by linarith)` as an intermediate fact. Use polynomial arithmetic with `[mul_nonneg hu0.le hw]`. Establish `hF : Real.exp (u ^ 2) ≤ 1 + u`. Use `exp_le_quad_lemma (u ^ 2) (by positivity) (by nlinarith)` as an intermediate fact. Use polynomial arithmetic with `[mul_nonneg hu0.le hw, mul_nonneg (sq_nonneg u) hw, mul_nonneg (pow_nonneg hu0.le 3) hw]`.

Establish `hM : A + 2 * ε ≤ 1 + 3 * u`. Establish `h1 : (1 + u) * Real.exp (u ^ 2) ≤ (1 + u) * (1 + u)` using `mul_le_mul_of_nonneg_left hF (by linarith)`. Use polynomial arithmetic with `[mul_nonneg hu0.le hw]`. Establish `hX : Pg * (A + 2 * ε) ≤ 1 + 11 * u`. Establish `h1 : Pg * (A + 2 * ε) ≤ Pg * (1 + 3 * u)` using `mul_le_mul_of_nonneg_left hM hPg0`.

Establish `h2 : Pg * (1 + 3 * u) ≤ (1 + 7 * u) * (1 + 3 * u)` using `mul_le_mul_of_nonneg_right (hPg.trans hE) (by linarith)`. Use polynomial arithmetic with `[mul_nonneg hu0.le hw]`. Establish `hY : Pg * (ε + ε') ≤ 3 * u ^ 2`. Establish `h1 : Pg * (ε + ε') ≤ Pg * (2 * u ^ 2)` using `mul_le_mul_of_nonneg_left (by linarith) hPg0`. Establish `h2 : Pg * (2 * u ^ 2) ≤ (1 + 7 * u) * (2 * u ^ 2)` using `mul_le_mul_of_nonneg_right (hPg.trans hE) (by positivity)`.

Use polynomial arithmetic with `[mul_nonneg (sq_nonneg u) hw]`. Establish `hs0 : 0 ≤ √(Pg * (A + 2 * ε))` using `Real.sqrt_nonneg _`. Establish `ht0 : 0 ≤ √(Pg * (ε + ε'))` using `Real.sqrt_nonneg _`. Establish `hs2 : √(Pg * (A + 2 * ε)) ^ 2 ≤ 1 + 11 * u`. Combine the equalities or inequalities in the displayed calculation.

Establish `ht2 : √(Pg * (ε + ε')) ^ 2 ≤ 3 * u ^ 2`. Combine the equalities or inequalities in the displayed calculation. Establish `hc1 : (0:ℝ) ≤ 1 + 11 / 2 * u` using `by linarith`. Establish `hc2 : (0:ℝ) ≤ 7 / 4 * u` using `by linarith`. Establish `hsb : √(Pg * (A + 2 * ε)) ≤ 1 + 11 / 2 * u`.

Use polynomial arithmetic with `[hs2, hs0, hc1, sq_nonneg u]`. Establish `htb : √(Pg * (ε + ε')) ≤ 7 / 4 * u`. Use polynomial arithmetic with `[ht2, ht0, hc2, sq_nonneg u]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem t_EtaZero : SqrtSumSqLeOneAddInvPowSix := by
  intro b Pg A ε ε' hb hPg0 hPg hA hε hε'
  have hb0 : 0 < b := by linarith
  obtain ⟨u, hu⟩ : ∃ u, u = (b ^ 7)⁻¹ := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; exact inv_pos.mpr (pow_pos hb0 7)
  have hb7 : (1000:ℝ) ≤ b ^ 7 := by
    have h16 : (16:ℝ) ^ 7 ≤ b ^ 7 := pow_le_pow_left₀ (by norm_num) hb 7
    have : (1000:ℝ) ≤ 16 ^ 7 := by norm_num
    linarith
  have hu1 : u ≤ 1 / 1000 := by
    rw [hu, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hb7
  have hw : (0:ℝ) ≤ 1 / 1000 - u := by linarith
  have h14 : (b ^ 14)⁻¹ = u ^ 2 := by
    rw [hu, inv_pow, ← pow_mul] <;> norm_num
  have h6 : 16 * u ≤ (b ^ 6)⁻¹ := by
    have e : (b ^ 6)⁻¹ = b * u := by
      have hbne : b ≠ 0 := hb0.ne'
      rw [hu]
      field_simp
      try ring
    rw [e]
    nlinarith
  rw [← hu] at hPg hA
  rw [h14] at hA hε hε'
  have hE : Real.exp (6 * u) ≤ 1 + 7 * u := by
    have := exp_le_quad_lemma (6 * u) (by linarith) (by linarith)
    nlinarith [mul_nonneg hu0.le hw]
  have hF : Real.exp (u ^ 2) ≤ 1 + u := by
    have := exp_le_quad_lemma (u ^ 2) (by positivity) (by nlinarith)
    nlinarith [mul_nonneg hu0.le hw, mul_nonneg (sq_nonneg u) hw,
      mul_nonneg (pow_nonneg hu0.le 3) hw]
  have hM : A + 2 * ε ≤ 1 + 3 * u := by
    have h1 : (1 + u) * Real.exp (u ^ 2) ≤ (1 + u) * (1 + u) :=
      mul_le_mul_of_nonneg_left hF (by linarith)
    nlinarith [mul_nonneg hu0.le hw]
  have hX : Pg * (A + 2 * ε) ≤ 1 + 11 * u := by
    have h1 : Pg * (A + 2 * ε) ≤ Pg * (1 + 3 * u) := mul_le_mul_of_nonneg_left hM hPg0
    have h2 : Pg * (1 + 3 * u) ≤ (1 + 7 * u) * (1 + 3 * u) :=
      mul_le_mul_of_nonneg_right (hPg.trans hE) (by linarith)
    nlinarith [mul_nonneg hu0.le hw]
  have hY : Pg * (ε + ε') ≤ 3 * u ^ 2 := by
    have h1 : Pg * (ε + ε') ≤ Pg * (2 * u ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hPg0
    have h2 : Pg * (2 * u ^ 2) ≤ (1 + 7 * u) * (2 * u ^ 2) :=
      mul_le_mul_of_nonneg_right (hPg.trans hE) (by positivity)
    nlinarith [mul_nonneg (sq_nonneg u) hw]
  have hs0 : 0 ≤ √(Pg * (A + 2 * ε)) := Real.sqrt_nonneg _
  have ht0 : 0 ≤ √(Pg * (ε + ε')) := Real.sqrt_nonneg _
  have hs2 : √(Pg * (A + 2 * ε)) ^ 2 ≤ 1 + 11 * u := by
    calc √(Pg * (A + 2 * ε)) ^ 2 ≤ (√(1 + 11 * u)) ^ 2 :=
          pow_le_pow_left₀ hs0 (Real.sqrt_le_sqrt hX) 2
      _ = 1 + 11 * u := Real.sq_sqrt (by linarith)
  have ht2 : √(Pg * (ε + ε')) ^ 2 ≤ 3 * u ^ 2 := by
    calc √(Pg * (ε + ε')) ^ 2 ≤ (√(3 * u ^ 2)) ^ 2 :=
          pow_le_pow_left₀ ht0 (Real.sqrt_le_sqrt hY) 2
      _ = 3 * u ^ 2 := Real.sq_sqrt (by positivity)
  have hc1 : (0:ℝ) ≤ 1 + 11 / 2 * u := by linarith
  have hc2 : (0:ℝ) ≤ 7 / 4 * u := by linarith
  have hsb : √(Pg * (A + 2 * ε)) ≤ 1 + 11 / 2 * u := by
    nlinarith [hs2, hs0, hc1, sq_nonneg u]
  have htb : √(Pg * (ε + ε')) ≤ 7 / 4 * u := by
    nlinarith [ht2, ht0, hc2, sq_nonneg u]
  calc (√(Pg * (A + 2 * ε)) + √(Pg * (ε + ε'))) ^ 2 ≤ (1 + 11 / 2 * u + 7 / 4 * u) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (add_le_add hsb htb) 2
    _ ≤ 1 + 16 * u := by nlinarith [mul_nonneg hu0.le hw]
    _ ≤ 1 + (b ^ 6)⁻¹ := by linarith

end Num3

section Num4

open Formalism.FourierDecayAlt.PB

/- English proof (translation)
Introduce `δ y z hδ hy hz h1`. Establish `hx0 : 0 ≤ δ + y + z` using `by linarith`. Establish `hconv` using `convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ)) (show (0:ℝ) ≤ 1 - (δ + y + z) by linarith) hx0 (by ring)`. Simplify using `only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.exp_zero] at hconv`. Establish `he` using `Real.exp_one_lt_d9`.

Establish `hδe : 1 + δ ≤ Real.exp δ` using `by linarith [Real.add_one_le_exp δ]`. Establish `hprod : (1 + δ) * Real.exp y * Real.exp z ≤ Real.exp (δ + y + z)`. Rewrite using `[Real.exp_add, Real.exp_add, mul_assoc, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right hδe (by positivity)`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left he.le hx0]`.
-/
theorem t_MainRowShape : MainRowShape := by
  intro δ y z hδ hy hz h1
  have hx0 : 0 ≤ δ + y + z := by linarith
  have hconv := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ))
    (show (0:ℝ) ≤ 1 - (δ + y + z) by linarith) hx0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.exp_zero] at hconv
  have he := Real.exp_one_lt_d9
  have hδe : 1 + δ ≤ Real.exp δ := by linarith [Real.add_one_le_exp δ]
  have hprod : (1 + δ) * Real.exp y * Real.exp z ≤ Real.exp (δ + y + z) := by
    rw [Real.exp_add, Real.exp_add, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hδe (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left he.le hx0]

end Num4

section Hil1

open Formalism.FourierDecayAlt.PB Finset

/- English proof (translation)
Introduce `τ Rw I H H₁ _ _ _ _ _ X hX`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `t`. Simplify using `only [Set.mem_union, Set.mem_univ, iff_true]`. Distinguish the cases in `h1 : X.isId t`.

Conclude with `Or.inl (Or.inl (Or.inl h1))`. Distinguish the cases in `h2 : X.G t = 0`. Conclude with `Or.inl (Or.inl (Or.inr ⟨h2, h1⟩))`. Distinguish the cases in `h3 : X.gener t`. Conclude with `Or.inr ⟨h2, h3⟩`.

Conclude with `Or.inl (Or.inr ⟨h2, h3⟩)`. Rewrite using `[Set.disjoint_left]`. Introduce `t h1 h2`. Establish `a : X.isId t` using `h1`. Establish `b : X.G t = 0 ∧ ¬ X.isId t` using `h2`.

Conclude with `b.2 a`. Rewrite using `[Set.disjoint_left]`. Introduce `t h1 h2`. Establish `a : X.isId t` using `h1`. Establish `b : X.G t ≠ 0 ∧ ¬ X.gener t` using `h2`.

Conclude with `b.1 (hX t a)`. Rewrite using `[Set.disjoint_left]`. Introduce `t h1 h2`. Establish `a : X.isId t` using `h1`. Establish `b : X.G t ≠ 0 ∧ X.gener t` using `h2`.

Conclude with `b.1 (hX t a)`. Rewrite using `[Set.disjoint_left]`. Introduce `t h1 h2`. Establish `a : X.G t = 0 ∧ ¬ X.isId t` using `h1`. Establish `b : X.G t ≠ 0 ∧ ¬ X.gener t` using `h2`.

Conclude with `b.1 a.1`. Rewrite using `[Set.disjoint_left]`. Introduce `t h1 h2`. Establish `a : X.G t = 0 ∧ ¬ X.isId t` using `h1`. Establish `b : X.G t ≠ 0 ∧ X.gener t` using `h2`.

Conclude with `b.1 a.1`. Rewrite using `[Set.disjoint_left]`. Introduce `t h1 h2`. Establish `a : X.G t ≠ 0 ∧ ¬ X.gener t` using `h1`. Establish `b : X.G t ≠ 0 ∧ X.gener t` using `h2`.

Conclude with `a.2 b.2`.
-/
theorem t_FourParts : FourParts := by
  intro τ Rw I H H₁ _ _ _ _ _ X hX
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext t
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases h1 : X.isId t
    · exact Or.inl (Or.inl (Or.inl h1))
    · by_cases h2 : X.G t = 0
      · exact Or.inl (Or.inl (Or.inr ⟨h2, h1⟩))
      · by_cases h3 : X.gener t
        · exact Or.inr ⟨h2, h3⟩
        · exact Or.inl (Or.inr ⟨h2, h3⟩)
  · rw [Set.disjoint_left]
    intro t h1 h2
    have a : X.isId t := h1
    have b : X.G t = 0 ∧ ¬ X.isId t := h2
    exact b.2 a
  · rw [Set.disjoint_left]
    intro t h1 h2
    have a : X.isId t := h1
    have b : X.G t ≠ 0 ∧ ¬ X.gener t := h2
    exact b.1 (hX t a)
  · rw [Set.disjoint_left]
    intro t h1 h2
    have a : X.isId t := h1
    have b : X.G t ≠ 0 ∧ X.gener t := h2
    exact b.1 (hX t a)
  · rw [Set.disjoint_left]
    intro t h1 h2
    have a : X.G t = 0 ∧ ¬ X.isId t := h1
    have b : X.G t ≠ 0 ∧ ¬ X.gener t := h2
    exact b.1 a.1
  · rw [Set.disjoint_left]
    intro t h1 h2
    have a : X.G t = 0 ∧ ¬ X.isId t := h1
    have b : X.G t ≠ 0 ∧ X.gener t := h2
    exact b.1 a.1
  · rw [Set.disjoint_left]
    intro t h1 h2
    have a : X.G t ≠ 0 ∧ ¬ X.gener t := h1
    have b : X.G t ≠ 0 ∧ X.gener t := h2
    exact a.2 b.2

/- English proof (translation)
Introduce `H _ x y η ε dd hdd hx hy`. Establish `hx' : ‖x‖ ≤ √(1 + η + ε) * √dd`. Rewrite using `[← Real.sqrt_mul' _ hdd]`. Combine the equalities or inequalities in the displayed calculation. Establish `hy' : ‖y‖ ≤ √ε * √dd`.

Rewrite using `[← Real.sqrt_mul' _ hdd]`. Combine the equalities or inequalities in the displayed calculation. Establish `hxy : ‖x + y‖ ≤ (√(1 + η + ε) + √ε) * √dd`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem t_TextClosing : NormSqAddBoundBySqrtSum := by
  intro H _ x y η ε dd hdd hx hy
  have hx' : ‖x‖ ≤ √(1 + η + ε) * √dd := by
    rw [← Real.sqrt_mul' _ hdd]
    calc ‖x‖ = √(‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
      _ ≤ √((1 + η + ε) * dd) := Real.sqrt_le_sqrt hx
  have hy' : ‖y‖ ≤ √ε * √dd := by
    rw [← Real.sqrt_mul' _ hdd]
    calc ‖y‖ = √(‖y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg y)).symm
      _ ≤ √(ε * dd) := Real.sqrt_le_sqrt hy
  have hxy : ‖x + y‖ ≤ (√(1 + η + ε) + √ε) * √dd := by
    calc ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
      _ ≤ √(1 + η + ε) * √dd + √ε * √dd := add_le_add hx' hy'
      _ = (√(1 + η + ε) + √ε) * √dd := by ring
  calc ‖x + y‖ ^ 2 ≤ ((√(1 + η + ε) + √ε) * √dd) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxy 2
    _ = (√(1 + η + ε) + √ε) ^ 2 * dd := by rw [mul_pow, Real.sq_sqrt hdd]

/- English proof (translation)
Introduce `hEI τ Rw I H H₁ _ _ _ _ _ X Pg S hN hG`. Establish `hN' : ‖X.part S‖ ^ 2 = (∑ i, ∑ j, X.GG i j * inner ℂ (X.vecPart S i) (X.vecPart S j)).re` using `hN`. Establish `h` using `hEI I H₁ X.GG (Pg * X.Gam1) (X.vecPart S) hG`. Use `show ‖X.part S‖ ^ 2 ≤ Pg * (X.Gam1 * ∑ i, ‖X.vecPart S i‖ ^ 2)`. Rewrite using `[hN']`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem t_PriceOfIota : NormSqBoundOfEqualIota := by
  intro hEI τ Rw I H H₁ _ _ _ _ _ X Pg S hN hG
  have hN' : ‖X.part S‖ ^ 2 =
      (∑ i, ∑ j, X.GG i j * inner ℂ (X.vecPart S i) (X.vecPart S j)).re := hN
  have h := hEI I H₁ X.GG (Pg * X.Gam1) (X.vecPart S) hG
  show ‖X.part S‖ ^ 2 ≤ Pg * (X.Gam1 * ∑ i, ‖X.vecPart S i‖ ^ 2)
  rw [hN']
  calc _ ≤ (Pg * X.Gam1) * ∑ i, ‖X.vecPart S i‖ ^ 2 := h
    _ = Pg * (X.Gam1 * ∑ i, ‖X.vecPart S i‖ ^ 2) := by ring

/- English proof (translation)
Introduce `hSF τ Rw I H H₁ _ _ _ _ _ X ε dd hA hL`. Establish `hL' : X.pairAbs (X.big X.nzSet ∪ X.nsc X.genSet) ≤ ε * dd` using `hL`. Prove the components needed by the constructor for the conclusion. Use `show X.pairAbs (X.big X.nzSet) ≤ ε * dd`. Conclude with `((hSF τ Rw I H H₁ X hA _ _ Set.subset_union_left).1).trans hL'`.

Use `show X.pairAbs (X.nsc X.genSet) ≤ ε * dd`. Conclude with `((hSF τ Rw I H H₁ X hA _ _ Set.subset_union_right).1).trans hL'`.
-/
theorem t_LoopsGiveRows : LoopsGiveRows := by
  intro hSF τ Rw I H H₁ _ _ _ _ _ X ε dd hA hL
  have hL' : X.pairAbs (X.big X.nzSet ∪ X.nsc X.genSet) ≤ ε * dd := hL
  constructor
  · show X.pairAbs (X.big X.nzSet) ≤ ε * dd
    exact ((hSF τ Rw I H H₁ X hA _ _ Set.subset_union_left).1).trans hL'
  · show X.pairAbs (X.nsc X.genSet) ≤ ε * dd
    exact ((hSF τ Rw I H H₁ X hA _ _ Set.subset_union_right).1).trans hL'

end Hil1

section Hil2

open Formalism.FourierDecayAlt.PB Finset

section
variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Terms τ Rw I H H₁)

/- English proof (translation)
Establish `hA' : Summable (fun t => ‖X.op t‖) ∧ Summable (fun t => ‖X.vec t‖) ∧ 0 < X.Gam1` using `hA`. Establish `h2` using `Summable.mul_of_nonneg hA'.2.1 hA'.2.1 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)`. Conclude with `Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => norm_inner_le_norm _ _) h2`.
-/
theorem summable_abs (hA : X.AbsConv) :
    Summable (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) := by
  have hA' : Summable (fun t => ‖X.op t‖) ∧ Summable (fun t => ‖X.vec t‖) ∧ 0 < X.Gam1 := hA
  have h2 := Summable.mul_of_nonneg hA'.2.1 hA'.2.1 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => norm_inner_le_norm _ _) h2

end

/- English proof (translation)
Introduce `τ Rw I H H₁ _ _ _ _ _ X hA Q Q' hQ`. Establish `hA' : Summable (fun t => ‖X.op t‖) ∧ Summable (fun t => ‖X.vec t‖) ∧ 0 < X.Gam1` using `hA`. Establish `hs` using `summable_abs X hA`. Establish `hG` using `hA'.2.2.le`. Establish `hb : ∀ p, ‖Q.indicator (fun p : τ × τ => (inner ℂ (X.vec p.1) (X.vec p.2)).re) p‖ ≤ Q.indicator (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) p`.

Introduce `p`. Distinguish the cases in `hp : p ∈ Q`. Rewrite using `[Set.indicator_of_mem hp, Set.indicator_of_mem hp, Real.norm_eq_abs] first`. Consider the case `exact Complex.abs_re_le_norm _`. Consider the case `exact Complex.abs_re_le_abs _`.

Consider the case `exact RCLike.abs_re_le_norm _`. Use `first`. Consider the case `rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]`. Consider the case `rw [Set.indicator_of_not_mem hp, Set.indicator_of_not_mem hp]`. Simplify using the standard rewrite rules.

Establish `hsr : Summable (fun p : τ × τ => ‖Q.indicator (fun p : τ × τ => (inner ℂ (X.vec p.1) (X.vec p.2)).re) p‖)` using `Summable.of_nonneg_of_le (fun p => norm_nonneg _) hb (hs.indicator Q)`. Prove the components needed by the constructor for the conclusion. Use `show X.Gam1 * _ ≤ X.Gam1 * _`. Use `mul_le_mul_of_nonneg_left ?_ hG` and prove the remaining obligations. Establish `hle : ∀ p, Q.indicator (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) p ≤ Q'.indicator (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) p` using `fun p => Set.indicator_le_indicator_of_subset hQ (fun _ => norm_nonneg _) p`.

Use `first`. Consider the case `exact Summable.tsum_le_tsum hle (hs.indicator Q) (hs.indicator Q')`. Consider the case `exact tsum_le_tsum hle (hs.indicator Q) (hs.indicator Q')`. Use `show |X.Gam1 * _| ≤ X.Gam1 * _`. Rewrite using `[abs_mul, abs_of_pos hA'.2.2]`.

Use `mul_le_mul_of_nonneg_left ?_ hG` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Consider the case `exact Summable.tsum_le_tsum hb hsr (hs.indicator Q)`. Consider the case `exact tsum_le_tsum hb hsr (hs.indicator Q)`.
-/
theorem t_SubFamily : SubFamily := by
  intro τ Rw I H H₁ _ _ _ _ _ X hA Q Q' hQ
  have hA' : Summable (fun t => ‖X.op t‖) ∧ Summable (fun t => ‖X.vec t‖) ∧ 0 < X.Gam1 := hA
  have hs := summable_abs X hA
  have hG := hA'.2.2.le
  have hb : ∀ p, ‖Q.indicator (fun p : τ × τ => (inner ℂ (X.vec p.1) (X.vec p.2)).re) p‖ ≤
      Q.indicator (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) p := by
    intro p
    by_cases hp : p ∈ Q
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Real.norm_eq_abs]
      first
          | exact Complex.abs_re_le_norm _
          | exact Complex.abs_re_le_abs _
          | exact RCLike.abs_re_le_norm _
    · first
        | rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]
        | rw [Set.indicator_of_not_mem hp, Set.indicator_of_not_mem hp]
      simp
  have hsr : Summable (fun p : τ × τ =>
      ‖Q.indicator (fun p : τ × τ => (inner ℂ (X.vec p.1) (X.vec p.2)).re) p‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) hb (hs.indicator Q)
  constructor
  · show X.Gam1 * _ ≤ X.Gam1 * _
    refine mul_le_mul_of_nonneg_left ?_ hG
    have hle : ∀ p, Q.indicator (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) p ≤
        Q'.indicator (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) p :=
      fun p => Set.indicator_le_indicator_of_subset hQ (fun _ => norm_nonneg _) p
    first
      | exact Summable.tsum_le_tsum hle (hs.indicator Q) (hs.indicator Q')
      | exact tsum_le_tsum hle (hs.indicator Q) (hs.indicator Q')
  · show |X.Gam1 * _| ≤ X.Gam1 * _
    rw [abs_mul, abs_of_pos hA'.2.2]
    refine mul_le_mul_of_nonneg_left ?_ hG
    calc |∑' p, Q.indicator (fun p : τ × τ => (inner ℂ (X.vec p.1) (X.vec p.2)).re) p|
        = ‖∑' p, Q.indicator (fun p : τ × τ => (inner ℂ (X.vec p.1) (X.vec p.2)).re) p‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∑' p, ‖Q.indicator (fun p : τ × τ => (inner ℂ (X.vec p.1) (X.vec p.2)).re) p‖ :=
          norm_tsum_le_tsum_norm hsr
      _ ≤ ∑' p, Q.indicator (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) p := by
          first
            | exact Summable.tsum_le_tsum hb hsr (hs.indicator Q)
            | exact tsum_le_tsum hb hsr (hs.indicator Q)

/- English proof (translation)
Introduce `hPI hEI hPS hSF τ Rw I H H₁ _ _ _ _ _ _ X Pg A ε ε' dd hPg hdd hA hNX hGG hRO hCP hIZ hRB hRNS hRM hRNG`. Take `⟨-, hgen, hng⟩` from `hPS τ Rw I H H₁ X hA hRO hCP`. Establish `hsubN : X.big X.ngSet ⊆ X.big X.nzSet`. Introduce `p hp`. Establish `hp' : (p.1 ∈ X.ngSet ∧ p.2 ∈ X.ngSet ∧ X.rowOf p.1 = X.rowOf p.2) ∧ 2 ≤ X.s0 p.1 p.2` using `hp`.

Establish `h1 : p.1 ∈ X.nzSet` using `(show X.G p.1 ≠ 0 ∧ ¬ X.gener p.1 from hp'.1.1).1`. Establish `h2 : p.2 ∈ X.nzSet` using `(show X.G p.2 ≠ 0 ∧ ¬ X.gener p.2 from hp'.1.2.1).1`. Use `show (p.1 ∈ X.nzSet ∧ p.2 ∈ X.nzSet ∧ X.rowOf p.1 = X.rowOf p.2) ∧ 2 ≤ X.s0 p.1 p.2`. Conclude with `⟨⟨h1, h2, hp'.1.2.2⟩, hp'.2⟩`. Take `⟨hmN, -⟩` from `hSF τ Rw I H H₁ X hA _ _ hsubN`.

Take `⟨-, habsN⟩` from `hSF τ Rw I H H₁ X hA _ _ (subset_rfl : X.big X.ngSet ⊆ X.big X.ngSet)`. Establish `hRB' : X.pairAbs (X.big X.nzSet) ≤ ε * dd` using `hRB`. Establish `hRNG' : X.pairSum (X.one X.ngSet) ≤ ε' * dd` using `hRNG`. Establish `hPhiN : X.PhiEq X.ngSet ≤ (ε + ε') * dd`. Rewrite using `[hng]`.

Use `le_abs_self (X.pairSum (X.big X.ngSet))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hRNS' : X.pairAbs (X.nsc X.genSet) ≤ ε * dd` using `hRNS`. Establish `hRM' : X.pairSum (X.sc X.genSet) ≤ A * dd` using `hRM`. Establish `hsub : X.big X.genSet ⊆ X.big X.nzSet`.

Introduce `p hp`. Establish `hp' : (p.1 ∈ X.genSet ∧ p.2 ∈ X.genSet ∧ X.rowOf p.1 = X.rowOf p.2) ∧ 2 ≤ X.s0 p.1 p.2` using `hp`. Establish `h1 : p.1 ∈ X.nzSet` using `(show X.G p.1 ≠ 0 ∧ X.gener p.1 from hp'.1.1).1`. Establish `h2 : p.2 ∈ X.nzSet` using `(show X.G p.2 ≠ 0 ∧ X.gener p.2 from hp'.1.2.1).1`. Use `show (p.1 ∈ X.nzSet ∧ p.2 ∈ X.nzSet ∧ X.rowOf p.1 = X.rowOf p.2) ∧ 2 ≤ X.s0 p.1 p.2`.

Conclude with `⟨⟨h1, h2, hp'.1.2.2⟩, hp'.2⟩`. Take `⟨hm, -⟩` from `hSF τ Rw I H H₁ X hA _ _ hsub`. Take `⟨-, habs1⟩` from `hSF τ Rw I H H₁ X hA _ _ (subset_rfl : X.big X.genSet ⊆ X.big X.genSet)`. Take `⟨-, habs2⟩` from `hSF τ Rw I H H₁ X hA _ _ (subset_rfl : X.nsc X.genSet ⊆ X.nsc X.genSet)`. Establish `hPhiG : X.PhiEq X.genSet ≤ (A + 2 * ε) * dd`.

Rewrite using `[hgen]`. Use `le_abs_self (X.pairSum (X.big X.genSet))` as an intermediate fact. Use `le_abs_self (X.pairSum (X.nsc X.genSet))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx : ‖X.part X.genSet‖ ^ 2 ≤ (Pg * (A + 2 * ε)) * dd`.

Use `hPI hEI τ Rw I H H₁ X Pg X.genSet hNX.1 hGG` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `hy : ‖X.part X.ngSet‖ ^ 2 ≤ (Pg * (ε + ε')) * dd`. Use `hPI hEI τ Rw I H H₁ X Pg X.ngSet hNX.2 hGG` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.

Establish `hIZ' : X.part X.idSet = 0` using `hIZ`. Use `show ‖X.part X.idSet + X.part X.genSet + X.part X.ngSet‖ ^ 2 ≤ _`. Rewrite using `[hIZ', zero_add]`. Establish `e : 1 + (Pg * (A + 2 * ε) - 1 - Pg * (ε + ε')) + Pg * (ε + ε') = Pg * (A + 2 * ε)` using `by ring`. Establish `hTC` using `t_TextClosing H (X.part X.genSet) (X.part X.ngSet) (Pg * (A + 2 * ε) - 1 - Pg * (ε + ε')) (Pg * (ε + ε')) dd hdd (by rw [e]; exact hx) hy`.

Rewrite `hTC` using `[e]`. Conclude with `hTC`.
-/
theorem t_PairBoundAbstract : PairBoundAbstract := by
  intro hPI hEI hPS hSF τ Rw I H H₁ _ _ _ _ _ _ X Pg A ε ε' dd hPg hdd hA hNX hGG hRO hCP hIZ
    hRB hRNS hRM hRNG
  obtain ⟨-, hgen, hng⟩ := hPS τ Rw I H H₁ X hA hRO hCP
  have hsubN : X.big X.ngSet ⊆ X.big X.nzSet := by
    intro p hp
    have hp' : (p.1 ∈ X.ngSet ∧ p.2 ∈ X.ngSet ∧ X.rowOf p.1 = X.rowOf p.2) ∧ 2 ≤ X.s0 p.1 p.2 := hp
    have h1 : p.1 ∈ X.nzSet := (show X.G p.1 ≠ 0 ∧ ¬ X.gener p.1 from hp'.1.1).1
    have h2 : p.2 ∈ X.nzSet := (show X.G p.2 ≠ 0 ∧ ¬ X.gener p.2 from hp'.1.2.1).1
    show (p.1 ∈ X.nzSet ∧ p.2 ∈ X.nzSet ∧ X.rowOf p.1 = X.rowOf p.2) ∧ 2 ≤ X.s0 p.1 p.2
    exact ⟨⟨h1, h2, hp'.1.2.2⟩, hp'.2⟩
  obtain ⟨hmN, -⟩ := hSF τ Rw I H H₁ X hA _ _ hsubN
  obtain ⟨-, habsN⟩ := hSF τ Rw I H H₁ X hA _ _ (subset_rfl : X.big X.ngSet ⊆ X.big X.ngSet)
  have hRB' : X.pairAbs (X.big X.nzSet) ≤ ε * dd := hRB
  have hRNG' : X.pairSum (X.one X.ngSet) ≤ ε' * dd := hRNG
  have hPhiN : X.PhiEq X.ngSet ≤ (ε + ε') * dd := by
    rw [hng]
    have := le_abs_self (X.pairSum (X.big X.ngSet))
    linarith
  have hRNS' : X.pairAbs (X.nsc X.genSet) ≤ ε * dd := hRNS
  have hRM' : X.pairSum (X.sc X.genSet) ≤ A * dd := hRM
  have hsub : X.big X.genSet ⊆ X.big X.nzSet := by
    intro p hp
    have hp' : (p.1 ∈ X.genSet ∧ p.2 ∈ X.genSet ∧ X.rowOf p.1 = X.rowOf p.2) ∧ 2 ≤ X.s0 p.1 p.2 := hp
    have h1 : p.1 ∈ X.nzSet := (show X.G p.1 ≠ 0 ∧ X.gener p.1 from hp'.1.1).1
    have h2 : p.2 ∈ X.nzSet := (show X.G p.2 ≠ 0 ∧ X.gener p.2 from hp'.1.2.1).1
    show (p.1 ∈ X.nzSet ∧ p.2 ∈ X.nzSet ∧ X.rowOf p.1 = X.rowOf p.2) ∧ 2 ≤ X.s0 p.1 p.2
    exact ⟨⟨h1, h2, hp'.1.2.2⟩, hp'.2⟩
  obtain ⟨hm, -⟩ := hSF τ Rw I H H₁ X hA _ _ hsub
  obtain ⟨-, habs1⟩ := hSF τ Rw I H H₁ X hA _ _ (subset_rfl : X.big X.genSet ⊆ X.big X.genSet)
  obtain ⟨-, habs2⟩ := hSF τ Rw I H H₁ X hA _ _ (subset_rfl : X.nsc X.genSet ⊆ X.nsc X.genSet)
  have hPhiG : X.PhiEq X.genSet ≤ (A + 2 * ε) * dd := by
    rw [hgen]
    have := le_abs_self (X.pairSum (X.big X.genSet))
    have := le_abs_self (X.pairSum (X.nsc X.genSet))
    linarith
  have hx : ‖X.part X.genSet‖ ^ 2 ≤ (Pg * (A + 2 * ε)) * dd := by
    have := hPI hEI τ Rw I H H₁ X Pg X.genSet hNX.1 hGG
    calc _ ≤ Pg * X.PhiEq X.genSet := this
      _ ≤ Pg * ((A + 2 * ε) * dd) := mul_le_mul_of_nonneg_left hPhiG hPg
      _ = _ := by ring
  have hy : ‖X.part X.ngSet‖ ^ 2 ≤ (Pg * (ε + ε')) * dd := by
    have := hPI hEI τ Rw I H H₁ X Pg X.ngSet hNX.2 hGG
    calc _ ≤ Pg * X.PhiEq X.ngSet := this
      _ ≤ Pg * ((ε + ε') * dd) := mul_le_mul_of_nonneg_left hPhiN hPg
      _ = _ := by ring
  have hIZ' : X.part X.idSet = 0 := hIZ
  show ‖X.part X.idSet + X.part X.genSet + X.part X.ngSet‖ ^ 2 ≤ _
  rw [hIZ', zero_add]
  have e : 1 + (Pg * (A + 2 * ε) - 1 - Pg * (ε + ε')) + Pg * (ε + ε') = Pg * (A + 2 * ε) := by ring
  have hTC := t_TextClosing H (X.part X.genSet) (X.part X.ngSet)
    (Pg * (A + 2 * ε) - 1 - Pg * (ε + ε')) (Pg * (ε + ε')) dd hdd (by rw [e]; exact hx) hy
  rw [e] at hTC
  exact hTC

end Hil2

section Hil3

open Formalism.FourierDecayAlt.PB Finset

/- English proof (translation)
Introduce `hPBA hPI hEI hPS hSF hNP hNE hND hNL hNN hNGE hEZ τ Rw I H H₁ _ _ _ _ _ _ X k r f b g1 g2 c Cn δ e1 dd hSN hdd hδ0 hδ he0 he1 hAC hNX hGG hRO hCP hIZ hRB hRNS hRM hRNG`. Take `⟨hb, hk32, hfk, hr, hg1, hg2, hlb, hc, hCn⟩` from `hSN`. Establish `hb1 : (1:ℝ) ≤ b` using `by linarith`. Establish `hk1 : 1 ≤ k` using `by omega`. Take `⟨-, -, hPg0, hPg⟩` from `hNP f k b g1 g2 hb1 hk1 hfk hg1 hg2`.

Establish `hE` using `hNE k b (by linarith) hlb`. Take `⟨hD1, hD2⟩` from `hND k r f hfk hk32 hr`. Establish `hL` using `hNL k f c hc`. Establish `hG` using `hNGE k r (by omega)`. Establish `hN` using `hNN k (2 * r + 2) f Cn b hCn`.

Establish `hε' : ((2 : ℝ) ^ (k - 2 * r - 5))⁻¹ * Real.exp (Cn * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b) ≤ (b ^ 14)⁻¹` using `(mul_le_mul_of_nonneg_right hG (Real.exp_pos _).le).trans (hN.trans hE)`. Establish `he1' : e1 ≤ Real.exp ((b ^ 14)⁻¹)` using `he1.trans (Real.exp_le_exp.mpr ((hD1.trans hD2).trans hE))`. Establish `hb7 : (0:ℝ) ≤ (b ^ 7)⁻¹` using `inv_nonneg.mpr (pow_nonneg (by linarith) 7)`. Establish `hA : (1 + δ) * e1 ≤ (1 + (b ^ 7)⁻¹) * Real.exp ((b ^ 14)⁻¹)` using `mul_le_mul (by linarith) he1' he0 (by linarith)`. Establish `hmain` using `hPBA hPI hEI hPS hSF τ Rw I H H₁ X ((1 + 3 / g1) ^ f * (1 + 3 / g2) ^ f) ((1 + δ) * e1) (Real.exp (-(c * k * f * Real.log k))) (((2 : ℝ) ^ (k - 2 * r - 5))⁻¹ * Real.exp (Cn * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b)) dd hPg0 hdd hAC hNX hGG hRO hCP hIZ hRB hRNS hRM hRNG`.

Establish `hfin` using `hEZ b _ _ _ _ hb hPg0 hPg hA (hL.trans hE) hε'`. Conclude with `hmain.trans (mul_le_mul_of_nonneg_right hfin hdd)`.
-/
theorem t_PairBound : PairBound := by
  intro hPBA hPI hEI hPS hSF hNP hNE hND hNL hNN hNGE hEZ τ Rw I H H₁ _ _ _ _ _ _ X k r f b g1 g2 c Cn
    δ e1 dd hSN hdd hδ0 hδ he0 he1 hAC hNX hGG hRO hCP hIZ hRB hRNS hRM hRNG
  obtain ⟨hb, hk32, hfk, hr, hg1, hg2, hlb, hc, hCn⟩ := hSN
  have hb1 : (1:ℝ) ≤ b := by linarith
  have hk1 : 1 ≤ k := by omega
  obtain ⟨-, -, hPg0, hPg⟩ := hNP f k b g1 g2 hb1 hk1 hfk hg1 hg2
  have hE := hNE k b (by linarith) hlb
  obtain ⟨hD1, hD2⟩ := hND k r f hfk hk32 hr
  have hL := hNL k f c hc
  have hG := hNGE k r (by omega)
  have hN := hNN k (2 * r + 2) f Cn b hCn
  have hε' : ((2 : ℝ) ^ (k - 2 * r - 5))⁻¹ *
      Real.exp (Cn * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b) ≤ (b ^ 14)⁻¹ :=
    (mul_le_mul_of_nonneg_right hG (Real.exp_pos _).le).trans (hN.trans hE)
  have he1' : e1 ≤ Real.exp ((b ^ 14)⁻¹) :=
    he1.trans (Real.exp_le_exp.mpr ((hD1.trans hD2).trans hE))
  have hb7 : (0:ℝ) ≤ (b ^ 7)⁻¹ := inv_nonneg.mpr (pow_nonneg (by linarith) 7)
  have hA : (1 + δ) * e1 ≤ (1 + (b ^ 7)⁻¹) * Real.exp ((b ^ 14)⁻¹) :=
    mul_le_mul (by linarith) he1' he0 (by linarith)
  have hmain := hPBA hPI hEI hPS hSF τ Rw I H H₁ X ((1 + 3 / g1) ^ f * (1 + 3 / g2) ^ f)
    ((1 + δ) * e1) (Real.exp (-(c * k * f * Real.log k)))
    (((2 : ℝ) ^ (k - 2 * r - 5))⁻¹ * Real.exp (Cn * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b)) dd
    hPg0 hdd hAC hNX hGG hRO hCP hIZ hRB hRNS hRM hRNG
  have hfin := hEZ b _ _ _ _ hb hPg0 hPg hA (hL.trans hE) hε'
  exact hmain.trans (mul_le_mul_of_nonneg_right hfin hdd)

end Hil3

section Hil4

open Formalism.FourierDecayAlt.PB Finset
open Classical
open scoped ComplexOrder

/- English proof (translation)
Introduce `τ Rw I H H₁ _ _ _ _ _ _ X hA hD`. Establish `hA' : Summable (fun t => ‖X.op t‖) ∧ Summable (fun t => ‖X.vec t‖) ∧ 0 < X.Gam1` using `hA`. Establish `hs : Summable X.op` using `Summable.of_norm hA'.1`. Establish `hsI : ∀ S : Set τ, Summable (S.indicator X.op)` using `fun S => hs.indicator S`. Establish `hpt : ∀ t, X.op t = X.idSet.indicator X.op t + X.genSet.indicator X.op t + X.ngSet.indicator X.op t + X.degSet.indicator X.op t`.

Introduce `t`. Distinguish the cases in `h1 : X.isId t`. Establish `m1 : t ∈ X.idSet` using `h1`. Establish `m2 : t ∉ X.genSet` using `fun h => (show X.G t ≠ 0 ∧ X.gener t from h).1 (hD t h1)`. Establish `m3 : t ∉ X.ngSet` using `fun h => (show X.G t ≠ 0 ∧ ¬ X.gener t from h).1 (hD t h1)`.

Establish `m4 : t ∉ X.degSet` using `fun h => (show X.G t = 0 ∧ ¬ X.isId t from h).2 h1`. Simplify using `[Set.indicator_apply, m1, m2, m3, m4]`. Distinguish the cases in `h2 : X.G t = 0`. Establish `m1 : t ∉ X.idSet` using `h1`. Establish `m2 : t ∉ X.genSet` using `fun h => (show X.G t ≠ 0 ∧ X.gener t from h).1 h2`.

Establish `m3 : t ∉ X.ngSet` using `fun h => (show X.G t ≠ 0 ∧ ¬ X.gener t from h).1 h2`. Establish `m4 : t ∈ X.degSet` using `⟨h2, h1⟩`. Simplify using `[Set.indicator_apply, m1, m2, m3, m4]`. Distinguish the cases in `h3 : X.gener t`. Establish `m1 : t ∉ X.idSet` using `h1`.

Establish `m2 : t ∈ X.genSet` using `⟨h2, h3⟩`. Establish `m3 : t ∉ X.ngSet` using `fun h => (show X.G t ≠ 0 ∧ ¬ X.gener t from h).2 h3`. Establish `m4 : t ∉ X.degSet` using `fun h => h2 (show X.G t = 0 ∧ ¬ X.isId t from h).1`. Simplify using `[Set.indicator_apply, m1, m2, m3, m4]`. Establish `m1 : t ∉ X.idSet` using `h1`.

Establish `m2 : t ∉ X.genSet` using `fun h => h3 (show X.G t ≠ 0 ∧ X.gener t from h).2`. Establish `m3 : t ∈ X.ngSet` using `⟨h2, h3⟩`. Establish `m4 : t ∉ X.degSet` using `fun h => h2 (show X.G t = 0 ∧ ¬ X.isId t from h).1`. Simplify using `[Set.indicator_apply, m1, m2, m3, m4]`. Use `show ∑' t, X.op t = (∑' t, X.idSet.indicator X.op t + ∑' t, X.genSet.indicator X.op t + ∑' t, X.ngSet.indicator X.op t) + ∑' t, X.degSet.indicator X.op t`.

Establish `e1 : ∑' t, X.op t = ∑' t, (X.idSet.indicator X.op t + X.genSet.indicator X.op t + X.ngSet.indicator X.op t + X.degSet.indicator X.op t)` using `tsum_congr hpt`. Rewrite using `[e1]`. Use `first`. Consider the case `rw [Summable.tsum_add (((hsI _).add (hsI _)).add (hsI _)) (hsI _), Summable.tsum_add ((hsI _).add (hsI _)) (hsI _), Summable.tsum_add (hsI _) (hsI _)]`. Consider the case `rw [tsum_add (((hsI _).add (hsI _)).add (hsI _)) (hsI _), tsum_add ((hsI _).add (hsI _)) (hsI _), tsum_add (hsI _) (hsI _)]`.
-/
theorem t_SplitSum : SplitSum := by
  intro τ Rw I H H₁ _ _ _ _ _ _ X hA hD
  have hA' : Summable (fun t => ‖X.op t‖) ∧ Summable (fun t => ‖X.vec t‖) ∧ 0 < X.Gam1 := hA
  have hs : Summable X.op := Summable.of_norm hA'.1
  have hsI : ∀ S : Set τ, Summable (S.indicator X.op) := fun S => hs.indicator S
  have hpt : ∀ t, X.op t = X.idSet.indicator X.op t + X.genSet.indicator X.op t +
      X.ngSet.indicator X.op t + X.degSet.indicator X.op t := by
    intro t
    by_cases h1 : X.isId t
    · have m1 : t ∈ X.idSet := h1
      have m2 : t ∉ X.genSet := fun h => (show X.G t ≠ 0 ∧ X.gener t from h).1 (hD t h1)
      have m3 : t ∉ X.ngSet := fun h => (show X.G t ≠ 0 ∧ ¬ X.gener t from h).1 (hD t h1)
      have m4 : t ∉ X.degSet := fun h => (show X.G t = 0 ∧ ¬ X.isId t from h).2 h1
      simp [Set.indicator_apply, m1, m2, m3, m4]
    · by_cases h2 : X.G t = 0
      · have m1 : t ∉ X.idSet := h1
        have m2 : t ∉ X.genSet := fun h => (show X.G t ≠ 0 ∧ X.gener t from h).1 h2
        have m3 : t ∉ X.ngSet := fun h => (show X.G t ≠ 0 ∧ ¬ X.gener t from h).1 h2
        have m4 : t ∈ X.degSet := ⟨h2, h1⟩
        simp [Set.indicator_apply, m1, m2, m3, m4]
      · by_cases h3 : X.gener t
        · have m1 : t ∉ X.idSet := h1
          have m2 : t ∈ X.genSet := ⟨h2, h3⟩
          have m3 : t ∉ X.ngSet := fun h => (show X.G t ≠ 0 ∧ ¬ X.gener t from h).2 h3
          have m4 : t ∉ X.degSet := fun h => h2 (show X.G t = 0 ∧ ¬ X.isId t from h).1
          simp [Set.indicator_apply, m1, m2, m3, m4]
        · have m1 : t ∉ X.idSet := h1
          have m2 : t ∉ X.genSet := fun h => h3 (show X.G t ≠ 0 ∧ X.gener t from h).2
          have m3 : t ∈ X.ngSet := ⟨h2, h3⟩
          have m4 : t ∉ X.degSet := fun h => h2 (show X.G t = 0 ∧ ¬ X.isId t from h).1
          simp [Set.indicator_apply, m1, m2, m3, m4]
  show ∑' t, X.op t = (∑' t, X.idSet.indicator X.op t + ∑' t, X.genSet.indicator X.op t +
    ∑' t, X.ngSet.indicator X.op t) + ∑' t, X.degSet.indicator X.op t
  have e1 : ∑' t, X.op t = ∑' t, (X.idSet.indicator X.op t + X.genSet.indicator X.op t +
      X.ngSet.indicator X.op t + X.degSet.indicator X.op t) := tsum_congr hpt
  rw [e1]
  first
    | rw [Summable.tsum_add (((hsI _).add (hsI _)).add (hsI _)) (hsI _),
        Summable.tsum_add ((hsI _).add (hsI _)) (hsI _), Summable.tsum_add (hsI _) (hsI _)]
    | rw [tsum_add (((hsI _).add (hsI _)).add (hsI _)) (hsI _),
        tsum_add ((hsI _).add (hsI _)) (hsI _), tsum_add (hsI _) (hsI _)]

/- English proof (translation)
Introduce `I H₁ _ _ _ Γ c a hM`. Take `⟨m, v, hv0⟩` from `Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hM`. Establish `hM' : ∀ i j, ((c : ℂ) • (1 : Matrix I I ℂ) - Matrix.of Γ) i j = ∑ l, v l i * star (v l j)`. Introduce `i j`. Rewrite using `[hv0]`.

Simplify using `[Matrix.sum_apply, Matrix.vecMulVec_apply]`. Establish `hw : ∀ l, inner ℂ (∑ i, star (v l i) • a i) (∑ i, star (v l i) • a i) = ∑ i, ∑ j, v l i * star (v l j) * inner ℂ (a i) (a j)`. Introduce `l`. Simplify using `only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, starRingEnd_apply, star_star, Finset.mul_sum, mul_assoc]`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))`. Establish `hsum : ∑ i, ∑ j, ((c : ℂ) • (1 : Matrix I I ℂ) - Matrix.of Γ) i j * inner ℂ (a i) (a j) = ∑ l, inner ℂ (∑ i, star (v l i) • a i) (∑ i, star (v l i) • a i)`. Repeatedly rewrite using `[hw, hM', Finset.sum_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hnn : 0 ≤ (∑ l, inner ℂ (∑ i, star (v l i) • a i) (∑ i, star (v l i) • a i)).re`.

Rewrite using `[Complex.re_sum]`. Use `Finset.sum_nonneg (fun l _ => ?_)` and prove the remaining obligations. Use `inner_self_nonneg (𝕜 := ℂ) (x := ∑ i, star (v l i) • a i)` as an intermediate fact. Simplify using `using this`. Establish `hsplit : ∑ i, ∑ j, ((c : ℂ) • (1 : Matrix I I ℂ) - Matrix.of Γ) i j * inner ℂ (a i) (a j) = (c : ℂ) * ∑ i, inner ℂ (a i) (a i) - ∑ i, ∑ j, Γ i j * inner ℂ (a i) (a j)`.

Simplify using `[Matrix.sub_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, ite_mul]`. Establish `hre : ((c : ℂ) * ∑ i, inner ℂ (a i) (a i)).re = c * ∑ i, ‖a i‖ ^ 2`. Rewrite using `[Complex.re_ofReal_mul, Complex.re_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Conclude with `inner_self_eq_norm_sq (𝕜 := ℂ) (a i)`. Rewrite `hsplit` using `[hsum]`. Establish `htot` using `congrArg Complex.re hsplit`. Rewrite `htot` using `[Complex.sub_re, hre]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem t_EqualIota : GramSumLeOfPosSemidef := by
  intro I H₁ _ _ _ Γ c a hM
  obtain ⟨m, v, hv0⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hM
  have hM' : ∀ i j, ((c : ℂ) • (1 : Matrix I I ℂ) - Matrix.of Γ) i j = ∑ l, v l i * star (v l j) := by
    intro i j
    rw [hv0]
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply]
  have hw : ∀ l, inner ℂ (∑ i, star (v l i) • a i) (∑ i, star (v l i) • a i) =
      ∑ i, ∑ j, v l i * star (v l j) * inner ℂ (a i) (a j) := by
    intro l
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, starRingEnd_apply,
      star_star, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hsum : ∑ i, ∑ j, ((c : ℂ) • (1 : Matrix I I ℂ) - Matrix.of Γ) i j * inner ℂ (a i) (a j) =
      ∑ l, inner ℂ (∑ i, star (v l i) • a i) (∑ i, star (v l i) • a i) := by
    simp_rw [hw, hM', Finset.sum_mul]
    calc ∑ i, ∑ j, ∑ l, v l i * star (v l j) * inner ℂ (a i) (a j)
        = ∑ i, ∑ l, ∑ j, v l i * star (v l j) * inner ℂ (a i) (a j) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ l, ∑ i, ∑ j, v l i * star (v l j) * inner ℂ (a i) (a j) := Finset.sum_comm
  have hnn : 0 ≤ (∑ l, inner ℂ (∑ i, star (v l i) • a i) (∑ i, star (v l i) • a i)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_nonneg (fun l _ => ?_)
    have := inner_self_nonneg (𝕜 := ℂ) (x := ∑ i, star (v l i) • a i)
    simpa using this
  have hsplit : ∑ i, ∑ j, ((c : ℂ) • (1 : Matrix I I ℂ) - Matrix.of Γ) i j * inner ℂ (a i) (a j) =
      (c : ℂ) * ∑ i, inner ℂ (a i) (a i) - ∑ i, ∑ j, Γ i j * inner ℂ (a i) (a j) := by
    simp [Matrix.sub_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, ite_mul]
  have hre : ((c : ℂ) * ∑ i, inner ℂ (a i) (a i)).re = c * ∑ i, ‖a i‖ ^ 2 := by
    rw [Complex.re_ofReal_mul, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (a i)
  rw [hsum] at hsplit
  have htot := congrArg Complex.re hsplit
  rw [Complex.sub_re, hre] at htot
  linarith

end Hil4

section Hil5

open Formalism.FourierDecayAlt.PB Finset
open Classical

section
variable {τ H₁ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]

noncomputable def reInner (w : H₁) : H₁ →+ ℝ :=
  AddMonoidHom.mk' (fun x => (inner ℂ w x).re) (by intro a b; simp)

/- English proof (translation)
Use `show Continuous (fun x => (inner ℂ w x).re)`. Conclude with `Complex.continuous_re.comp (continuous_const.inner continuous_id)`.
-/
theorem cont_reInner (w : H₁) : Continuous (reInner w) := by
  show Continuous (fun x => (inner ℂ w x).re)
  exact Complex.continuous_re.comp (continuous_const.inner continuous_id)

/- English proof (translation)
Conclude with `hf.map_tsum (reInner w) (cont_reInner w)`.
-/
theorem re_inner_tsum (f : τ → H₁) (hf : Summable f) (w : H₁) :
    (inner ℂ w (∑' t, f t)).re = ∑' t, (inner ℂ w (f t)).re := by
  exact hf.map_tsum (reInner w) (cont_reInner w)

/- English proof (translation)
Establish `h2` using `Summable.mul_of_nonneg hf hf (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)`. Use `Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) h2)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.norm_eq_abs]`. Use `first`.

Consider the case `exact Complex.abs_re_le_norm _`. Consider the case `exact Complex.abs_re_le_abs _`. Consider the case `exact RCLike.abs_re_le_norm _`. Use `_ ≤ ‖f p.1‖ * ‖f p.2‖ := norm_inner_le_norm _ _`.
-/
theorem summable_re (f : τ → H₁) (hf : Summable (fun t => ‖f t‖)) :
    Summable (fun p : τ × τ => (inner ℂ (f p.1) (f p.2)).re) := by
  have h2 := Summable.mul_of_nonneg hf hf (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) h2)
  calc ‖(inner ℂ (f p.1) (f p.2)).re‖ ≤ ‖inner ℂ (f p.1) (f p.2)‖ := by
        rw [Real.norm_eq_abs]
        first
          | exact Complex.abs_re_le_norm _
          | exact Complex.abs_re_le_abs _
          | exact RCLike.abs_re_le_norm _
    _ ≤ ‖f p.1‖ * ‖f p.2‖ := norm_inner_le_norm _ _

/- English proof (translation)
Establish `hs : Summable f` using `Summable.of_norm hf`. Establish `h1 : ‖∑' t, f t‖ ^ 2 = (inner ℂ (∑' t, f t) (∑' t, f t)).re` using `by first`. Consider the case `exact norm_sq_eq_re_inner (𝕜 := ℂ) _`. Consider the case `exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm`. Establish `h2 : ∀ b, (inner ℂ (∑' t, f t) (f b)).re = ∑' a, (inner ℂ (f b) (f a)).re`.

Introduce `b`. Rewrite using `[← inner_conj_symm, Complex.conj_re]`. Conclude with `re_inner_tsum f hs (f b)`. Rewrite using `[h1, re_inner_tsum f hs (∑' t, f t)]`. Repeatedly rewrite using `[h2]`.

Establish `hg` using `summable_re f hf`. Use `first`. Consider the case `exact (Summable.tsum_prod hg).symm`. Consider the case `exact (tsum_prod' hg (fun b => hg.prod_factor b)).symm`. Consider the case `exact (Summable.tsum_prod' hg (fun b => hg.prod_factor b)).symm`.
-/
theorem norm_sq_tsum [CompleteSpace H₁] (f : τ → H₁) (hf : Summable (fun t => ‖f t‖)) :
    ‖∑' t, f t‖ ^ 2 = ∑' p : τ × τ, (inner ℂ (f p.1) (f p.2)).re := by
  have hs : Summable f := Summable.of_norm hf
  have h1 : ‖∑' t, f t‖ ^ 2 = (inner ℂ (∑' t, f t) (∑' t, f t)).re := by
    first
      | exact norm_sq_eq_re_inner (𝕜 := ℂ) _
      | exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
  have h2 : ∀ b, (inner ℂ (∑' t, f t) (f b)).re = ∑' a, (inner ℂ (f b) (f a)).re := by
    intro b
    rw [← inner_conj_symm, Complex.conj_re]
    exact re_inner_tsum f hs (f b)
  rw [h1, re_inner_tsum f hs (∑' t, f t)]
  simp_rw [h2]
  have hg := summable_re f hf
  first
    | exact (Summable.tsum_prod hg).symm
    | exact (tsum_prod' hg (fun b => hg.prod_factor b)).symm
    | exact (Summable.tsum_prod' hg (fun b => hg.prod_factor b)).symm

end

/- English proof (translation)
Introduce `τ Rw I H H₁ _ _ _ _ _ _ X hA hO hS0`. Use `set Z : τ × τ → ℝ := fun p => (inner ℂ (X.vec p.1) (X.vec p.2)).re with hZdef`. Establish `hZ : Summable Z` using `summable_re X.vec hA.2.1`. Establish `c1 : ∀ S : Set τ, X.PhiEq S = X.pairSum (X.allPairs S)`. Introduce `S`.

Unfold `Terms.PhiEq Terms.pairSum`. Use `congr 1`. Establish `hi : ∀ i, ‖X.vecPart S i‖ ^ 2 = ∑' p : τ × τ, (if X.io (X.rowOf p.1) = i then (if p.1 ∈ S ∧ p.2 ∈ S ∧ X.io (X.rowOf p.2) = X.io (X.rowOf p.1) then Z p else 0) else 0)`. Introduce `i`. Unfold `Terms.vecPart`.

Rewrite using `[norm_sq_tsum]`. Apply `tsum_congr` to reduce the goal to its premises. Introduce `p`. Apply the tactic sequence `by_cases h1 : X.io (X.rowOf p.1) = i <;> by_cases h2 : X.io (X.rowOf p.2) = i <;>`. Apply the tactic sequence `by_cases h3 : p.1 ∈ S <;> by_cases h4 : p.2 ∈ S <;>`.

Simplify using `[Set.indicator, h1, h2, h3, h4, hZdef]`. Repeatedly rewrite using `[norm_indicator_eq_indicator_norm]`. Conclude with `hA.2.1.indicator _`. Repeatedly rewrite using `[hi]`. Rewrite using `[← Summable.tsum_finsetSum]`.

Apply `tsum_congr` to reduce the goal to its premises. Introduce `p`. Rewrite using `[Finset.sum_ite_eq]`. Simplify using `only [mem_univ, if_true]`. Apply the tactic sequence `by_cases h3 : p.1 ∈ S <;> by_cases h4 : p.2 ∈ S <;>`.

Apply the tactic sequence `by_cases h5 : X.rowOf p.1 = X.rowOf p.2 <;>`. Simplify using `[Set.indicator, Terms.allPairs, h3, h4, h5]`. Apply the tactic sequence `all_goals first`. Consider the case `rfl`. Consider the case `(intro h6`.

Use `hO p.1 p.2 h6.symm h5` as an intermediate fact. Simplify using `[hZdef, this])`. Introduce `i _`. Use `Summable.of_norm_bounded hZ.norm (fun p => ?_)` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.

Use `⟨c1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[c1]`. Unfold `Terms.pairSum`. Rewrite using `[← mul_add, ← mul_add, ← Summable.tsum_add (hZ.indicator _) (hZ.indicator _), ← Summable.tsum_add ((hZ.indicator _).add (hZ.indicator _)) (hZ.indicator _)]`. Use `congr 1`.

Apply `tsum_congr` to reduce the goal to its premises. Introduce `p`. Distinguish the cases in `h : p ∈ X.allPairs X.genSet`. Establish `h1 : 1 ≤ X.s0 p.1 p.2` using `hS0 p.1 p.2 h.2.2 h.1.1 h.2.1.1`. Distinguish the cases in `h2 : X.s0 p.1 p.2 = 1`.

Apply the tactic sequence `by_cases h3 : X.scal p.1 p.2 <;>`. Apply the tactic sequence `simp [Set.indicator, Terms.big, Terms.nsc, Terms.sc, h, h2, h3] <;> rfl`. Establish `h4 : 2 ≤ X.s0 p.1 p.2` using `by omega`. Simplify using `[Set.indicator, Terms.big, Terms.nsc, Terms.sc, h, h2, h4]`. Both sides reduce to the same expression.

Simplify using `[Set.indicator, Terms.big, Terms.nsc, Terms.sc, h]`. Rewrite using `[c1]`. Unfold `Terms.pairSum`. Rewrite using `[← mul_add, ← Summable.tsum_add (hZ.indicator _) (hZ.indicator _)]`. Use `congr 1`.

Apply `tsum_congr` to reduce the goal to its premises. Introduce `p`. Distinguish the cases in `h : p ∈ X.allPairs X.ngSet`. Establish `h1 : 1 ≤ X.s0 p.1 p.2` using `hS0 p.1 p.2 h.2.2 h.1.1 h.2.1.1`. Distinguish the cases in `h2 : X.s0 p.1 p.2 = 1`.

Simplify using `[Set.indicator, Terms.big, Terms.one, h, h2]`. Both sides reduce to the same expression. Establish `h4 : 2 ≤ X.s0 p.1 p.2` using `by omega`. Simplify using `[Set.indicator, Terms.big, Terms.one, h, h2, h4]`. Both sides reduce to the same expression.

Simplify using `[Set.indicator, Terms.big, Terms.one, h]`.
-/
theorem t_PairSplit : PairSplit := by
  intro τ Rw I H H₁ _ _ _ _ _ _ X hA hO hS0
  set Z : τ × τ → ℝ := fun p => (inner ℂ (X.vec p.1) (X.vec p.2)).re with hZdef
  have hZ : Summable Z := summable_re X.vec hA.2.1
  have c1 : ∀ S : Set τ, X.PhiEq S = X.pairSum (X.allPairs S) := by
    intro S
    unfold Terms.PhiEq Terms.pairSum
    congr 1
    have hi : ∀ i, ‖X.vecPart S i‖ ^ 2 = ∑' p : τ × τ,
        (if X.io (X.rowOf p.1) = i then
          (if p.1 ∈ S ∧ p.2 ∈ S ∧ X.io (X.rowOf p.2) = X.io (X.rowOf p.1) then Z p else 0) else 0) := by
      intro i
      unfold Terms.vecPart
      rw [norm_sq_tsum]
      · apply tsum_congr; intro p
        by_cases h1 : X.io (X.rowOf p.1) = i <;> by_cases h2 : X.io (X.rowOf p.2) = i <;>
          by_cases h3 : p.1 ∈ S <;> by_cases h4 : p.2 ∈ S <;>
          simp [Set.indicator, h1, h2, h3, h4, hZdef]
      · simp_rw [norm_indicator_eq_indicator_norm]
        exact hA.2.1.indicator _
    simp_rw [hi]
    rw [← Summable.tsum_finsetSum]
    · apply tsum_congr; intro p
      rw [Finset.sum_ite_eq]
      simp only [mem_univ, if_true]
      by_cases h3 : p.1 ∈ S <;> by_cases h4 : p.2 ∈ S <;>
        by_cases h5 : X.rowOf p.1 = X.rowOf p.2 <;>
        simp [Set.indicator, Terms.allPairs, h3, h4, h5]
      all_goals first
        | rfl
        | (intro h6
           have := hO p.1 p.2 h6.symm h5
           simp [hZdef, this])
    · intro i _
      refine Summable.of_norm_bounded hZ.norm (fun p => ?_)
      split_ifs <;> simp
  refine ⟨c1, ?_, ?_⟩
  · rw [c1]
    unfold Terms.pairSum
    rw [← mul_add, ← mul_add, ← Summable.tsum_add (hZ.indicator _) (hZ.indicator _),
      ← Summable.tsum_add ((hZ.indicator _).add (hZ.indicator _)) (hZ.indicator _)]
    congr 1
    apply tsum_congr; intro p
    by_cases h : p ∈ X.allPairs X.genSet
    · have h1 : 1 ≤ X.s0 p.1 p.2 := hS0 p.1 p.2 h.2.2 h.1.1 h.2.1.1
      by_cases h2 : X.s0 p.1 p.2 = 1
      · by_cases h3 : X.scal p.1 p.2 <;>
          simp [Set.indicator, Terms.big, Terms.nsc, Terms.sc, h, h2, h3] <;> rfl
      · have h4 : 2 ≤ X.s0 p.1 p.2 := by omega
        simp [Set.indicator, Terms.big, Terms.nsc, Terms.sc, h, h2, h4]; rfl
    · simp [Set.indicator, Terms.big, Terms.nsc, Terms.sc, h]
  · rw [c1]
    unfold Terms.pairSum
    rw [← mul_add, ← Summable.tsum_add (hZ.indicator _) (hZ.indicator _)]
    congr 1
    apply tsum_congr; intro p
    by_cases h : p ∈ X.allPairs X.ngSet
    · have h1 : 1 ≤ X.s0 p.1 p.2 := hS0 p.1 p.2 h.2.2 h.1.1 h.2.1.1
      by_cases h2 : X.s0 p.1 p.2 = 1
      · simp [Set.indicator, Terms.big, Terms.one, h, h2]; rfl
      · have h4 : 2 ≤ X.s0 p.1 p.2 := by omega
        simp [Set.indicator, Terms.big, Terms.one, h, h2, h4]; rfl
    · simp [Set.indicator, Terms.big, Terms.one, h]

end Hil5

section Hil6

open Formalism.FourierDecayAlt.PB

/- English proof (translation)
Introduce `hPS hSF τ Rw I H H₁ _ _ _ _ _ _ X ε ε' dd hA hRO hCP hRB hRNG`. Take `⟨-, -, hng⟩` from `hPS τ Rw I H H₁ X hA hRO hCP`. Establish `hsubN : X.big X.ngSet ⊆ X.big X.nzSet`. Introduce `p hp`. Establish `hp' : (p.1 ∈ X.ngSet ∧ p.2 ∈ X.ngSet ∧ X.rowOf p.1 = X.rowOf p.2) ∧ 2 ≤ X.s0 p.1 p.2` using `hp`.

Establish `h1 : p.1 ∈ X.nzSet` using `(show X.G p.1 ≠ 0 ∧ ¬ X.gener p.1 from hp'.1.1).1`. Establish `h2 : p.2 ∈ X.nzSet` using `(show X.G p.2 ≠ 0 ∧ ¬ X.gener p.2 from hp'.1.2.1).1`. Use `show (p.1 ∈ X.nzSet ∧ p.2 ∈ X.nzSet ∧ X.rowOf p.1 = X.rowOf p.2) ∧ 2 ≤ X.s0 p.1 p.2`. Conclude with `⟨⟨h1, h2, hp'.1.2.2⟩, hp'.2⟩`. Take `⟨hmN, -⟩` from `hSF τ Rw I H H₁ X hA _ _ hsubN`.

Take `⟨-, habsN⟩` from `hSF τ Rw I H H₁ X hA _ _ (subset_rfl : X.big X.ngSet ⊆ X.big X.ngSet)`. Establish `hRB' : X.pairAbs (X.big X.nzSet) ≤ ε * dd` using `hRB`. Establish `hRNG' : X.pairSum (X.one X.ngSet) ≤ ε' * dd` using `hRNG`. Establish `hPhiN : X.PhiEq X.ngSet ≤ (ε + ε') * dd`. Rewrite using `[hng]`.

Use `le_abs_self (X.pairSum (X.big X.ngSet))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hPhiN`.
-/
theorem t_NGTotal : NGTotal := by
  intro hPS hSF τ Rw I H H₁ _ _ _ _ _ _ X ε ε' dd hA hRO hCP hRB hRNG
  obtain ⟨-, -, hng⟩ := hPS τ Rw I H H₁ X hA hRO hCP
  have hsubN : X.big X.ngSet ⊆ X.big X.nzSet := by
    intro p hp
    have hp' : (p.1 ∈ X.ngSet ∧ p.2 ∈ X.ngSet ∧ X.rowOf p.1 = X.rowOf p.2) ∧ 2 ≤ X.s0 p.1 p.2 := hp
    have h1 : p.1 ∈ X.nzSet := (show X.G p.1 ≠ 0 ∧ ¬ X.gener p.1 from hp'.1.1).1
    have h2 : p.2 ∈ X.nzSet := (show X.G p.2 ≠ 0 ∧ ¬ X.gener p.2 from hp'.1.2.1).1
    show (p.1 ∈ X.nzSet ∧ p.2 ∈ X.nzSet ∧ X.rowOf p.1 = X.rowOf p.2) ∧ 2 ≤ X.s0 p.1 p.2
    exact ⟨⟨h1, h2, hp'.1.2.2⟩, hp'.2⟩
  obtain ⟨hmN, -⟩ := hSF τ Rw I H H₁ X hA _ _ hsubN
  obtain ⟨-, habsN⟩ := hSF τ Rw I H H₁ X hA _ _ (subset_rfl : X.big X.ngSet ⊆ X.big X.ngSet)
  have hRB' : X.pairAbs (X.big X.nzSet) ≤ ε * dd := hRB
  have hRNG' : X.pairSum (X.one X.ngSet) ≤ ε' * dd := hRNG
  have hPhiN : X.PhiEq X.ngSet ≤ (ε + ε') * dd := by
    rw [hng]
    have := le_abs_self (X.pairSum (X.big X.ngSet))
    linarith
  exact hPhiN

end Hil6

section LocA

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB
open scoped ComplexOrder ComplexConjugate
open Classical

/- English proof (translation)
Establish `e : (Matrix.of fun x y : Y => k' x y) = Matrix.of fun x y : Y => k x y`. Use extensionality with `x y`. Simplify using `only [Matrix.of_apply]`. Conclude with `(h x x.2 y y.2).symm`. Use `show Matrix.PosSemidef (Matrix.of fun x y : Y => k' x y)`.

Rewrite using `[e]`. Conclude with `hk`.
-/
theorem psd_congr {α : Type} {Y : Finset α} {k k' : α → α → ℂ}
    (h : ∀ x ∈ Y, ∀ y ∈ Y, k x y = k' x y) (hk : TB.PSDOn Y k) : TB.PSDOn Y k' := by
  have e : (Matrix.of fun x y : Y => k' x y) = Matrix.of fun x y : Y => k x y := by
    ext x y
    simp only [Matrix.of_apply]
    exact (h x x.2 y y.2).symm
  show Matrix.PosSemidef (Matrix.of fun x y : Y => k' x y)
  rw [e]
  exact hk

/- English proof (translation)
Establish `e : (Matrix.of fun x y : Y => k x y + k' x y) = (Matrix.of fun x y : Y => k x y) + Matrix.of fun x y : Y => k' x y`. Use extensionality with `x y`. Simplify using `[Matrix.of_apply]`. Use `show Matrix.PosSemidef (Matrix.of fun x y : Y => k x y + k' x y)`. Rewrite using `[e]`.

Conclude with `Matrix.PosSemidef.add hk hk'`.
-/
theorem psd_add {α : Type} {Y : Finset α} {k k' : α → α → ℂ}
    (hk : TB.PSDOn Y k) (hk' : TB.PSDOn Y k') : TB.PSDOn Y (fun x y => k x y + k' x y) := by
  have e : (Matrix.of fun x y : Y => k x y + k' x y) =
      (Matrix.of fun x y : Y => k x y) + Matrix.of fun x y : Y => k' x y := by
    ext x y
    simp [Matrix.of_apply]
  show Matrix.PosSemidef (Matrix.of fun x y : Y => k x y + k' x y)
  rw [e]
  exact Matrix.PosSemidef.add hk hk'

/- English proof (translation)
Establish `h` using `hS α Empty Y (fun p => p.elim) (fun p => p.elim)`. Conclude with `psd_congr (fun x _ y _ => by simp) h`.
-/
theorem psd_one (hS : J.SchurProduct) {α : Type} (Y : Finset α) : TB.PSDOn Y (fun _ _ => (1 : ℂ)) := by
  have h := hS α Empty Y (fun p => p.elim) (fun p => p.elim)
  exact psd_congr (fun x _ y _ => by simp) h

variable {E : Type} [Field E]

/- English proof (translation)
Take `⟨p, u, η, m, d, hm, hd, hun, hS⟩` from `h`. Take `⟨Θ, hΘ⟩` from `h13 s hs p.K p.R p.ψ p.datum p.char0 m (Y.image η) (by`. Introduce `h hh`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hh`. Conclude with `hm x hx)`.

Establish `hok` using `hLP hA hA2 p.K p.R p.ψ p.datum E (TB.Pt E) s m p.σ u η Y Θ hs hm hΘ`. Use `⟨J.phaseSys d (J.pullSys p.R p.ψ s p.σ u η Θ), hPh E _ d _ Y hd hok, hS, ?_⟩` and prove the remaining obligations. Introduce `hu t ht`. Establish `h1` using `hUH hA hN0 p.K p.R p.ψ p.datum E (TB.Pt E) s m p.σ u η Y Θ hm (hun hu) hΘ t ht`. Use `psd_congr ?_ h1` and prove the remaining obligations.

Introduce `x hx y hy`. Establish `hL : S.L = (J.pullSys p.R p.ψ s p.σ u η Θ).L` using `hS.2.2.1`. Establish `hN` using `hS.1 t t ht ht x hx y hy`. Rewrite using `[hN, hL]`. Establish `hdd : d t * conj (d t) = 1`.

Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hd t]`. Simplify using the standard rewrite rules. Simplify using `only [J.phaseSys, hdd, one_mul]`. Both sides reduce to the same expression.
-/
theorem pullOk (hA : J.PSDAgree) (hA2 : A5.A2) (hLP : J.LocalPullback) (hPh : J.PhaseOk)
    (hUH : J.LocalUnitHeads) (hN0 : A5.BaseKernelOne)
    (h13 : ∀ s, 1 ≤ s → A5.A13 s) {S : J.LocSys E (TB.Pt E)} {Y : Finset (TB.Pt E)} {s : ℕ} {un : Bool}
    (hs : 1 ≤ s) (h : IsPull S Y s un) :
    ∃ S' : J.LocSys E (TB.Pt E), S'.Ok Y ∧ SameKernels S S' Y ∧
      (un = true → ∀ t : E, t ≠ 0 → TB.PSDOn Y (fun h h' =>
        (if t ∈ S.L then (1 : ℂ) else 0) - S.N t t h h')) := by
  obtain ⟨p, u, η, m, d, hm, hd, hun, hS⟩ := h
  obtain ⟨Θ, hΘ⟩ := h13 s hs p.K p.R p.ψ p.datum p.char0 m (Y.image η) (by
    intro h hh; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hh; exact hm x hx)
  have hok := hLP hA hA2 p.K p.R p.ψ p.datum E (TB.Pt E) s m p.σ u η Y Θ hs hm hΘ
  refine ⟨J.phaseSys d (J.pullSys p.R p.ψ s p.σ u η Θ), hPh E _ d _ Y hd hok, hS, ?_⟩
  intro hu t ht
  have h1 := hUH hA hN0 p.K p.R p.ψ p.datum E (TB.Pt E) s m p.σ u η Y Θ hm (hun hu) hΘ t ht
  refine psd_congr ?_ h1
  intro x hx y hy
  have hL : S.L = (J.pullSys p.R p.ψ s p.σ u η Θ).L := hS.2.2.1
  have hN := hS.1 t t ht ht x hx y hy
  rw [hN, hL]
  have hdd : d t * conj (d t) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hd t]; simp
  simp only [J.phaseSys, hdd, one_mul]
  rfl

/- English proof (translation)
Take `⟨p, u, τ₀, η, m, hm, hun, hS⟩` from `h`. Take `⟨Θ, hu, -, hF⟩` from `h1 p.K p.R p.ψ p.datum m`. Establish `hΘ` using `hF (Y.image η) (by`. Introduce `h hh`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hh`.

Conclude with `hm x hx)`. Establish `hSK` using `hS Θ hΘ.1 hu`. Use `⟨J.topSys p.R p.ψ p.σ u τ₀ η Θ, hTP hA p.K p.R p.ψ p.datum E (TB.Pt E) p.σ u τ₀ η Y Θ hΘ, hSK, ?_⟩` and prove the remaining obligations. Introduce `hu' t ht`. Establish `h2` using `hTU hA hN0 p.K p.R p.ψ p.datum E (TB.Pt E) m p.σ u τ₀ η Y Θ hm (hun hu').1 (hun hu').2 hΘ t`.

Use `psd_congr ?_ h2` and prove the remaining obligations. Introduce `x hx y hy`. Rewrite using `[hSK.1 t t ht ht x hx y hy, hSK.2.2.1]`.
-/
theorem topOk (hA : J.PSDAgree) (hTP : J.TopPullback) (hTU : J.TopUnitHeads) (hN0 : A5.BaseKernelOne)
    (h1 : A5.SingleBlockThetaProps) {S : J.LocSys E (TB.Pt E)} {Y : Finset (TB.Pt E)} {un : Bool}
    (h : IsTopSys S Y un) :
    ∃ S' : J.LocSys E (TB.Pt E), S'.Ok Y ∧ SameKernels S S' Y ∧
      (un = true → ∀ t : E, t ≠ 0 → TB.PSDOn Y (fun h h' =>
        (if t ∈ S.L then (1 : ℂ) else 0) - S.N t t h h')) := by
  obtain ⟨p, u, τ₀, η, m, hm, hun, hS⟩ := h
  obtain ⟨Θ, hu, -, hF⟩ := h1 p.K p.R p.ψ p.datum m
  have hΘ := hF (Y.image η) (by
    intro h hh; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hh; exact hm x hx)
  have hSK := hS Θ hΘ.1 hu
  refine ⟨J.topSys p.R p.ψ p.σ u τ₀ η Θ, hTP hA p.K p.R p.ψ p.datum E (TB.Pt E) p.σ u τ₀ η Y Θ hΘ, hSK, ?_⟩
  intro hu' t ht
  have h2 := hTU hA hN0 p.K p.R p.ψ p.datum E (TB.Pt E) m p.σ u τ₀ η Y Θ hm (hun hu').1 (hun hu').2 hΘ t
  refine psd_congr ?_ h2
  intro x hx y hy
  rw [hSK.1 t t ht ht x hx y hy, hSK.2.2.1]

end LocA

section LocB

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB
open scoped ComplexOrder ComplexConjugate
open Classical

variable {E : Type} [Field E]

/- English proof (translation)
Take `⟨hB, hF⟩` from `h`. Establish `fac : ∀ F : J.LocSys E (TB.Pt E), ((tp ∧ IsTopSys F Y true) ∨ (¬ tp ∧ IsPull F Y s true)) → ∃ S' : J.LocSys E (TB.Pt E), S'.Ok Y ∧ SameKernels F S' Y ∧ (∀ t : E, t ≠ 0 → TB.PSDOn Y (fun h h' => (if t ∈ F.L then (1 : ℂ) else 0) - F.N t t h h'))`. Introduce `F hF`. Break down `hF with ⟨-, hT⟩ | ⟨-, hP⟩` into its components or cases. Take `⟨S', a, b, c⟩` from `topOk hA hTP hTU hN0 h1 hT`.

Conclude with `⟨S', a, b, c rfl⟩`. Take `⟨S', a, b, c⟩` from `pullOk hA hA2 hLP hPh hUH hN0 h13 hs hP`. Conclude with `⟨S', a, b, c rfl⟩`. Use `⟨J.LocSys.mk S.N (fun t _ _ => if t ∈ S.L then 1 else 0) (fun _ _ => 1) S.L S.L', hOS E (TB.Pt E) S.N S.L S.L' Y ?_ ?_ ?_, ⟨fun _ _ _ _ _ _ _ _ => rfl, hB, rfl, rfl⟩⟩` and prove the remaining obligations. Introduce `t t' ht ht' h hh h' hh' hne`.

Take `⟨Q, _, F, hQ, hN, -, hL'⟩` from `hF t t' ht ht'`. Apply `hL'` to reduce the goal to its premises. Introduce `q`. Take `⟨S', hok, hSK, -⟩` from `fac (F q) (hQ q)`. Rewrite using `[hSK.2.2.2]`.

Apply `hok.1 t t' ht ht' h hh h' hh'` to reduce the goal to its premises. Rewrite using `[← hSK.1 t t' ht ht' h hh h' hh']`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Rewrite using `[hN h hh h' hh']`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ q) h0`. Introduce `t ht`. Take `⟨Q, _, F, hQ, hN, -, -⟩` from `hF t t ht ht`. Use `hSch (TB.Pt E) Q Y (fun q => (F q).N t t) (by` as an intermediate fact. Introduce `q`.

Take `⟨S', hok, hSK, -⟩` from `fac (F q) (hQ q)`. Conclude with `psd_congr (fun x hx y hy => (hSK.1 t t ht ht x hx y hy).symm) (hok.2.1 t ht))`. Conclude with `psd_congr (fun x hx y hy => (hN x hx y hy).symm) this`. Introduce `t ht`. Take `⟨Q, _, F, hQ, hN, hL, -⟩` from `hF t t ht ht`.

Establish `key` using `hOD hPD E (TB.Pt E) Q (fun q => (F q).N t t) (fun q => (F q).L) t Y (by`. Introduce `q`. Take `⟨S', hok, hSK, -⟩` from `fac (F q) (hQ q)`. Conclude with `psd_congr (fun x hx y hy => (hSK.1 t t ht ht x hx y hy).symm) (hok.2.1 t ht)) (by`. Introduce `q`.

Take `⟨S', -, -, hd⟩` from `fac (F q) (hQ q)`. Conclude with `hd t ht)`. Distinguish the cases in `hin : t ∈ ⨅ q, (F q).L`. Establish `hS : t ∈ S.L` using `hL (fun q => (AddSubgroup.mem_iInf.1 hin) q)`. Use `psd_congr ?_ key` and prove the remaining obligations.

Introduce `x hx y hy`. Simplify using `only [hin, hS, if_true, hN x hx y hy]`. Distinguish the cases in `hS : t ∈ S.L`. Use `psd_add (psd_one hSch Y) key` as an intermediate fact. Use `psd_congr ?_ this` and prove the remaining obligations.

Introduce `x hx y hy`. Simplify using `only [hin, hS, if_true, if_false, hN x hx y hy]`. Expand and normalize the polynomial expressions, which then agree. Use `psd_congr ?_ key` and prove the remaining obligations. Introduce `x hx y hy`.

Simplify using `only [hin, hS, if_false, hN x hx y hy]`.
-/
theorem outOk (hA : J.PSDAgree) (hA2 : A5.A2) (hLP : J.LocalPullback) (hPh : J.PhaseOk)
    (hUH : J.LocalUnitHeads) (hN0 : A5.BaseKernelOne) (h13 : ∀ s, 1 ≤ s → A5.A13 s)
    (hTP : J.TopPullback) (hTU : J.TopUnitHeads) (h1 : A5.SingleBlockThetaProps)
    (hSch : J.SchurProduct) (hPD : J.ProductDomination) (hOD : J.OutsideDomination)
    (hOS : J.OutsideSysOk)
    {S : J.LocSys E (TB.Pt E)} {Y : Finset (TB.Pt E)} {s : ℕ} {tp : Prop}
    (hs : 1 ≤ s) (h : IsOut S Y s tp) :
    ∃ S' : J.LocSys E (TB.Pt E), S'.Ok Y ∧ SameKernels S S' Y := by
  obtain ⟨hB, hF⟩ := h
  have fac : ∀ F : J.LocSys E (TB.Pt E), ((tp ∧ IsTopSys F Y true) ∨ (¬ tp ∧ IsPull F Y s true)) →
      ∃ S' : J.LocSys E (TB.Pt E), S'.Ok Y ∧ SameKernels F S' Y ∧
      (∀ t : E, t ≠ 0 → TB.PSDOn Y (fun h h' => (if t ∈ F.L then (1 : ℂ) else 0) - F.N t t h h')) := by
    intro F hF
    rcases hF with ⟨-, hT⟩ | ⟨-, hP⟩
    · obtain ⟨S', a, b, c⟩ := topOk hA hTP hTU hN0 h1 hT
      exact ⟨S', a, b, c rfl⟩
    · obtain ⟨S', a, b, c⟩ := pullOk hA hA2 hLP hPh hUH hN0 h13 hs hP
      exact ⟨S', a, b, c rfl⟩
  refine ⟨J.LocSys.mk S.N (fun t _ _ => if t ∈ S.L then 1 else 0) (fun _ _ => 1) S.L S.L',
    hOS E (TB.Pt E) S.N S.L S.L' Y ?_ ?_ ?_, ⟨fun _ _ _ _ _ _ _ _ => rfl, hB, rfl, rfl⟩⟩
  · intro t t' ht ht' h hh h' hh' hne
    obtain ⟨Q, _, F, hQ, hN, -, hL'⟩ := hF t t' ht ht'
    apply hL'
    intro q
    obtain ⟨S', hok, hSK, -⟩ := fac (F q) (hQ q)
    rw [hSK.2.2.2]
    apply hok.1 t t' ht ht' h hh h' hh'
    rw [← hSK.1 t t' ht ht' h hh h' hh']
    intro h0
    apply hne
    rw [hN h hh h' hh']
    exact Finset.prod_eq_zero (Finset.mem_univ q) h0
  · intro t ht
    obtain ⟨Q, _, F, hQ, hN, -, -⟩ := hF t t ht ht
    have := hSch (TB.Pt E) Q Y (fun q => (F q).N t t) (by
      intro q
      obtain ⟨S', hok, hSK, -⟩ := fac (F q) (hQ q)
      exact psd_congr (fun x hx y hy => (hSK.1 t t ht ht x hx y hy).symm) (hok.2.1 t ht))
    exact psd_congr (fun x hx y hy => (hN x hx y hy).symm) this
  · intro t ht
    obtain ⟨Q, _, F, hQ, hN, hL, -⟩ := hF t t ht ht
    have key := hOD hPD E (TB.Pt E) Q (fun q => (F q).N t t) (fun q => (F q).L) t Y (by
      intro q
      obtain ⟨S', hok, hSK, -⟩ := fac (F q) (hQ q)
      exact psd_congr (fun x hx y hy => (hSK.1 t t ht ht x hx y hy).symm) (hok.2.1 t ht)) (by
      intro q
      obtain ⟨S', -, -, hd⟩ := fac (F q) (hQ q)
      exact hd t ht)
    by_cases hin : t ∈ ⨅ q, (F q).L
    · have hS : t ∈ S.L := hL (fun q => (AddSubgroup.mem_iInf.1 hin) q)
      refine psd_congr ?_ key
      intro x hx y hy
      simp only [hin, hS, if_true, hN x hx y hy]
    · by_cases hS : t ∈ S.L
      · have := psd_add (psd_one hSch Y) key
        refine psd_congr ?_ this
        intro x hx y hy
        simp only [hin, hS, if_true, if_false, hN x hx y hy]
        ring
      · refine psd_congr ?_ key
        intro x hx y hy
        simp only [hin, hS, if_false, hN x hx y hy]

/- English proof (translation)
Take `⟨P, _, S, a, hS, hN, hB, hL, hL'⟩` from `hD.2.1 i s hs hsi hi Y hY`. Establish `ex : ∀ p, ∃ S' : J.LocSys E (TB.Pt E), S'.Ok Y ∧ SameKernels (S p) S' Y`. Introduce `p`. Break down `hS p with ⟨-, hT⟩ | ⟨-, hP⟩ | hO` into its components or cases. Take `⟨S', a, b, -⟩` from `topOk hA hTP hTU hN0 h1 hT`.

Conclude with `⟨S', a, b⟩`. Take `⟨S', a, b, -⟩` from `pullOk hA hA2 hLP hPh hUH hN0 h13 hs hP`. Conclude with `⟨S', a, b⟩`. Conclude with `outOk hA hA2 hLP hPh hUH hN0 h13 hTP hTU h1 hSch hPD hOD hOS hs hO`. Use `choose S' hok hSK using ex`.

Use `⟨P, inferInstance, S', a, hok, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `t t' ht ht' h hh h' hh'`. Rewrite using `[hN t t' ht ht' h hh h' hh']`. Simplify using `only [J.scaleSys, J.prodSys]`. Use `congr 1`.

Conclude with `Finset.prod_congr rfl (fun p _ => (hSK p).1 t t' ht ht' h hh h' hh')`. Introduce `h hh h' hh'`. Rewrite using `[hB h hh h' hh']`. Simplify using `only [J.scaleSys, J.prodSys]`. Use `congr 1`.

Conclude with `Finset.prod_congr rfl (fun p _ => (hSK p).2.1 h hh h' hh')`. Rewrite using `[hL]`. Conclude with `iInf_congr (fun p => (hSK p).2.2.1)`. Establish `: (⨅ p, (S' p).L') = ⨅ p, (S p).L'` using `iInf_congr (fun p => ((hSK p).2.2.2).symm)`. Rewrite using `[this]`.

Conclude with `hL'`.
-/
theorem famOk (hA : J.PSDAgree) (hA2 : A5.A2) (hLP : J.LocalPullback) (hPh : J.PhaseOk)
    (hUH : J.LocalUnitHeads) (hN0 : A5.BaseKernelOne) (h13 : ∀ s, 1 ≤ s → A5.A13 s)
    (hTP : J.TopPullback) (hTU : J.TopUnitHeads) (h1 : A5.SingleBlockThetaProps)
    (hSch : J.SchurProduct) (hPD : J.ProductDomination) (hOD : J.OutsideDomination)
    (hOS : J.OutsideSysOk) {W : Type} (D : TB.Data E W) (hD : LocalModel D)
    (i s : ℕ) (hs : 1 ≤ s) (hsi : s ≤ i) (hi : i ≤ D.r + 1) (Y : Finset (TB.Pt E))
    (hY : ∀ h ∈ Y, TB.level h = i - s) :
    ∃ (P : Type) (_ : Fintype P) (S : P → J.LocSys E (TB.Pt E)) (a : TB.Pt E → ℝ),
      (∀ p, (S p).Ok Y) ∧
      (∀ t t', t ≠ 0 → t' ≠ 0 → ∀ h ∈ Y, ∀ h' ∈ Y,
        (J.sysOf D i s).N t t' h h' = (J.scaleSys a (J.prodSys S)).N t t' h h') ∧
      (∀ h ∈ Y, ∀ h' ∈ Y, (J.sysOf D i s).B h h' = (J.scaleSys a (J.prodSys S)).B h h') ∧
      (J.sysOf D i s).L = ⨅ p, (S p).L ∧ (⨅ p, (S p).L') ≤ (J.sysOf D i s).L' := by
  obtain ⟨P, _, S, a, hS, hN, hB, hL, hL'⟩ := hD.2.1 i s hs hsi hi Y hY
  have ex : ∀ p, ∃ S' : J.LocSys E (TB.Pt E), S'.Ok Y ∧ SameKernels (S p) S' Y := by
    intro p
    rcases hS p with ⟨-, hT⟩ | ⟨-, hP⟩ | hO
    · obtain ⟨S', a, b, -⟩ := topOk hA hTP hTU hN0 h1 hT
      exact ⟨S', a, b⟩
    · obtain ⟨S', a, b, -⟩ := pullOk hA hA2 hLP hPh hUH hN0 h13 hs hP
      exact ⟨S', a, b⟩
    · exact outOk hA hA2 hLP hPh hUH hN0 h13 hTP hTU h1 hSch hPD hOD hOS hs hO
  choose S' hok hSK using ex
  refine ⟨P, inferInstance, S', a, hok, ?_, ?_, ?_, ?_⟩
  · intro t t' ht ht' h hh h' hh'
    rw [hN t t' ht ht' h hh h' hh']
    simp only [J.scaleSys, J.prodSys]
    congr 1
    exact Finset.prod_congr rfl (fun p _ => (hSK p).1 t t' ht ht' h hh h' hh')
  · intro h hh h' hh'
    rw [hB h hh h' hh']
    simp only [J.scaleSys, J.prodSys]
    congr 1
    exact Finset.prod_congr rfl (fun p _ => (hSK p).2.1 h hh h' hh')
  · rw [hL]; exact iInf_congr (fun p => (hSK p).2.2.1)
  · have : (⨅ p, (S' p).L') = ⨅ p, (S p).L' := iInf_congr (fun p => ((hSK p).2.2.2).symm)
    rw [this]; exact hL'

end LocB

section Loc

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB
open scoped ComplexOrder ComplexConjugate
open Classical

/- English proof (translation)
Introduce and unpack `⟨hA, hSch, hPD, hDS, hDP, hBD, hPL, hSO, hPh, hOS, hOD, hLP, hUH, hTP, hTU, hGL, hUM, hAS, hAF, hKL, hLK, hDM, hDA, hA2, hKG, hN0, -, -, h1, -, -, -⟩ h13 E W _ D hD`. Establish `fam` using `fun i s hs hsi hi Y hY => famOk hA hA2 hLP hPh hUH hN0 h13 hTP hTU h1 hSch hPD hOD hOS D hD i s hs hsi hi Y hY`. Establish `hE : ∀ i, 1 ≤ i → i ≤ D.r + 1 → 0 ≤ D.e i ∧ D.e i ≤ 1`. Apply the tactic sequence `intro i h1 h2; rw [hD.2.2.2 i h1 h2]; constructor <;> norm_num`. Use `⟨?_, ?_, hE, ?_⟩` and prove the remaining obligations.

Introduce `i Y`. Take `⟨P, _, pl, η, cl, d, a, hK⟩` from `hD.1 i Y`. Use `hKL hSch hDS (TB.Pt E) P Y (D.Kr i) (fun p x y => if cl p x = cl p y then d p x * conj (d p y) * A5.Kp (pl p).R (pl p).ψ (η p x) (η p y) else 0) a hK ?_` and prove the remaining obligations. Introduce `p`. Use `hBD (TB.Pt E) (Option E) Y (cl p) (fun x y => d p x * conj (d p y) * A5.Kp (pl p).R (pl p).ψ (η p x) (η p y)) ?_` and prove the remaining obligations.

Introduce `b`. Conclude with `hDP (TB.Pt E) _ _ (d p) (hLK hA hKG (pl p).K (pl p).R (pl p).ψ (pl p).datum (TB.Pt E) (η p) _)`. Take `⟨Th, h2, -, -⟩` from `hAF hUM hAS E W D (by`. Introduce `i s hs hsi hi Y hY`. Take `⟨P, _, S, a, hok, hN, hB, hL, hL'⟩` from `fam i s hs hsi hi Y hY`.

Conclude with `hGL hPL hSO E W P D i s S a Y hN hB hL hL' hok) hE hD.2.2.1`. Conclude with `h2`. Use `(hDA hPL hSO hDM E W D ?_).2` and prove the remaining obligations. Introduce `T i s hs hsi hi`. Take `⟨P, _, S, a, hok, hN, hB, hL, -⟩` from `fam i s hs hsi hi (T.X (i - s)) (fun h hh => ((T.isTower (i - s) h).1 hh).1)`.

Conclude with `⟨P, inferInstance, S, a, hok, fun t ht h hh h' hh' => hN t t ht ht h hh h' hh', hB, hL⟩`.
-/
theorem t_AxiomsOfLocalModel : AxiomsOfLocalModel := by
  rintro ⟨hA, hSch, hPD, hDS, hDP, hBD, hPL, hSO, hPh, hOS, hOD, hLP, hUH, hTP, hTU, hGL, hUM, hAS, hAF,
    hKL, hLK, hDM, hDA, hA2, hKG, hN0, -, -, h1, -, -, -⟩ h13 E W _ D hD
  have fam := fun i s hs hsi hi Y hY =>
    famOk hA hA2 hLP hPh hUH hN0 h13 hTP hTU h1 hSch hPD hOD hOS D hD i s hs hsi hi Y hY
  have hE : ∀ i, 1 ≤ i → i ≤ D.r + 1 → 0 ≤ D.e i ∧ D.e i ≤ 1 := by
    intro i h1 h2; rw [hD.2.2.2 i h1 h2]; constructor <;> norm_num
  refine ⟨?_, ?_, hE, ?_⟩
  · intro i Y
    obtain ⟨P, _, pl, η, cl, d, a, hK⟩ := hD.1 i Y
    refine hKL hSch hDS (TB.Pt E) P Y (D.Kr i)
      (fun p x y => if cl p x = cl p y then
          d p x * conj (d p y) * A5.Kp (pl p).R (pl p).ψ (η p x) (η p y) else 0) a hK ?_
    intro p
    refine hBD (TB.Pt E) (Option E) Y (cl p)
      (fun x y => d p x * conj (d p y) * A5.Kp (pl p).R (pl p).ψ (η p x) (η p y)) ?_
    intro b
    exact hDP (TB.Pt E) _ _ (d p)
      (hLK hA hKG (pl p).K (pl p).R (pl p).ψ (pl p).datum (TB.Pt E) (η p) _)
  · obtain ⟨Th, h2, -, -⟩ := hAF hUM hAS E W D (by
      intro i s hs hsi hi Y hY
      obtain ⟨P, _, S, a, hok, hN, hB, hL, hL'⟩ := fam i s hs hsi hi Y hY
      exact hGL hPL hSO E W P D i s S a Y hN hB hL hL' hok) hE hD.2.2.1
    exact h2
  · refine (hDA hPL hSO hDM E W D ?_).2
    intro T i s hs hsi hi
    obtain ⟨P, _, S, a, hok, hN, hB, hL, -⟩ := fam i s hs hsi hi (T.X (i - s))
      (fun h hh => ((T.isTower (i - s) h).1 hh).1)
    exact ⟨P, inferInstance, S, a, hok, fun t ht h hh h' hh' => hN t t ht ht h hh h' hh', hB, hL⟩

end Loc

section Lat

open NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB

/- English proof (translation)
Introduce `E _ _ _ g ν s P hP hgP K _ R σ hσ ω hω hω' u α ψ η Θ hu t`. Establish `key : ∀ B : S6.FI E, S6.ConjStable E B → ∀ x : E, x ∈ S6.locAt E P (S6.zsub E B) → x - (-1) ^ s * IsCMField.complexConj E x ∈ S6.locAt E P (S6.zsub E B)`. Introduce `B hB x hx`. Take `⟨a, ha, h⟩` from `hx`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations.

Establish `hc : IsCMField.complexConj E (algebraMap (𝓞 (maximalRealSubfield E)) E a * x) ∈ S6.zsub E B` using `hB _ h`. Rewrite `hc` using `[map_mul, Formalism.FourierDecayAlt.P.S6x2.conj_real]`. Establish `e : algebraMap (𝓞 (maximalRealSubfield E)) E a * (x - (-1) ^ s * IsCMField.complexConj E x) = algebraMap (𝓞 (maximalRealSubfield E)) E a * x - (-1) ^ s * (algebraMap (𝓞 (maximalRealSubfield E)) E a * IsCMField.complexConj E x)` using `by ring`. Rewrite using `[e]`. Apply the tactic sequence `rcases neg_one_pow_eq_or E s with h1 | h1 <;> rw [h1]`.

Rewrite using `[one_mul]`. Conclude with `(S6.zsub E B).sub_mem h hc`. Rewrite using `[neg_one_mul, sub_neg_eq_add]`. Conclude with `(S6.zsub E B).add_mem h hc`. Establish `hPer : t ∈ S6.locAt E P (S6.perLat E g ν s) ↔ t ∈ S6.locAt E P (S6.zsub E (S6.idl E g 0 ν))`.

Unfold `S6.perLat`. Rewrite using `[Formalism.FourierDecayAlt.P.localTwistedLattice E _ _ s P hP t, Formalism.FourierDecayAlt.P.localAwayFromLevel E g 1 ν P hP hgP, Formalism.FourierDecayAlt.P.localAwayFromLevel E g 2 ν P hP hgP]`. Conclude with `⟨fun h => h.1, fun h => ⟨h, key _ (Formalism.FourierDecayAlt.P.different_power_conj_stable E g 0 ν) t h⟩⟩`. Establish `hLift : t ∈ S6.locAt E P (S6.liftLat E g ν s) ↔ t ∈ S6.locAt E P (S6.zsub E (S6.idl E g 0 (-ν)))`. Unfold `S6.liftLat`.

Rewrite using `[Formalism.FourierDecayAlt.P.localTwistedLattice E _ _ s P hP t, Formalism.FourierDecayAlt.P.localAwayFromLevel E g (-1) (-ν) P hP hgP]`. Conclude with `⟨fun h => h.1, fun h => ⟨h, key _ (Formalism.FourierDecayAlt.P.different_power_conj_stable E g 0 (-ν)) t h⟩⟩`. Establish `hinv : ((u⁻¹ : Kˣ) : K) = σ ω⁻¹`. Distinguish the cases in `hω0 : ω = 0`. Establish `h0 : (u : K) = 0` using `by rw [hu, hω0, map_zero]`.

Establish `h10 : (1 : K) = 0` using `by rw [← u.mul_inv, h0, zero_mul]`. Use `subsingleton_of_zero_eq_one h10.symm` as an intermediate fact. Conclude with `Subsingleton.elim _ _`. Apply `Units.inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[hu, ← map_mul, mul_inv_cancel₀ hω0, map_one]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show (u : K) * σ t ∈ R ↔ _`. Rewrite using `[hu, ← map_mul, ← hσ, ← hω, hPer]`. Use `show ((u⁻¹ : Kˣ) : K) * σ t ∈ R ↔ _`. Rewrite using `[hinv, ← map_mul, ← hσ, ← hω', hLift]`.
-/
theorem t_PullLatticeOrdinary : PullLatticeOrdinary := by
  intro E _ _ _ g ν s P hP hgP K _ R σ hσ ω hω hω' u α ψ η Θ hu t
  have key : ∀ B : S6.FI E, S6.ConjStable E B → ∀ x : E, x ∈ S6.locAt E P (S6.zsub E B) →
      x - (-1) ^ s * IsCMField.complexConj E x ∈ S6.locAt E P (S6.zsub E B) := by
    intro B hB x hx
    obtain ⟨a, ha, h⟩ := hx
    refine ⟨a, ha, ?_⟩
    have hc : IsCMField.complexConj E (algebraMap (𝓞 (maximalRealSubfield E)) E a * x) ∈ S6.zsub E B :=
      hB _ h
    rw [map_mul, Formalism.FourierDecayAlt.P.S6x2.conj_real] at hc
    have e : algebraMap (𝓞 (maximalRealSubfield E)) E a * (x - (-1) ^ s * IsCMField.complexConj E x) =
        algebraMap (𝓞 (maximalRealSubfield E)) E a * x -
          (-1) ^ s * (algebraMap (𝓞 (maximalRealSubfield E)) E a * IsCMField.complexConj E x) := by ring
    rw [e]
    rcases neg_one_pow_eq_or E s with h1 | h1 <;> rw [h1]
    · rw [one_mul]; exact (S6.zsub E B).sub_mem h hc
    · rw [neg_one_mul, sub_neg_eq_add]; exact (S6.zsub E B).add_mem h hc
  have hPer : t ∈ S6.locAt E P (S6.perLat E g ν s) ↔ t ∈ S6.locAt E P (S6.zsub E (S6.idl E g 0 ν)) := by
    unfold S6.perLat
    rw [Formalism.FourierDecayAlt.P.localTwistedLattice E _ _ s P hP t, Formalism.FourierDecayAlt.P.localAwayFromLevel E g 1 ν P hP hgP,
      Formalism.FourierDecayAlt.P.localAwayFromLevel E g 2 ν P hP hgP]
    exact ⟨fun h => h.1, fun h => ⟨h, key _ (Formalism.FourierDecayAlt.P.different_power_conj_stable E g 0 ν) t h⟩⟩
  have hLift : t ∈ S6.locAt E P (S6.liftLat E g ν s) ↔
      t ∈ S6.locAt E P (S6.zsub E (S6.idl E g 0 (-ν))) := by
    unfold S6.liftLat
    rw [Formalism.FourierDecayAlt.P.localTwistedLattice E _ _ s P hP t, Formalism.FourierDecayAlt.P.localAwayFromLevel E g (-1) (-ν) P hP hgP]
    exact ⟨fun h => h.1, fun h => ⟨h, key _ (Formalism.FourierDecayAlt.P.different_power_conj_stable E g 0 (-ν)) t h⟩⟩
  have hinv : ((u⁻¹ : Kˣ) : K) = σ ω⁻¹ := by
    by_cases hω0 : ω = 0
    · have h0 : (u : K) = 0 := by rw [hu, hω0, map_zero]
      have h10 : (1 : K) = 0 := by rw [← u.mul_inv, h0, zero_mul]
      have := subsingleton_of_zero_eq_one h10.symm
      exact Subsingleton.elim _ _
    · apply Units.inv_eq_of_mul_eq_one_right
      rw [hu, ← map_mul, mul_inv_cancel₀ hω0, map_one]
  refine ⟨?_, ?_⟩
  · show (u : K) * σ t ∈ R ↔ _
    rw [hu, ← map_mul, ← hσ, ← hω, hPer]
  · show ((u⁻¹ : Kˣ) : K) * σ t ∈ R ↔ _
    rw [hinv, ← map_mul, ← hσ, ← hω', hLift]

/- English proof (translation)
Assemble the required witnesses or components as `⟨Formalism.FourierDecayAlt.P.intersection_of_local, Formalism.FourierDecayAlt.P.lattice_of_local, Formalism.FourierDecayAlt.P.twistedIsRealOrderLattice, Formalism.FourierDecayAlt.P.pull_lattice_typed, Formalism.FourierDecayAlt.P.pull_lattice_typed_unit, Formalism.FourierDecayAlt. …`.
-/
theorem t_LatticeLink : LatticeLink :=
  ⟨Formalism.FourierDecayAlt.P.intersection_of_local, Formalism.FourierDecayAlt.P.lattice_of_local,
    Formalism.FourierDecayAlt.P.twistedIsRealOrderLattice, Formalism.FourierDecayAlt.P.pull_lattice_typed,
    Formalism.FourierDecayAlt.P.pull_lattice_typed_unit, Formalism.FourierDecayAlt.P.pull_lift_typed,
    Formalism.FourierDecayAlt.P.pull_lift_typed_unit, t_PullLatticeOrdinary⟩

end Lat

section Main

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Formalism.FourierDecayAlt.PB
open scoped ComplexOrder ComplexConjugate

/- English proof (translation)
Introduce `hLC hGC _hLL hAx h13s C₄ Cthr h4`. Establish `hLC2` using `hLC`. Take `⟨hA, hSch, hPD, hDS, hDP, hBD, hPL, hSO, hPh, hOS, hOD, hLP, hUH, hTP, hTU, hGL, hUM, hAS, hAF, hKL, hLK, hDM, hDA, hA2, hKG, hN0, hN1P, hTh1, h1, hNsS, hNsB, hLA⟩` from `hLC`. Take `⟨hTA, hRW, hDST, hSBM, hRST, hDSum, hDL2, hDSz, hDC, hPT, hPJ, hPSJ, hBox, hLat, hId, hNorm, hDeg, hFP, hX, hLSJ, hIS, hILS, hSz, hSR, hGP, hMT, hFM⟩` from `hGC`. Establish `hLem : A5.LemmaA` using `hLA hA2 hN1P hTh1 h1 h13s hN0 hNsS hNsB`.

Establish `h13 : ∀ s, 1 ≤ s → A5.A13 s` using `hLem.2.1`. Take `⟨C₁, hC1, hIL⟩` from `hILS hLSJ hIS hBox hLat hId hNorm hDeg hFP hX`. Take `⟨CT, CT', hT⟩` from `hRW hTA C₁ C₄ hC1 h4`. Use `⟨max (max Cthr 1) |CT|, |CT|, le_trans (le_max_left _ _) (le_max_left _ _), le_trans (le_max_right _ _) (le_max_left _ _), abs_nonneg _, le_max_right _ _, ?_⟩` and prove the remaining obligations. Introduce `C0 CG CDel cT Cb hC0 hCG hCDel hcT hCb hcTb`.

Take `⟨k1, hk1⟩` from `hSR hSz (max (max Cthr 1) |CT|) C0 CG CDel cT Cb |CT| CT' (le_trans (le_max_right _ _) (le_max_left _ _)) hC0 hCG hCDel hcT hCb hcTb (abs_nonneg _) (le_max_right _ _)`. Take `⟨k3, hk3⟩` from `hGP CDel Cb hCDel hCb`. Use `⟨max k1 k3, ?_⟩` and prove the remaining obligations. Introduce `E W _ _ _ D e G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf hU hInst hLM jn H _ _ _ Vt c sd hReal hDens P _ B hRows hMassData hEL`. Take `⟨hI, he1, hδ⟩` from `hEL`.

Take `⟨hg1, hg2, hlen⟩` from `hk3 (InfinitePlace E) G bb (le_trans (le_max_right _ _) hk) hyp.1`. Take `⟨s1, s2, s3, s4, s5⟩` from `hk1 (InfinitePlace E) G bb Cp Cf Th de de' T T' du du' l (le_trans (le_max_left _ _) hk) hyp h16 hCf`. Establish `hGr : IsGreatest (G.thrSet (max (max Cthr 1) |CT|) de de' T T' l) ((Th ^ G.f)⁻¹)`. Take `⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩` from `hyp`. Conclude with `h`.

Establish `hCA0 : 0 ≤ max (max Cthr 1) |CT|` using `le_trans (abs_nonneg _) (le_max_right _ _)`. Take `⟨hSB, hLS⟩` from `hIL E W D e G _ de de' T T' l Th hU hInst hg1 hg2 hCA0 hlen s2 hGr`. Establish `hf : D.f = G.f`. Use `Fintype.card_congr e` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin]`.

Conclude with `this`. Establish `hr : D.r = G.r` using `hInst.1`. Establish `hf1 : 1 ≤ D.f`. Take `⟨_, d2, d3⟩` from `hDeg E`. Rewrite using `[hf]`.

Unfold `Sz.Glob.f`. Use linear arithmetic over natural numbers and integers. Establish `hK : 4 ≤ D.K` using `by rw [hInst.2.1]; norm_num`. Establish `hTh0 : 0 < Th` using `by linarith`. Take `⟨hKr, hAxA2, hEB, hDomA⟩` from `hAx hLC2 h13 E W D hLM`.

Take `⟨r1, r2, r3, r4, r5, r6, r7, r8⟩` from `hReal`. Establish `hPS : D.PoissonStep`. Take `⟨V, i1, i2, i3, i4, i5, ι, i6, π, Λ, i7, i8, emb, dmap, hb, hFr, hW⟩` from `r4`. Conclude with `hPSJ hPT hPJ E W D V ι π hb Λ emb dmap hFr hW`. Establish `hA4 : D.LeadingDomination Vt (fun _ _ => (0 : ℂ))`.

Use `⟨fun ρ p h => absurd rfl h, fun Y _ R => ?_, fun ρ => ?_⟩` and prove the remaining obligations. Conclude with `Formalism.FourierDecayAlt.P.Jx7.psd_congr (fun x _ y _ => by simp) (hKr (D.r + 1) Y)`. Simplify using the standard rewrite rules. Establish `hRec : TC.RecHypAfter D C₁ C₄ Th jn Vt (fun _ _ => (0 : ℂ))` using `⟨hK, hf1, hTh0, hSB, r1, hKr, r2, hAxA2, hEB, hDomA, r3, hPS, r5, r6, hLS, r7, r8, hA4⟩`. Take `⟨hk5, Pd, q, lq, hq, hcard, hx⟩` from `hDens`.

Take `⟨hsdE, hsd2⟩` from `hDC hDSum hDL2 hDSz Pd q lq G.k G.r G.f sd hk5 hq hcard hx`. Establish `he0 : D.e (D.r + 1) = 0` using `hLM.2.2.2 (D.r + 1) (by omega) le_rfl`. Take `⟨w1, w2, w3, w4, w5, w6⟩` from `hRows`. Take `⟨q1, q2, q3, q4, q5⟩` from `hRST hDST hSBM E W D C₁ C₄ Th jn H Vt (fun _ _ => (0 : ℂ)) c sd hsd2 he0 hRec w1 w2 w3`. Establish `hjn` using `Formalism.FourierDecayAlt.P.Jx7.jn_nonneg D jn r1 r7`.

Establish `habs : (CT / Th) ^ D.f ≤ (|CT| / Th) ^ D.f`. Combine the equalities or inequalities in the displayed calculation. Establish `hr0 : (0 : ℝ) ≤ D.r` using `Nat.cast_nonneg _`. Establish `hsm : (D.r : ℝ) * (CT / Th) ^ D.f ≤ 1`. Use `le_trans (mul_le_mul_of_nonneg_left habs hr0) ?_` and prove the remaining obligations.

Rewrite using `[hr, hf]`. Conclude with `s3`. Establish `he1p : 0 < B.e1` using `by rw [he1]; exact lt_of_lt_of_le one_pos (le_max_right _ _)`. Establish `hbound : ∀ R : Finset ℕ, ∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2 ≤ (1 + B.δ) * B.e1 * B.IntN`. Introduce `R`.

Use `hT E W (TC.scaleTop D (max sd 1)) Th jn H Vt c sd q1 s1 (by rw [q2, q3]; exact hsm) (fun i hi => by` as an intermediate fact. Rewrite `hi` using `[q2]`. Rewrite using `[q5 i hi]`. Conclude with `hLM.2.2.2 i (Finset.mem_Icc.1 hi).1 (by have := (Finset.mem_Icc.1 hi).2; omega))`. Use the proof step `(by rw [q2]; exact q4) R`.

Rewrite `this` using `[q2, q3]`. Use `le_trans this ?_` and prove the remaining obligations. Rewrite using `[hδ, hI, he1]`. Establish `h2 : CT * ((D.r : ℝ) + 1) * (CT / Th) ^ D.f ≤ |CT| * ((D.r : ℝ) + 1) * (|CT| / Th) ^ D.f`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[abs_mul, abs_mul, abs_pow, abs_div, abs_of_pos hTh0, abs_of_nonneg (by linarith : (0:ℝ) ≤ (D.r : ℝ) + 1)]`. Apply `mul_le_mul_of_nonneg_right _ hjn` to reduce the goal to its premises. Apply `mul_le_mul_of_nonneg_right _ (le_trans zero_le_one (le_max_right _ _))` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key : B.c0 * B.c0' * B.KV ≤ (1 + B.δ) * B.e1 * (B.n0c * B.IntN)`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩` from `hMassData`. Establish `hmain` using `hFM hMT P { B with Kgs2 := B.tt * B.Gam1 * B.Sig } b1 he1p w5 (le_refl _) b2 b3 key b4 b5 b6 b7 b8 b9 b10 b11 b12 b13`. Establish `hGS : B.tt * B.Gam1 * B.Sig ≤ (1 + B.δ) * B.e1 * B.tt * (B.d * B.d' / B.Dstar)`. Establish `h1` using `hmain.1`.

Establish `h2` using `hmain.2.1`. Rewrite `h2` using `[h1]`. Conclude with `h2`. Establish `htt : 0 < B.tt`. Unfold `S3.MassData.tt`.

Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `p _`. Use `(b1.1 p).1` as an intermediate fact. Check the signs of the components of the expression. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `: B.tt * (B.Gam1 * B.Sig) ≤ B.tt * ((1 + B.δ) * B.e1 * (B.d * B.d' / B.Dstar))`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_of_mul_le_mul_left this htt`. Rewrite using `[hδ]`. Check the signs of the components of the expression.

Rewrite using `[hδ, hr, hf]`. Conclude with `s5`. Rewrite using `[he1]`. Conclude with `le_max_right _ _`. Rewrite using `[he1]; exact max_le hsdE (Real.one_le_exp (by positivity))`.
-/
theorem t_MainRow : MainRow := by
  intro hLC hGC _hLL hAx h13s C₄ Cthr h4
  have hLC2 := hLC
  obtain ⟨hA, hSch, hPD, hDS, hDP, hBD, hPL, hSO, hPh, hOS, hOD, hLP, hUH, hTP, hTU, hGL, hUM, hAS,
    hAF, hKL, hLK, hDM, hDA, hA2, hKG, hN0, hN1P, hTh1, h1, hNsS, hNsB, hLA⟩ := hLC
  obtain ⟨hTA, hRW, hDST, hSBM, hRST, hDSum, hDL2, hDSz, hDC, hPT, hPJ, hPSJ, hBox, hLat, hId, hNorm,
    hDeg, hFP, hX, hLSJ, hIS, hILS, hSz, hSR, hGP, hMT, hFM⟩ := hGC
  have hLem : A5.LemmaA := hLA hA2 hN1P hTh1 h1 h13s hN0 hNsS hNsB
  have h13 : ∀ s, 1 ≤ s → A5.A13 s := hLem.2.1
  obtain ⟨C₁, hC1, hIL⟩ := hILS hLSJ hIS hBox hLat hId hNorm hDeg hFP hX
  obtain ⟨CT, CT', hT⟩ := hRW hTA C₁ C₄ hC1 h4
  refine ⟨max (max Cthr 1) |CT|, |CT|, le_trans (le_max_left _ _) (le_max_left _ _),
    le_trans (le_max_right _ _) (le_max_left _ _), abs_nonneg _, le_max_right _ _, ?_⟩
  intro C0 CG CDel cT Cb hC0 hCG hCDel hcT hCb hcTb
  obtain ⟨k1, hk1⟩ := hSR hSz (max (max Cthr 1) |CT|) C0 CG CDel cT Cb |CT| CT'
    (le_trans (le_max_right _ _) (le_max_left _ _)) hC0 hCG hCDel hcT hCb hcTb (abs_nonneg _)
    (le_max_right _ _)
  obtain ⟨k3, hk3⟩ := hGP CDel Cb hCDel hCb
  refine ⟨max k1 k3, ?_⟩
  intro E W _ _ _ D e G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf hU hInst hLM jn H _ _ _ Vt c
    sd hReal hDens P _ B hRows hMassData hEL
  obtain ⟨hI, he1, hδ⟩ := hEL
  obtain ⟨hg1, hg2, hlen⟩ := hk3 (InfinitePlace E) G bb (le_trans (le_max_right _ _) hk) hyp.1
  obtain ⟨s1, s2, s3, s4, s5⟩ := hk1 (InfinitePlace E) G bb Cp Cf Th de de' T T' du du' l
    (le_trans (le_max_left _ _) hk) hyp h16 hCf
  have hGr : IsGreatest (G.thrSet (max (max Cthr 1) |CT|) de de' T T' l) ((Th ^ G.f)⁻¹) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := hyp
    exact h
  have hCA0 : 0 ≤ max (max Cthr 1) |CT| := le_trans (abs_nonneg _) (le_max_right _ _)
  obtain ⟨hSB, hLS⟩ := hIL E W D e G _ de de' T T' l Th hU hInst hg1 hg2 hCA0 hlen s2 hGr
  have hf : D.f = G.f := by
    have := Fintype.card_congr e
    rw [Fintype.card_fin] at this
    exact this
  have hr : D.r = G.r := hInst.1
  have hf1 : 1 ≤ D.f := by
    obtain ⟨_, d2, d3⟩ := hDeg E
    rw [hf]; unfold Sz.Glob.f; omega
  have hK : 4 ≤ D.K := by rw [hInst.2.1]; norm_num
  have hTh0 : 0 < Th := by linarith
  obtain ⟨hKr, hAxA2, hEB, hDomA⟩ := hAx hLC2 h13 E W D hLM
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := hReal
  have hPS : D.PoissonStep := by
    obtain ⟨V, i1, i2, i3, i4, i5, ι, i6, π, Λ, i7, i8, emb, dmap, hb, hFr, hW⟩ := r4
    exact hPSJ hPT hPJ E W D V ι π hb Λ emb dmap hFr hW
  have hA4 : D.LeadingDomination Vt (fun _ _ => (0 : ℂ)) := by
    refine ⟨fun ρ p h => absurd rfl h, fun Y _ R => ?_, fun ρ => ?_⟩
    · exact Formalism.FourierDecayAlt.P.Jx7.psd_congr (fun x _ y _ => by simp) (hKr (D.r + 1) Y)
    · simp
  have hRec : TC.RecHypAfter D C₁ C₄ Th jn Vt (fun _ _ => (0 : ℂ)) :=
    ⟨hK, hf1, hTh0, hSB, r1, hKr, r2, hAxA2, hEB, hDomA, r3, hPS, r5, r6, hLS, r7, r8, hA4⟩
  obtain ⟨hk5, Pd, q, lq, hq, hcard, hx⟩ := hDens
  obtain ⟨hsdE, hsd2⟩ := hDC hDSum hDL2 hDSz Pd q lq G.k G.r G.f sd hk5 hq hcard hx
  have he0 : D.e (D.r + 1) = 0 := hLM.2.2.2 (D.r + 1) (by omega) le_rfl
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := hRows
  obtain ⟨q1, q2, q3, q4, q5⟩ := hRST hDST hSBM E W D C₁ C₄ Th jn H Vt (fun _ _ => (0 : ℂ)) c sd hsd2
    he0 hRec w1 w2 w3
  have hjn := Formalism.FourierDecayAlt.P.Jx7.jn_nonneg D jn r1 r7
  have habs : (CT / Th) ^ D.f ≤ (|CT| / Th) ^ D.f := by
    calc (CT / Th) ^ D.f ≤ |(CT / Th) ^ D.f| := le_abs_self _
      _ = (|CT| / Th) ^ D.f := by rw [abs_pow, abs_div, abs_of_pos hTh0]
  have hr0 : (0 : ℝ) ≤ D.r := Nat.cast_nonneg _
  have hsm : (D.r : ℝ) * (CT / Th) ^ D.f ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left habs hr0) ?_
    rw [hr, hf]; exact s3
  have he1p : 0 < B.e1 := by rw [he1]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hbound : ∀ R : Finset ℕ, ∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2 ≤ (1 + B.δ) * B.e1 * B.IntN := by
    intro R
    have := hT E W (TC.scaleTop D (max sd 1)) Th jn H Vt c sd q1 s1 (by rw [q2, q3]; exact hsm)
      (fun i hi => by
        rw [q2] at hi
        rw [q5 i hi]
        exact hLM.2.2.2 i (Finset.mem_Icc.1 hi).1 (by have := (Finset.mem_Icc.1 hi).2; omega))
      (by rw [q2]; exact q4) R
    rw [q2, q3] at this
    refine le_trans this ?_
    rw [hδ, hI, he1]
    have h2 : CT * ((D.r : ℝ) + 1) * (CT / Th) ^ D.f ≤
        |CT| * ((D.r : ℝ) + 1) * (|CT| / Th) ^ D.f := by
      calc CT * ((D.r : ℝ) + 1) * (CT / Th) ^ D.f
          ≤ |CT * ((D.r : ℝ) + 1) * (CT / Th) ^ D.f| := le_abs_self _
        _ = |CT| * ((D.r : ℝ) + 1) * (|CT| / Th) ^ D.f := by
            rw [abs_mul, abs_mul, abs_pow, abs_div, abs_of_pos hTh0,
              abs_of_nonneg (by linarith : (0:ℝ) ≤ (D.r : ℝ) + 1)]
    apply mul_le_mul_of_nonneg_right _ hjn
    apply mul_le_mul_of_nonneg_right _ (le_trans zero_le_one (le_max_right _ _))
    linarith
  have key : B.c0 * B.c0' * B.KV ≤ (1 + B.δ) * B.e1 * (B.n0c * B.IntN) := by
    calc B.c0 * B.c0' * B.KV ≤ B.n0c * ((1 + B.δ) * B.e1 * B.IntN) := w4 _ hbound
      _ = _ := by ring
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩ := hMassData
  have hmain := hFM hMT P { B with Kgs2 := B.tt * B.Gam1 * B.Sig } b1 he1p w5 (le_refl _) b2 b3 key b4
    b5 b6 b7 b8 b9 b10 b11 b12 b13
  have hGS : B.tt * B.Gam1 * B.Sig ≤ (1 + B.δ) * B.e1 * B.tt * (B.d * B.d' / B.Dstar) := by
    have h1 := hmain.1
    have h2 := hmain.2.1
    rw [h1] at h2
    exact h2
  have htt : 0 < B.tt := by
    unfold S3.MassData.tt
    apply Finset.prod_pos
    intro p _
    have := (b1.1 p).1
    positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : B.tt * (B.Gam1 * B.Sig) ≤ B.tt * ((1 + B.δ) * B.e1 * (B.d * B.d' / B.Dstar)) := by
      calc B.tt * (B.Gam1 * B.Sig) = B.tt * B.Gam1 * B.Sig := by ring
        _ ≤ _ := hGS
        _ = _ := by ring
    exact le_of_mul_le_mul_left this htt
  · rw [hδ]; positivity
  · rw [hδ, hr, hf]; exact s5
  · rw [he1]; exact le_max_right _ _
  · rw [he1]; exact max_le hsdE (Real.one_le_exp (by positivity))

end Main

section Loops

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB Finset

/- English proof (translation)
Introduce `hND hDS hS0 hGS hB3 C hC`. Take `⟨K1, h1⟩` from `hND C hC`. Take `⟨K2, h2⟩` from `hDS C hC`. Take `⟨K3, h3⟩` from `hS0 C hC`. Use `⟨max K1 (max K2 K3), ?_⟩` and prove the remaining obligations.

Introduce `τ Rw I H H₁ _ _ _ _ _ X k r f A b g v NT Gam Xi dd hA hP hXi hx hdd hIn`. Establish `mono : ∀ K : ℝ, K ≤ max K1 (max K2 K3) → Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K k (2 * r + 2) f b g v NT Gam`. Introduce `K hK`. Take `⟨p1, p2, p3, p4, p5, p6, p7⟩` from `hP`. Use `⟨p1, p2, p3, p4, p5, le_trans ?_ p6, p7⟩` and prove the remaining obligations.

Establish `hl : 0 ≤ Real.log b` using `Real.log_nonneg (by linarith)`. Establish `: 0 ≤ (((2 * r + 2 : ℕ) : ℝ)) ^ 5 * f * Real.log b` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hK this]`. Establish `q1` using `h1 k (2 * r + 2) f b g v NT Gam Xi (mono K1 (le_max_left _ _)) hXi`. Establish `q2` using `h2 k (2 * r + 2) f b g v NT Gam Xi (mono K2 (le_trans (le_max_left _ _) (le_max_right _ _))) hXi`.

Establish `q3` using `h3 k r f b g v NT Gam (mono K3 (le_trans (le_max_right _ _) (le_max_right _ _)))`. Take `⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩` from `hP`. Establish `hk1 : 1 ≤ k` using `by omega`. Establish `q1'` using `le_trans q1 (hGS k f b g hk1 (by linarith) p5)`. Establish `hG : 0 < Gam ^ 2` using `by positivity`.

Establish `q2' : Gam ^ 2 * ∑ s ∈ Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k (2 * r + 2) f s b g v Gam Xi ≤ Real.exp (-((k : ℝ) * f * Real.log k) / 2)`. Combine the equalities or inequalities in the displayed calculation. Establish `q4` using `hB3 A ((k : ℝ) * f * Real.log k) hA hx`. Unfold `Terms.RowLoops`. Use `le_trans hIn ?_` and prove the remaining obligations.

Use `mul_le_mul_of_nonneg_right ?_ hdd` and prove the remaining obligations. Establish `e3 : Real.exp (-((1 / 3 : ℝ) * k * f * Real.log k)) = Real.exp (-((k : ℝ) * f * Real.log k) / 3)` using `by congr 1; ring`. Rewrite using `[e3]`. Use `le_trans ?_ q4` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left ?_ (by linarith)` and prove the remaining obligations.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem t_LoopsJoint : LoopsJoint := by
  intro hND hDS hS0 hGS hB3 C hC
  obtain ⟨K1, h1⟩ := hND C hC
  obtain ⟨K2, h2⟩ := hDS C hC
  obtain ⟨K3, h3⟩ := hS0 C hC
  refine ⟨max K1 (max K2 K3), ?_⟩
  intro τ Rw I H H₁ _ _ _ _ _ X k r f A b g v NT Gam Xi dd hA hP hXi hx hdd hIn
  have mono : ∀ K : ℝ, K ≤ max K1 (max K2 K3) →
      Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K k (2 * r + 2) f b g v NT Gam := by
    intro K hK
    obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hP
    refine ⟨p1, p2, p3, p4, p5, le_trans ?_ p6, p7⟩
    have hl : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
    have : 0 ≤ (((2 * r + 2 : ℕ) : ℝ)) ^ 5 * f * Real.log b := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hK this]
  have q1 := h1 k (2 * r + 2) f b g v NT Gam Xi (mono K1 (le_max_left _ _)) hXi
  have q2 := h2 k (2 * r + 2) f b g v NT Gam Xi
    (mono K2 (le_trans (le_max_left _ _) (le_max_right _ _))) hXi
  have q3 := h3 k r f b g v NT Gam (mono K3 (le_trans (le_max_right _ _) (le_max_right _ _)))
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := hP
  have hk1 : 1 ≤ k := by omega
  have q1' := le_trans q1 (hGS k f b g hk1 (by linarith) p5)
  have hG : 0 < Gam ^ 2 := by positivity
  have q2' : Gam ^ 2 * ∑ s ∈ Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k (2 * r + 2) f s b g v Gam Xi ≤
      Real.exp (-((k : ℝ) * f * Real.log k) / 2) := by
    calc _ ≤ Gam ^ 2 * (Real.exp (-((k : ℝ) * f * Real.log k) / 2) * (Gam ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left q2 hG.le
      _ = _ := by field_simp
  have q4 := hB3 A ((k : ℝ) * f * Real.log k) hA hx
  unfold Terms.RowLoops
  refine le_trans hIn ?_
  refine mul_le_mul_of_nonneg_right ?_ hdd
  have e3 : Real.exp (-((1 / 3 : ℝ) * k * f * Real.log k)) =
      Real.exp (-((k : ℝ) * f * Real.log k) / 3) := by congr 1; ring
  rw [e3]
  refine le_trans ?_ q4
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  linarith

end Loops

section From

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB Finset NumberField

/- English proof (translation)
Introduce `hMR hPB hLC hGC hLL hAx hStep hPBA hPI hEI hPS hSF hNP hNE hND hNL hNN hNGE hEZ C₄ Cthr hC4`. Take `⟨CA, C, h1, h2, h3, h4, hrest⟩` from `hMR hLC hGC hLL hAx hStep C₄ Cthr hC4`. Use `⟨CA, C, h1, h2, h3, h4, ?_⟩` and prove the remaining obligations. Introduce `C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6`. Take `⟨k0, hk⟩` from `hrest C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6`.

Use `⟨k0, ?_⟩` and prove the remaining obligations. Introduce `E W _ _ _ D e G bb Cp Cf Th de de' T T' du du' l hk0 hSz hc hCf hU hInst hLM jn H _ _ _ Vt c sd hRI hDI P _ B hRows hMassData hEL τ Rw I HS H₁ _ _ _ _ _ _ X c5 Cn hLink hSplit hNum hBig hNsc hNG`. Take `⟨m1, m2, m3, m4, m5⟩` from `hk E W D e G bb Cp Cf Th de de' T T' du du' l hk0 hSz hc hCf hU hInst hLM jn H Vt c sd hRI hDI P B hRows hMassData hEL`. Take `⟨lG, lS, ⟨typ, htyp⟩, ld, ld', lD⟩` from `hLink`. Take `⟨s1, s2, s3, s4, s5, s6, _⟩` from `hSplit`.

Establish `htt : B.tt = (1 + 3 / (G.g1 : ℝ)) ^ G.f * (1 + 3 / (G.g2 : ℝ)) ^ G.f`. Unfold `S3.MassData.tt`. Rewrite using `[Fintype.prod_equiv typ (fun p => 1 + 3 / B.g p) (fun x => 1 + 3 / (if x.1 then (G.g1 : ℝ) else (G.g2 : ℝ))) (fun p => by rw [htyp p])]`. Rewrite using `[Fintype.prod_prod_type]`. Simplify using `[Sz.Glob.f, Finset.prod_const, Finset.card_univ]`.

Take `⟨hp, hμKo, _, _, _, _, _, _, _, _, _, _, _, _, _, hvolG, _, _, _, _, _, _, _, _, _, _, hdeg, _, _, _, _, hd, hd', _, _, _⟩` from `hMassData.1`. Establish `hD : 0 < B.Dstar`. Unfold `S3.MassData.Dstar S3.MassData.μKpp`. Establish `: 0 < ∏ p, B.μKppp p` using `Finset.prod_pos (fun p _ => (hp p).2.2.2.2.2.2.2.1)`. Check the signs of the components of the expression.

Establish `hdd : 0 ≤ du * du' / (G.size de T du).Dstar`. Rewrite using `[← lD, ← ld, ← ld']`. Check the signs of the components of the expression. Use `hPB hPBA hPI hEI hPS hSF hNP hNE hND hNL hNN hNGE hEZ τ Rw I HS H₁ X G.k G.r G.f bb G.g1 G.g2 c5 Cn B.δ B.e1 _ hNum hdd m2 m3 (by linarith) m5 s1 s2 (htt ▸ s3) s4 s5 s6 hBig hNsc ?_ hNG` and prove the remaining obligations. Use `show X.pairSum _ ≤ _`.

Rewrite using `[lS, ← lD, ← ld, ← ld']`. Conclude with `m1`.
-/
theorem t_PairBoundFromLocal : PairBoundFromLocal := by
  intro hMR hPB hLC hGC hLL hAx hStep hPBA hPI hEI hPS hSF hNP hNE hND hNL hNN hNGE hEZ C₄ Cthr hC4
  obtain ⟨CA, C, h1, h2, h3, h4, hrest⟩ := hMR hLC hGC hLL hAx hStep C₄ Cthr hC4
  refine ⟨CA, C, h1, h2, h3, h4, ?_⟩
  intro C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6
  obtain ⟨k0, hk⟩ := hrest C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6
  refine ⟨k0, ?_⟩
  intro E W _ _ _ D e G bb Cp Cf Th de de' T T' du du' l hk0 hSz hc hCf hU hInst hLM jn H _ _ _ Vt c sd
    hRI hDI P _ B hRows hMassData hEL τ Rw I HS H₁ _ _ _ _ _ _ X c5 Cn hLink hSplit hNum hBig hNsc hNG
  obtain ⟨m1, m2, m3, m4, m5⟩ := hk E W D e G bb Cp Cf Th de de' T T' du du' l hk0 hSz hc hCf hU hInst hLM
    jn H Vt c sd hRI hDI P B hRows hMassData hEL
  obtain ⟨lG, lS, ⟨typ, htyp⟩, ld, ld', lD⟩ := hLink
  obtain ⟨s1, s2, s3, s4, s5, s6, _⟩ := hSplit
  have htt : B.tt = (1 + 3 / (G.g1 : ℝ)) ^ G.f * (1 + 3 / (G.g2 : ℝ)) ^ G.f := by
    unfold S3.MassData.tt
    rw [Fintype.prod_equiv typ (fun p => 1 + 3 / B.g p)
      (fun x => 1 + 3 / (if x.1 then (G.g1 : ℝ) else (G.g2 : ℝ))) (fun p => by rw [htyp p])]
    rw [Fintype.prod_prod_type]
    simp [Sz.Glob.f, Finset.prod_const, Finset.card_univ]
  obtain ⟨hp, hμKo, _, _, _, _, _, _, _, _, _, _, _, _, _, hvolG, _, _, _, _, _, _, _, _, _, _, hdeg,
    _, _, _, _, hd, hd', _, _, _⟩ := hMassData.1
  have hD : 0 < B.Dstar := by
    unfold S3.MassData.Dstar S3.MassData.μKpp
    have : 0 < ∏ p, B.μKppp p := Finset.prod_pos (fun p _ => (hp p).2.2.2.2.2.2.2.1)
    positivity
  have hdd : 0 ≤ du * du' / (G.size de T du).Dstar := by
    rw [← lD, ← ld, ← ld']; positivity
  refine hPB hPBA hPI hEI hPS hSF hNP hNE hND hNL hNN hNGE hEZ τ Rw I HS H₁ X G.k G.r G.f bb G.g1 G.g2 c5 Cn
    B.δ B.e1 _ hNum hdd m2 m3 (by linarith) m5 s1 s2 (htt ▸ s3) s4 s5 s6 hBig hNsc ?_ hNG
  show X.pairSum _ ≤ _
  rw [lS, ← lD, ← ld, ← ld']
  exact m1

end From

end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_FourParts`.
-/
theorem four_parts : Formalism.FourierDecayAlt.PB.FourParts := GrowthPolynomialOperator.t_FourParts

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_SplitSum`.
-/
theorem split_sum_alt : Formalism.FourierDecayAlt.PB.SplitSum := GrowthPolynomialOperator.t_SplitSum

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_EqualIota`.
-/
theorem equal_index : Formalism.FourierDecayAlt.PB.GramSumLeOfPosSemidef := GrowthPolynomialOperator.t_EqualIota

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_GGNumeric`.
-/
theorem gamma_numeric_bound : Formalism.FourierDecayAlt.PB.GGNumeric := GrowthPolynomialOperator.t_GGNumeric

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_PriceOfIota`.
-/
theorem price_of_index : Formalism.FourierDecayAlt.PB.NormSqBoundOfEqualIota := GrowthPolynomialOperator.t_PriceOfIota

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_PairSplit`.
-/
theorem pair_split_alt : Formalism.FourierDecayAlt.PB.PairSplit := GrowthPolynomialOperator.t_PairSplit

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_SubFamily`.
-/
theorem subfamilyAlt : Formalism.FourierDecayAlt.PB.SubFamily := GrowthPolynomialOperator.t_SubFamily

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_LoopsGiveRows`.
-/
theorem loops_give_series : Formalism.FourierDecayAlt.PB.LoopsGiveRows := GrowthPolynomialOperator.t_LoopsGiveRows

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_NGTotal`.
-/
theorem total_count_bound : Formalism.FourierDecayAlt.PB.NGTotal := GrowthPolynomialOperator.t_NGTotal

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_TextClosing`.
-/
theorem text_closing : Formalism.FourierDecayAlt.PB.NormSqAddBoundBySqrtSum := GrowthPolynomialOperator.t_TextClosing

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_PairBoundAbstract`.
-/
theorem pair_bound_abstract : Formalism.FourierDecayAlt.PB.PairBoundAbstract := GrowthPolynomialOperator.t_PairBoundAbstract

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_NumPrice`.
-/
theorem numerical_price : Formalism.FourierDecayAlt.PB.NumPrice := GrowthPolynomialOperator.t_NumPrice

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_NumExp`.
-/
theorem numerical_exponent : Formalism.FourierDecayAlt.PB.NumExp := GrowthPolynomialOperator.t_NumExp

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_NumDens`.
-/
theorem numerical_density : Formalism.FourierDecayAlt.PB.NumDens := GrowthPolynomialOperator.t_NumDens

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_NumLoops`.
-/
theorem numerical_loops : Formalism.FourierDecayAlt.PB.NumLoops := GrowthPolynomialOperator.t_NumLoops

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_NumNG`.
-/
theorem numerical_count : Formalism.FourierDecayAlt.PB.NumNG := GrowthPolynomialOperator.t_NumNG

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_NGExponent`.
-/
theorem count_exponent : Formalism.FourierDecayAlt.PB.NGExponent := GrowthPolynomialOperator.t_NGExponent

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_EtaZero`.
-/
theorem eta_zero_alt : Formalism.FourierDecayAlt.PB.SqrtSumSqLeOneAddInvPowSix := GrowthPolynomialOperator.t_EtaZero

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_MainRowShape`.
-/
theorem principal_series_shape : Formalism.FourierDecayAlt.PB.MainRowShape := GrowthPolynomialOperator.t_MainRowShape

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_PairBound`.
-/
theorem pair_bound_alt : Formalism.FourierDecayAlt.PB.PairBound := GrowthPolynomialOperator.t_PairBound

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_AxiomsOfLocalModel`.
-/
theorem axioms_of_local_model : Formalism.FourierDecayAlt.PB.AxiomsOfLocalModel := GrowthPolynomialOperator.t_AxiomsOfLocalModel

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_MainRow`.
-/
theorem principal_series : Formalism.FourierDecayAlt.PB.MainRow := GrowthPolynomialOperator.t_MainRow

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_LoopsJoint`.
-/
theorem loops_joint : Formalism.FourierDecayAlt.PB.LoopsJoint := GrowthPolynomialOperator.t_LoopsJoint

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_PairBoundFromLocal`.
-/
theorem pair_bound_from_local : Formalism.FourierDecayAlt.PB.PairBoundFromLocal := GrowthPolynomialOperator.t_PairBoundFromLocal

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_PullLatticeOrdinary`.
-/
theorem pull_lattice_ordinary : Formalism.FourierDecayAlt.PB.PullLatticeOrdinary := GrowthPolynomialOperator.t_PullLatticeOrdinary

/- English proof (translation)
The claim follows from `GrowthPolynomialOperator.t_LatticeLink`.
-/
theorem lattice_link : Formalism.FourierDecayAlt.PB.LatticeLink := GrowthPolynomialOperator.t_LatticeLink

end Formalism.FourierDecayAlt.P
