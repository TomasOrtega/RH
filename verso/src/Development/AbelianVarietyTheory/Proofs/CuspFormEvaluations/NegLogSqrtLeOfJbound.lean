import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

/- English proof (translation)
Introduce `E _ _ _ X dg n P S tableLineDegreeFive cc hS hP14 hcc`. Establish `hf : 0 < I2.PT.f E`. Establish `h1` using `P.hfr`. Break down `Nat.eq_zero_or_pos (I2.PT.f E) with h | h` into its components or cases. Rewrite `h1` using `[h]`.

Simplify using `at h1`. Conclude with `h`. Establish `hdp : 0 < I2.dstar (E` using `E) P.m := Nat.mul_pos (Nat.mul_pos two_pos hf) P.hm1`. Establish `hd0 : (1 : ℝ) ≤ (I2.dstar (E` using `E) P.m : ℝ) := by exact_mod_cast hdp`. Establish `hd : (0 : ℝ) < 2 * (I2.dstar (E` using `E) P.m : ℝ) := by linarith`.

Establish `hB` using `Real.rpow_pos_of_pos hd ((I2.dstar (E := E) P.m : ℝ) / 2)`. Establish `h6 : (0 : ℝ) < 6 * (2 * (I2.dstar (E` using `E) P.m : ℝ)) ^ ((I2.dstar (E := E) P.m : ℝ) / 2) := mul_pos (by norm_num) hB`. Establish `hph : 0 ≤ P.ph`. Unfold `I2.Par.ph I2.PT.ph`. Apply the tactic sequence `split_ifs <;> positivity`.

Establish `hA : (4 : ℝ)⁻¹ ^ n ≠ 0` using `by positivity`. Establish `hBn : (6 * (2 * (I2.dstar (E` using `E) P.m : ℝ)) ^ ((I2.dstar (E := E) P.m : ℝ) / 2))⁻¹ ^ n ≠ 0 := pow_ne_zero _ (inv_ne_zero h6.ne')`. Establish `hC : (2 : ℝ)⁻¹ ^ ((X.r + 2) * dg) ≠ 0` using `by positivity`. Establish `hJpos : 0 < P.Jbound n`. Unfold `I2.Par.Jbound`.

Conclude with `mul_pos (mul_pos (mul_pos (pow_pos (by norm_num) _) (pow_pos (inv_pos.2 h6) _)) (pow_pos (by norm_num) _)) (Real.exp_pos _)`. Establish `hJ : Real.log (P.Jbound n) = -(n * Real.log 4) - n * (Real.log 6 + (I2.dstar (E` using `E) P.m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) P.m : ℝ))) - (((X.r + 2) * dg : ℕ) : ℝ) * Real.log 2 - 2 * (8100 * Real.pi * n * (P.m : ℝ) ^ 4 * (I2.dstar (E := E) P.m : ℝ) ^ 4 * I2.RR (E := E) / P.q * P.ph) := by`. Unfold `I2.Par.Jbound`. Rewrite using `[Real.log_mul (mul_ne_zero (mul_ne_zero hA hBn) hC) (Real.exp_pos _).ne', Real.log_mul (mul_ne_zero hA hBn) hC, Real.log_mul hA hBn, Real.log_exp, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_inv, Real.log_inv, Real.log_inv, Real.log_mul (by norm_num) hB.ne', Real.log_rpow …`. Unfold `I2.Cchi`.

Expand and normalize the polynomial expressions, which then agree. Establish `hdg : (1 : ℝ) ≤ dg` using `by exact_mod_cast P.hDF`. Establish `h24 : Real.log 24 = Real.log 4 + Real.log 6`. Rewrite using `[← Real.log_mul (by norm_num) (by norm_num)]; norm_num`. Establish `hl2d : 0 ≤ Real.log (2 * (I2.dstar (E` using `E) P.m : ℝ)) := Real.log_nonneg (by linarith)`.

Establish `hT : 0 ≤ Real.log 24 + (I2.dstar (E` using `E) P.m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) P.m : ℝ)) := by`. Establish `: 0 < Real.log 24` using `Real.log_pos (by norm_num)`. Establish `: 0 ≤ (I2.dstar (E` using `E) P.m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) P.m : ℝ)) := by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpi : (0 : ℝ) < (Real.pi⁻¹) ^ dg` using `pow_pos (inv_pos.2 Real.pi_pos) _`.

Establish `hpos : 0 < (Real.pi⁻¹) ^ dg * P.Jbound n` using `mul_pos hpi hJpos`. Establish `hlS` using `Real.log_le_log hpos hS`. Rewrite `hlS` using `[Real.log_mul hpi.ne' hJpos.ne', Real.log_pow, Real.log_inv, hJ]`. Rewrite using `[Real.log_sqrt (hpos.le.trans hS)]`. Establish `e2` using `mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hT) (sub_nonneg.2 hdg)`.

Establish `e3` using `mul_le_mul_of_nonneg_right hcc hph`. Establish `e4` using `mul_le_mul_of_nonneg_right hP14 (by linarith : (0 : ℝ) ≤ dg)`. Unfold `p14 at e4`. Move the coercions through the operations in `at hlS`. Rewrite `e2`, `e4` using `[h24]`.

Combine the linear relations using `[e2, e3, e4]`.
-/
theorem neg_log_sqrt_le_of_jbound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : I2.PT E) (dg n : ℕ) (P : I2.Par X dg) (S tableLineDegreeFive cc : ℝ), (Real.pi⁻¹) ^ dg * P.Jbound n ≤ S → p14 E X.r n P.m ≤ tableLineDegreeFive → 8100 * Real.pi * n * (P.m : ℝ) ^ 4 * (I2.dstar (E := E) P.m : ℝ) ^ 4 * I2.RR (E := E) / P.q ≤ cc → -Real.log (Real.sqrt S) ≤ tableLineDegreeFive * dg + cc * P.ph := by
  intro E _ _ _ X dg n P S tableLineDegreeFive cc hS hP14 hcc
  have hf : 0 < I2.PT.f E := by
    have h1 := P.hfr
    rcases Nat.eq_zero_or_pos (I2.PT.f E) with h | h
    · rw [h] at h1; simp at h1
    · exact h
  have hdp : 0 < I2.dstar (E := E) P.m := Nat.mul_pos (Nat.mul_pos two_pos hf) P.hm1
  have hd0 : (1 : ℝ) ≤ (I2.dstar (E := E) P.m : ℝ) := by exact_mod_cast hdp
  have hd : (0 : ℝ) < 2 * (I2.dstar (E := E) P.m : ℝ) := by linarith
  have hB := Real.rpow_pos_of_pos hd ((I2.dstar (E := E) P.m : ℝ) / 2)
  have h6 : (0 : ℝ) < 6 * (2 * (I2.dstar (E := E) P.m : ℝ)) ^ ((I2.dstar (E := E) P.m : ℝ) / 2) :=
    mul_pos (by norm_num) hB
  have hph : 0 ≤ P.ph := by
    unfold I2.Par.ph I2.PT.ph
    split_ifs <;> positivity
  have hA : (4 : ℝ)⁻¹ ^ n ≠ 0 := by positivity
  have hBn : (6 * (2 * (I2.dstar (E := E) P.m : ℝ)) ^ ((I2.dstar (E := E) P.m : ℝ) / 2))⁻¹ ^ n ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero h6.ne')
  have hC : (2 : ℝ)⁻¹ ^ ((X.r + 2) * dg) ≠ 0 := by positivity
  have hJpos : 0 < P.Jbound n := by
    unfold I2.Par.Jbound
    exact mul_pos (mul_pos (mul_pos (pow_pos (by norm_num) _) (pow_pos (inv_pos.2 h6) _))
      (pow_pos (by norm_num) _)) (Real.exp_pos _)
  have hJ : Real.log (P.Jbound n) = -(n * Real.log 4) -
      n * (Real.log 6 + (I2.dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) P.m : ℝ))) -
      (((X.r + 2) * dg : ℕ) : ℝ) * Real.log 2 -
      2 * (8100 * Real.pi * n * (P.m : ℝ) ^ 4 * (I2.dstar (E := E) P.m : ℝ) ^ 4 * I2.RR (E := E) / P.q * P.ph) := by
    unfold I2.Par.Jbound
    rw [Real.log_mul (mul_ne_zero (mul_ne_zero hA hBn) hC) (Real.exp_pos _).ne',
      Real.log_mul (mul_ne_zero hA hBn) hC, Real.log_mul hA hBn, Real.log_exp, Real.log_pow,
      Real.log_pow, Real.log_pow, Real.log_inv, Real.log_inv, Real.log_inv,
      Real.log_mul (by norm_num) hB.ne', Real.log_rpow hd]
    unfold I2.Cchi
    ring
  have hdg : (1 : ℝ) ≤ dg := by exact_mod_cast P.hDF
  have h24 : Real.log 24 = Real.log 4 + Real.log 6 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hl2d : 0 ≤ Real.log (2 * (I2.dstar (E := E) P.m : ℝ)) := Real.log_nonneg (by linarith)
  have hT : 0 ≤ Real.log 24 + (I2.dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) P.m : ℝ)) := by
    have : 0 < Real.log 24 := Real.log_pos (by norm_num)
    have : 0 ≤ (I2.dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) P.m : ℝ)) := by positivity
    linarith
  have hpi : (0 : ℝ) < (Real.pi⁻¹) ^ dg := pow_pos (inv_pos.2 Real.pi_pos) _
  have hpos : 0 < (Real.pi⁻¹) ^ dg * P.Jbound n := mul_pos hpi hJpos
  have hlS := Real.log_le_log hpos hS
  rw [Real.log_mul hpi.ne' hJpos.ne', Real.log_pow, Real.log_inv, hJ] at hlS
  rw [Real.log_sqrt (hpos.le.trans hS)]
  have e2 := mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hT) (sub_nonneg.2 hdg)
  have e3 := mul_le_mul_of_nonneg_right hcc hph
  have e4 := mul_le_mul_of_nonneg_right hP14 (by linarith : (0 : ℝ) ≤ dg)
  unfold p14 at e4
  push_cast at hlS
  rw [h24] at e2 e4
  linarith [e2, e3, e4]

end GlobalTheory.AnVal
