import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmR
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta

namespace GlobalTheory.CompanionTheory.CenTheta

/- English proof (translation)
Establish `ha : 0 < |(a : ℝ)|` using `abs_pos.mpr a.ne_zero`. Establish `hq : (((|(a : ℝ)| : ℝ) : ℂ)) / ((‖(((|(a : ℝ)| : ℝ) : ℂ))‖ : ℝ) : ℂ) = 1`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs, abs_abs]`. Conclude with `div_self (Complex.ofReal_ne_zero.mpr ha.ne')`. Establish `hpos : (0 : ℝ) < ‖(((|(a : ℝ)| : ℝ) : ℂ))‖ ^ 2`.

Rewrite using `[Complex.norm_real, Real.norm_eq_abs, abs_abs]`. Check the signs of the components of the expression. Establish `hch : ‖chC n (Complex.I * t) (Units.mk0 ((|(a : ℝ)| : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr a.ne_zero)))‖ = 1`. Unfold `chC`. Simplify using `only [Units.val_mk0]`.

Rewrite using `[hq, one_zpow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]`. Simplify using the standard rewrite rules. Establish `hsg : ‖sgR (a : ℝ)‖ = 1`. Unfold `sgR`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hs : ‖(if 0 < (a : ℝ) then 1 else (-1 : ℂ) ^ n)‖ = 1` using `by split_ifs`. Simplify using the standard rewrite rules. Rewrite using `[norm_zpow]`. Simplify using the standard rewrite rules. Unfold `omR`.

Rewrite using `[norm_mul, norm_mul, hch, hsg, hs]`. Simplify using the standard rewrite rules.
-/
theorem norm_omR (n : ℤ) (t : ℝ) (a : ℝˣ) : ‖omR n t a‖ = 1 := by
  have ha : 0 < |(a : ℝ)| := abs_pos.mpr a.ne_zero
  have hq : (((|(a : ℝ)| : ℝ) : ℂ)) / ((‖(((|(a : ℝ)| : ℝ) : ℂ))‖ : ℝ) : ℂ) = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_abs]
    exact div_self (Complex.ofReal_ne_zero.mpr ha.ne')
  have hpos : (0 : ℝ) < ‖(((|(a : ℝ)| : ℝ) : ℂ))‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_abs]
    positivity
  have hch : ‖chC n (Complex.I * t) (Units.mk0 ((|(a : ℝ)| : ℝ) : ℂ)
      (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr a.ne_zero)))‖ = 1 := by
    unfold chC
    simp only [Units.val_mk0]
    rw [hq, one_zpow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp
  have hsg : ‖sgR (a : ℝ)‖ = 1 := by
    unfold sgR
    split_ifs <;> simp
  have hs : ‖(if 0 < (a : ℝ) then 1 else (-1 : ℂ) ^ n)‖ = 1 := by
    split_ifs
    · simp
    · rw [norm_zpow]; simp
  unfold omR
  rw [norm_mul, norm_mul, hch, hsg, hs]
  simp

end GlobalTheory.CompanionTheory.CenTheta
