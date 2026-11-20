import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvNegLogMvMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralSubst
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.ExpLogShift

open MvPowerSeries

/- English proof (translation)
Introduce `p _ g h n hE hh`. Establish `hh' : MvPowerSeries.constantCoeff (h : MvPowerSeries Unit ℂ_[p]) = 0` using `hh`. Establish `hX : MvPowerSeries.constantCoeff (GL3Theta.Xv () : MvPowerSeries Unit ℂ_[p]) = 0`. Simplify using `[GL3Theta.Xv]`. Establish `ha : MvPowerSeries.constantCoeff (g.phAt (h : MvPowerSeries Unit ℂ_[p])) = 0` using `GlobalTheory.CurveToStdLog.cc_phAt g hE hh'`.

Establish `hb : MvPowerSeries.constantCoeff (g.phAt (GL3Theta.Xv () : MvPowerSeries Unit ℂ_[p])) = 0` using `GlobalTheory.CurveToStdLog.cc_phAt g hE hX`. Use `⟨by simp [map_sub, map_mul, ha, hb], ?_⟩` and prove the remaining obligations. Use `set b : MvPowerSeries Unit ℂ_[p] := g.phAt (GL3Theta.Xv ()) with hbdef`. Use `set F : PowerSeries ℂ_[p] := ePhi1 g.lam g.abelian₂ g.C g.wq with hF`. Establish `hbph : b = (g.ph : MvPowerSeries Unit ℂ_[p])` using `by show PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[p]) g.ph = g.ph`.

Rewrite using `[← PowerSeries.map_algebraMap_eq_subst_X]`. Simplify using the standard rewrite rules. Establish `hbF : expMv b * (F : MvPowerSeries Unit ℂ_[p]) = 1`. Rewrite using `[hbph]`. Conclude with `(GlobalTheory.ExpLogMv.expMv_neg_logMv_mul p Unit _ hE).2`.

Establish `hnb : MvPowerSeries.constantCoeff (-b) = 0` using `by simp [hb]`. Establish `hneg : expMv (-b) = (F : MvPowerSeries Unit ℂ_[p])`. Establish `h0 : expMv b * expMv (-b) = 1`. Rewrite using `[← GlobalTheory.CurveToStdLog.expMv_add hb hnb, add_neg_cancel, GlobalTheory.CurveToStdLog.expMv_zero]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hsum : (g.phAt (h : MvPowerSeries Unit ℂ_[p])) - MvPowerSeries.C (n : ℂ_[p]) * b = g.phAt (h : MvPowerSeries Unit ℂ_[p]) + ∑ _i ∈ Finset.range n, -b`. Rewrite using `[Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_eq_add_neg, ← neg_mul]`. Use `congr 1`. Rewrite using `[neg_mul, mul_neg]`. Use `congr 1`.

Establish `hsum0 : MvPowerSeries.constantCoeff (∑ _i ∈ Finset.range n, -b) = 0`. Rewrite using `[map_sum]`. Simplify using `[hb]`. Rewrite using `[hsum, GlobalTheory.CurveToStdLog.expMv_add ha hsum0, GlobalTheory.CurveToStdLog.expMv_sum _ (fun _ => hnb), Finset.prod_const, Finset.card_range, hneg, ← GlobalTheory.CurveToStdLog.inv_ePhi1 g hE hh']`.
-/
theorem expMv_phAt_sub_nsmul : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (h : PowerSeries ℂ_[p]) (n : ℕ), PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 → PowerSeries.constantCoeff h = 0 → MvPowerSeries.constantCoeff ((g.phAt h : MvPowerSeries Unit ℂ_[p]) - MvPowerSeries.C (n : ℂ_[p]) * g.phAt (GL3Theta.Xv ())) = 0 ∧ expMv ((g.phAt h : MvPowerSeries Unit ℂ_[p]) - MvPowerSeries.C (n : ℂ_[p]) * g.phAt (GL3Theta.Xv ())) = ((PowerSeries.subst h (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq ^ n : PowerSeries ℂ_[p]) := by
  intro p _ g h n hE hh
  have hh' : MvPowerSeries.constantCoeff (h : MvPowerSeries Unit ℂ_[p]) = 0 := hh
  have hX : MvPowerSeries.constantCoeff (GL3Theta.Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := by
    simp [GL3Theta.Xv]
  have ha : MvPowerSeries.constantCoeff (g.phAt (h : MvPowerSeries Unit ℂ_[p])) = 0 :=
    GlobalTheory.CurveToStdLog.cc_phAt g hE hh'
  have hb : MvPowerSeries.constantCoeff (g.phAt (GL3Theta.Xv () : MvPowerSeries Unit ℂ_[p])) = 0 :=
    GlobalTheory.CurveToStdLog.cc_phAt g hE hX
  refine ⟨by simp [map_sub, map_mul, ha, hb], ?_⟩
  set b : MvPowerSeries Unit ℂ_[p] := g.phAt (GL3Theta.Xv ()) with hbdef
  set F : PowerSeries ℂ_[p] := ePhi1 g.lam g.abelian₂ g.C g.wq with hF

  have hbph : b = (g.ph : MvPowerSeries Unit ℂ_[p]) := by
    show PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[p]) g.ph = g.ph
    rw [← PowerSeries.map_algebraMap_eq_subst_X]; simp

  have hbF : expMv b * (F : MvPowerSeries Unit ℂ_[p]) = 1 := by
    rw [hbph]; exact (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul p Unit _ hE).2
  have hnb : MvPowerSeries.constantCoeff (-b) = 0 := by simp [hb]

  have hneg : expMv (-b) = (F : MvPowerSeries Unit ℂ_[p]) := by
    have h0 : expMv b * expMv (-b) = 1 := by
      rw [← GlobalTheory.CurveToStdLog.expMv_add hb hnb, add_neg_cancel, GlobalTheory.CurveToStdLog.expMv_zero]
    calc expMv (-b) = expMv (-b) * (expMv b * (F : MvPowerSeries Unit ℂ_[p])) := by rw [hbF, mul_one]
      _ = (expMv b * expMv (-b)) * F := by ring
      _ = F := by rw [h0, one_mul]
  have hsum : (g.phAt (h : MvPowerSeries Unit ℂ_[p])) - MvPowerSeries.C (n : ℂ_[p]) * b =
      g.phAt (h : MvPowerSeries Unit ℂ_[p]) + ∑ _i ∈ Finset.range n, -b := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_eq_add_neg, ← neg_mul]
    congr 1
    rw [neg_mul, mul_neg]
    congr 1
  have hsum0 : MvPowerSeries.constantCoeff (∑ _i ∈ Finset.range n, -b) = 0 := by
    rw [map_sum]; simp [hb]
  rw [hsum, GlobalTheory.CurveToStdLog.expMv_add ha hsum0,
    GlobalTheory.CurveToStdLog.expMv_sum _ (fun _ => hnb), Finset.prod_const, Finset.card_range, hneg,
    ← GlobalTheory.CurveToStdLog.inv_ePhi1 g hE hh']

end GlobalTheory.ExpLogShift
