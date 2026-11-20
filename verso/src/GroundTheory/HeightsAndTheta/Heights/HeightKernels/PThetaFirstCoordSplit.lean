import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsTheta
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ThetaGauss
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordFirst
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

namespace KThetaFirstCoordSplit

/- English proof (translation)
Use `set v := intVec k + (a + u₁) with hv`. Establish `hassoc : intVec k + a + u₁ = v` using `add_assoc _ _ _`. Rewrite using `[hassoc]`. Use `set δ := Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) with hδ`. Establish `hδ0 : 0 ≤ δ` using `Metric.infDist_nonneg`.

Establish `hv0 : v 0 = (k 0 : ℝ) + (a 0 + u₁ 0)` using `by simp [hv, intVec]`. Establish `hδle : δ ≤ |v 0|`. Establish `h` using `Metric.infDist_le_dist_of_mem (x := u₁ 0 + a 0) (Set.mem_range_self (f := ((↑) : ℤ → ℝ)) (-(k 0)))`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Real.dist_eq, hv0]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hδsq : δ ^ 2 ≤ v 0 ^ 2`. Rewrite using `[← sq_abs (v 0)]`.

Conclude with `pow_le_pow_left₀ hδ0 hδle 2`. Establish `hcoord : v 0 ^ 2 ≤ ρ ^ 2 * qf Y v`. Use `KCoord.sq_coord_le Y hY 0 v` as an intermediate fact. Rewrite `this` using `[hρY]`. Then use the resulting hypothesis. Establish `hρ2 : 0 < ρ ^ 2` using `by positivity`.

Establish `hkey : δ ^ 2 / ρ ^ 2 ≤ qf Y v`. Rewrite using `[div_le_iff₀ hρ2]`. Combine the linear relations using `[mul_comm (ρ ^ 2) (qf Y v)]`. Establish `hexp : exp (-(π / 2) * qf Y v) ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2)`. Apply `exp_le_exp.2` to reduce the goal to its premises.

Establish `h1 : (π / (2 * ρ ^ 2)) * δ ^ 2 = (π / 2) * (δ ^ 2 / ρ ^ 2)`. Clear the denominators using the available nonvanishing facts. Establish `h2 : (π / 2) * (δ ^ 2 / ρ ^ 2) ≤ (π / 2) * qf Y v` using `mul_le_mul_of_nonneg_left hkey (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsplit : exp (-π * qf Y v) = exp (-(π / 2) * qf Y v) * exp (-(π / 2) * qf Y v)`.

Rewrite using `[← exp_add]`. Put the polynomial expressions in normal form. Rewrite using `[hsplit]`. Conclude with `mul_le_mul_of_nonneg_right hexp (exp_pos _).le`.
-/
theorem term_le {g : ℕ} [NeZero g] (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ) (a u₁ : Fin g → ℝ)
    (hY : Y.PosDef) (hρ : 0 < ρ) (hρY : Y⁻¹ 0 0 = ρ ^ 2) (k : Fin g → ℤ) :
    exp (-π * qf Y (intVec k + a + u₁)) ≤
      exp (-(π / (2 * ρ ^ 2)) * Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) ^ 2) *
        exp (-(π / 2) * qf Y (intVec k + (a + u₁))) := by
  set v := intVec k + (a + u₁) with hv
  have hassoc : intVec k + a + u₁ = v := add_assoc _ _ _
  rw [hassoc]
  set δ := Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) with hδ
  have hδ0 : 0 ≤ δ := Metric.infDist_nonneg
  have hv0 : v 0 = (k 0 : ℝ) + (a 0 + u₁ 0) := by simp [hv, intVec]
  have hδle : δ ≤ |v 0| := by
    have h := Metric.infDist_le_dist_of_mem (x := u₁ 0 + a 0)
      (Set.mem_range_self (f := ((↑) : ℤ → ℝ)) (-(k 0)))
    refine h.trans (le_of_eq ?_)
    rw [Real.dist_eq, hv0]
    congr 1
    push_cast
    ring
  have hδsq : δ ^ 2 ≤ v 0 ^ 2 := by
    rw [← sq_abs (v 0)]
    exact pow_le_pow_left₀ hδ0 hδle 2
  have hcoord : v 0 ^ 2 ≤ ρ ^ 2 * qf Y v := by
    have := KCoord.sq_coord_le Y hY 0 v
    rwa [hρY] at this
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hkey : δ ^ 2 / ρ ^ 2 ≤ qf Y v := by
    rw [div_le_iff₀ hρ2]
    linarith [mul_comm (ρ ^ 2) (qf Y v)]
  have hexp : exp (-(π / 2) * qf Y v) ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) := by
    apply exp_le_exp.2
    have h1 : (π / (2 * ρ ^ 2)) * δ ^ 2 = (π / 2) * (δ ^ 2 / ρ ^ 2) := by
      field_simp
    have h2 : (π / 2) * (δ ^ 2 / ρ ^ 2) ≤ (π / 2) * qf Y v :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    linarith
  have hsplit : exp (-π * qf Y v) = exp (-(π / 2) * qf Y v) * exp (-(π / 2) * qf Y v) := by
    rw [← exp_add]
    ring_nf
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hexp (exp_pos _).le

end KThetaFirstCoordSplit

/- English proof (translation)
Introduce `g _ Y ρ a u₁ hY hρ hρY`. Establish `hs1 : Summable fun k : Fin g → ℤ => exp (-π * qf Y (intVec k + a + u₁))`. Use `KTheta.summable_exp_qf Y hY π pi_pos (a + u₁)` as an intermediate fact. Simplify `this` using `only [add_assoc]`. Establish `hs2 : Summable fun k : Fin g → ℤ => exp (-(π / 2) * qf Y (intVec k + (a + u₁)))` using `KTheta.summable_exp_qf Y hY (π / 2) (by positivity) (a + u₁)`.

Rewrite using `[← tsum_mul_left]`. Conclude with `Summable.tsum_le_tsum (fun k => KThetaFirstCoordSplit.term_le Y ρ a u₁ hY hρ hρY k) hs1 (hs2.mul_left _)`.
-/
theorem ThetaFirstCoordSplit.proof : ThetaFirstCoordSplit.Statement := by
  intro g _ Y ρ a u₁ hY hρ hρY
  have hs1 : Summable fun k : Fin g → ℤ => exp (-π * qf Y (intVec k + a + u₁)) := by
    have := KTheta.summable_exp_qf Y hY π pi_pos (a + u₁)
    simpa only [add_assoc] using this
  have hs2 : Summable fun k : Fin g → ℤ => exp (-(π / 2) * qf Y (intVec k + (a + u₁))) :=
    KTheta.summable_exp_qf Y hY (π / 2) (by positivity) (a + u₁)
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum
    (fun k => KThetaFirstCoordSplit.term_le Y ρ a u₁ hY hρ hρY k) hs1 (hs2.mul_left _)

end GroundTheory.Heights₂.Heights
