import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjRegular
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjMaxRankRegular
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

namespace ProjMaxRankRegular

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fderiv_ratios_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {κ τ : Type*}
    [Fintype κ] [Fintype τ] {F : E → κ → ℂ} {u : E} (hF : DifferentiableAt ℂ F u) (a : τ → κ)
    (b : κ) (hb : F u b ≠ 0) (v : E) (t : τ) :
    fderiv ℂ (fun w t => F w (a t) / F w b) u v t =
      (F u b * fderiv ℂ F u v (a t) - F u (a t) * fderiv ℂ F u v b) / F u b ^ 2 := by
  have hc : ∀ k, HasFDerivAt (fun w => F w k)
      ((ContinuousLinearMap.proj k).comp (fderiv ℂ F u)) u :=
    fun k => hasFDerivAt_pi'.1 hF.hasFDerivAt k
  have hq : ∀ t, HasFDerivAt (fun w => F w (a t) / F w b)
      (F u (a t) • (ContinuousLinearMap.toSpanSingleton ℂ (-(F u b ^ 2)⁻¹)).comp
          ((ContinuousLinearMap.proj b).comp (fderiv ℂ F u)) +
        (F u b)⁻¹ • (ContinuousLinearMap.proj (a t)).comp (fderiv ℂ F u)) u := by
    intro t
    have h := (hc (a t)).fun_mul ((hasFDerivAt_inv hb).comp u (hc b))
    simp only [Function.comp_def] at h
    simpa only [div_eq_mul_inv] using h
  rw [(hasFDerivAt_pi.2 hq).fderiv]
  simp
  field_simp
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Take a linear combination of the given relations to obtain the conclusion.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem proof : ProjMaxRankRegular.Statement := by
  intro K _ ι _ P J n R Ψ V BV hB y hy h0
  obtain ⟨i, hi, j, hj, hrank⟩ := hy
  have hsx : (BV.chart j).symm (BV.chart j y) = y := (BV.chart j).left_inv hj
  have hFd : DifferentiableAt ℂ (fun u => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)))
      (BV.chart j y) := (ProjRegular.proj_analyticAt Ψ hB y hj).differentiableAt
  have hF0 : Ψ (segre (R.lift y.1 ((BV.chart j).symm (BV.chart j y)).1)) 0 ≠ 0 := by
    rw [hsx]; exact h0
  have hFi : Ψ (segre (R.lift y.1 ((BV.chart j).symm (BV.chart j y)).1)) i ≠ 0 := by
    rw [hsx]; exact hi

  have hkerA : LinearMap.ker (fderiv ℂ
      (fun u (l : Fin (n + 1)) => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) l /
        Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) i) (BV.chart j y) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) = ⊥ := by
    have h := LinearMap.finrank_range_add_finrank_ker (fderiv ℂ
      (fun u (l : Fin (n + 1)) => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) l /
        Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) i) (BV.chart j y) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    rw [hrank, Module.finrank_fin_fun] at h
    exact Submodule.finrank_eq_zero.mp (by omega)

  have hG : (projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm =ᶠ[𝓝 (BV.chart j y)]
      fun u (l : Fin n) => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) (Fin.succ l) /
        Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) 0 := by
    filter_upwards [(ProjRegular.lift_analyticAt hB y hj).2] with u hu
    exact ProjRegular.projCoord_eq Ψ hu
  refine ⟨h0, fun k hk => ProjRegular.det_ne_zero_of_chart Ψ hB y h0 hk hj ?_⟩
  rw [hG.fderiv_eq]
  set F' := fderiv ℂ (fun u => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1))) (BV.chart j y)
  set Fu := Ψ (segre (R.lift y.1 ((BV.chart j).symm (BV.chart j y)).1))
  have hker : LinearMap.ker (fderiv ℂ (fun u (l : Fin n) =>
      Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) (Fin.succ l) /
        Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) 0) (BV.chart j y) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have hv' : ∀ l : Fin n, Fu 0 * F' v l.succ = Fu l.succ * F' v 0 := by
      intro l
      have h := congrFun hv l
      simp only [ContinuousLinearMap.coe_coe, Pi.zero_apply] at h
      rw [fderiv_ratios_apply hFd Fin.succ 0 hF0] at h
      rw [div_eq_zero_iff] at h
      rcases h with h | h
      · linear_combination h
      · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hF0
    have hall : ∀ m : Fin (n + 1), Fu 0 * F' v m = Fu m * F' v 0 :=
      Fin.cases (by ring) hv'
    have hA : v ∈ LinearMap.ker (fderiv ℂ
        (fun u (l : Fin (n + 1)) => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) l /
          Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) i) (BV.chart j y) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) := by
      rw [LinearMap.mem_ker]
      funext m
      simp only [ContinuousLinearMap.coe_coe, Pi.zero_apply]
      rw [fderiv_ratios_apply hFd (fun l => l) i hFi]
      have h1 : Fu i * F' v m - Fu m * F' v i = 0 := by
        apply mul_left_cancel₀ hF0
        linear_combination Fu i * hall m - Fu m * hall i
      rw [h1, zero_div]
    rw [hkerA] at hA
    exact hA
  exact ((LinearMap.isUnit_iff_isUnit_det _).1
    ((LinearMap.isUnit_iff_ker_eq_bot _).2 hker)).ne_zero

end ProjMaxRankRegular

end GroundTheory.Heights₂.Heights.Targets
