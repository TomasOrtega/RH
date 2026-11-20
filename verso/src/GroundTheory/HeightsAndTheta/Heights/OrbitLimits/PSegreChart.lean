import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChart
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartIntegral
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre isOpen_blockNonzero)

def expLine {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (v : ((Σ k, ι k) → ℂ) → ℝ) (hv : IsDegZeroSmooth v) : HermLine ι :=
  HermLine.ofWeight (fun z => -v z) fun c z hc => by rw [hv.2 c z hc]

/- English proof (translation)
Use function extensionality and compare the values at `j z`. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Simplify using `[pot, expLine, HermLine.ofWeight]`. Simplify using `[pot]`.
-/
theorem pot_cons_expLine {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {n : ℕ}
    (v : ((Σ k, ι k) → ℂ) → ℝ) (hv : IsDegZeroSmooth v) (L : Fin n → HermLine ι) :
    pot (Fin.cons (expLine v hv) L : Fin (n + 1) → HermLine ι) = Fin.cons v (pot L) := by
  funext j z
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [pot, expLine, HermLine.ofWeight]
  · simp [pot]

/- English proof (translation)
Introduce `j`. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Conclude with `Real.contDiff_exp.comp_contDiffOn hv.1.neg.neg`. Simplify using `using hL j`.
-/
theorem isSmoothHerm_cons_expLine {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {n : ℕ}
    (v : ((Σ k, ι k) → ℂ) → ℝ) (hv : IsDegZeroSmooth v) (L : Fin n → HermLine ι)
    (hL : ∀ j, IsSmoothHerm (L j)) :
    ∀ j, IsSmoothHerm ((Fin.cons (expLine v hv) L : Fin (n + 1) → HermLine ι) j) := by
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact Real.contDiff_exp.comp_contDiffOn hv.1.neg.neg
  · simpa using hL j

/- English proof (translation)
Introduce `K _ _ ι _ P n L u v i δ hP hL hu hv hδ hsupp`. Set `σ` to `(Fintype.equivFin ((k : K) → ι k)).symm`. Set `lam` to `chartLift σ i`. Set `χ : ContDiffBump (0 : Fin (Fintype.card ((k : K) → ι k)) → ℂ)` to `⟨1 / δ + 1, 1 / δ + 2, by positivity, by linarith⟩`. Set `U` to `fun x => χ x * u (lam x)`.

Set `V` to `fun x => v (lam x)`. Set `Φ : Fin n → _` to `fun j x => pot L j (lam x)`. Establish `hlam : ContDiff ℝ ∞ lam` using `contDiff_chartLift σ i`. Set `Ω` to `lam ⁻¹' {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0}`. Establish `hΩ : IsOpen Ω` using `isOpen_blockNonzero.preimage hlam.continuous`.

Establish `hsm : ∀ f : ((Σ k, ι k) → ℂ) → ℝ, ContDiffOn ℝ ∞ f {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0} → ContDiffOn ℝ ∞ (f ∘ lam) Ω` using `fun f hf => hf.comp hlam.contDiffOn fun _ hx => hx`. Establish `hpot : ∀ j, ContDiffOn ℝ ∞ (pot L j) {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0}` using `fun j => (hL j).log fun z hz => ((L j).pos z hz).ne'`. Establish `key : ∀ x ∈ segreChartSet P σ i, U =ᶠ[𝓝 x] u ∘ lam`. Introduce and unpack `_ ⟨z, -, hzi, rfl⟩`. Distinguish the cases in `hr : ‖fun a => segre z (σ a)‖ < 1 / δ + 1`.

Use `filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hr)] with y hy`. Simplify using `[U, χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]`. Establish `hle : ‖fun a => segre z (σ a)‖ ≤ ‖segre z‖` using `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => norm_le_pi_norm (segre z) (σ a)`. Establish `hcont : Continuous fun y => segre (lam y)` using `continuous_pi fun i' => continuous_finsetProd _ fun k _ => (continuous_apply (⟨k, i' k⟩ : Σ k, ι k)).comp hlam.continuous`. Establish `hO : IsOpen {y | ‖segre (lam y) i‖ < δ * ‖segre (lam y)‖}` using `isOpen_lt ((continuous_apply i).comp hcont).norm (continuous_const.mul hcont.norm)`.

Establish `hx : ‖segre (lam fun a => segre z (σ a)) i‖ < δ * ‖segre (lam fun a => segre z (σ a))‖`. Rewrite using `[segre_chartLift σ i z hzi, hzi, norm_one]`. Establish `h1 : 1 / δ < ‖segre z‖` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Use `filter_upwards [hO.mem_nhds hx] with y hy`.

Simplify using `[U, hsupp _ hy]`. Establish `hJ : ∀ J ∈ segreChartComponents P σ i, ComplexSets.zeroSet J ⊆ Ω` using `fun J hJ x hx => chartLift_blockNonzero σ i (chart_coord_eq_one hJ hx)`. Use `⟨Fintype.card ((k : K) → ι k), segreChartComponents P σ i, U, V, Φ, fun J hJs => ⟨(mem_segreChartComponents.1 hJs).1.1, hDim K ι P (n + 1) _ σ i hP J hJs, ⟨Ω, hΩ, hJ J hJs, (χ.contDiff.contDiffOn).mul (hsm u hu.1)⟩, ⟨Ω, hΩ, hJ J hJs, hsm v hv.1⟩, fun j => ⟨Ω, hΩ, hJ J hJs, hsm _ …` and prove the remaining obligations. Rewrite using `[← pot_cons_expLine v hv L]`. Use `hInt K ι P n _ σ i _ u δ U _ hP (isSmoothHerm_cons_expLine v hv L hL) hu hδ (Or.inl hsupp) fun x hx => ⟨key x hx, fun j => EventuallyEq.of_eq ?_⟩` and prove the remaining obligations.

Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Use function extensionality and compare the values at `y`. Simplify using `[V, lam, pot, expLine, HermLine.ofWeight]`. Both sides reduce to the same expression. Rewrite using `[← pot_cons_expLine u hu L]`.

Use `hInt K ι P n _ σ i _ v δ V _ hP (isSmoothHerm_cons_expLine u hu L hL) hv hδ (Or.inr fun z hz => by rw [pot_cons_expLine u hu L]; exact hsupp z hz) fun x hx => ⟨EventuallyEq.rfl, fun j => ?_⟩` and prove the remaining obligations. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Establish `h0 : pot (Fin.cons (expLine u hu) L : Fin (n + 1) → HermLine ι) 0 = u`. Rewrite using `[pot_cons_expLine u hu L]`. Both sides reduce to the same expression.

Simplify `key x hx` using `[h0]`. Conclude with `EventuallyEq.rfl`.
-/
theorem SegreChart.proof (hDim : SegreChartDim.Statement) (hInt : SegreChartIntegral.Statement) :
    SegreChart.Statement := by
  classical
  intro K _ _ ι _ P n L u v i δ hP hL hu hv hδ hsupp
  let σ := (Fintype.equivFin ((k : K) → ι k)).symm
  let lam := chartLift σ i
  let χ : ContDiffBump (0 : Fin (Fintype.card ((k : K) → ι k)) → ℂ) :=
    ⟨1 / δ + 1, 1 / δ + 2, by positivity, by linarith⟩
  let U := fun x => χ x * u (lam x)
  let V := fun x => v (lam x)
  let Φ : Fin n → _ := fun j x => pot L j (lam x)
  have hlam : ContDiff ℝ ∞ lam := contDiff_chartLift σ i

  let Ω := lam ⁻¹' {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0}
  have hΩ : IsOpen Ω := isOpen_blockNonzero.preimage hlam.continuous
  have hsm : ∀ f : ((Σ k, ι k) → ℂ) → ℝ, ContDiffOn ℝ ∞ f {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0} →
      ContDiffOn ℝ ∞ (f ∘ lam) Ω := fun f hf => hf.comp hlam.contDiffOn fun _ hx => hx
  have hpot : ∀ j, ContDiffOn ℝ ∞ (pot L j) {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0} := fun j =>
    (hL j).log fun z hz => ((L j).pos z hz).ne'

  have key : ∀ x ∈ segreChartSet P σ i, U =ᶠ[𝓝 x] u ∘ lam := by
    rintro _ ⟨z, -, hzi, rfl⟩
    by_cases hr : ‖fun a => segre z (σ a)‖ < 1 / δ + 1
    · filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hr)] with y hy
      simp [U, χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]
    · have hle : ‖fun a => segre z (σ a)‖ ≤ ‖segre z‖ :=
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => norm_le_pi_norm (segre z) (σ a)
      have hcont : Continuous fun y => segre (lam y) :=
        continuous_pi fun i' => continuous_finsetProd _ fun k _ =>
          (continuous_apply (⟨k, i' k⟩ : Σ k, ι k)).comp hlam.continuous
      have hO : IsOpen {y | ‖segre (lam y) i‖ < δ * ‖segre (lam y)‖} :=
        isOpen_lt ((continuous_apply i).comp hcont).norm (continuous_const.mul hcont.norm)
      have hx : ‖segre (lam fun a => segre z (σ a)) i‖ < δ * ‖segre (lam fun a => segre z (σ a))‖ := by
        rw [segre_chartLift σ i z hzi, hzi, norm_one]
        have h1 : 1 / δ < ‖segre z‖ := by linarith
        calc (1 : ℝ) = δ * (1 / δ) := by field_simp
          _ < δ * ‖segre z‖ := mul_lt_mul_of_pos_left h1 hδ
      filter_upwards [hO.mem_nhds hx] with y hy
      simp [U, hsupp _ hy]
  have hJ : ∀ J ∈ segreChartComponents P σ i, ComplexSets.zeroSet J ⊆ Ω := fun J hJ x hx =>
    chartLift_blockNonzero σ i (chart_coord_eq_one hJ hx)
  refine ⟨Fintype.card ((k : K) → ι k), segreChartComponents P σ i, U, V, Φ,
    fun J hJs => ⟨(mem_segreChartComponents.1 hJs).1.1,
      hDim K ι P (n + 1) _ σ i hP J hJs,
      ⟨Ω, hΩ, hJ J hJs, (χ.contDiff.contDiffOn).mul (hsm u hu.1)⟩,
      ⟨Ω, hΩ, hJ J hJs, hsm v hv.1⟩, fun j => ⟨Ω, hΩ, hJ J hJs, hsm _ (hpot j)⟩⟩,
    χ.hasCompactSupport.mul_right, ?_, ?_⟩
  · rw [← pot_cons_expLine v hv L]
    refine hInt K ι P n _ σ i _ u δ U _ hP (isSmoothHerm_cons_expLine v hv L hL) hu hδ (Or.inl hsupp)
      fun x hx => ⟨key x hx, fun j => EventuallyEq.of_eq ?_⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · funext y; simp [V, lam, pot, expLine, HermLine.ofWeight]
    · rfl
  · rw [← pot_cons_expLine u hu L]
    refine hInt K ι P n _ σ i _ v δ V _ hP (isSmoothHerm_cons_expLine u hu L hL) hv hδ
      (Or.inr fun z hz => by rw [pot_cons_expLine u hu L]; exact hsupp z hz)
      fun x hx => ⟨EventuallyEq.rfl, fun j => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · have h0 : pot (Fin.cons (expLine u hu) L : Fin (n + 1) → HermLine ι) 0 = u := by
        rw [pot_cons_expLine u hu L]; rfl
      simpa [h0] using key x hx
    · exact EventuallyEq.rfl

end GroundTheory.Heights₂.Heights
