import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def doublingIterate (h : E → ℂ) : ℕ → E → ℂ
  | 0 => fun z => h ((2 : ℂ)⁻¹ • z)
  | n + 1 => fun z =>
      3 * doublingIterate h n ((2 : ℂ)⁻¹ • z) + doublingIterate h n (-((2 : ℂ)⁻¹ • z))

/- English proof (translation)
Rewrite using `[norm_smul, norm_inv]`. Simplify using `[div_eq_inv_mul]`.
-/
private theorem norm_half_smul (z : E) : ‖(2 : ℂ)⁻¹ • z‖ = ‖z‖ / 2 := by
  rw [norm_smul, norm_inv]
  simp [div_eq_inv_mul]

/- English proof (translation)
Rewrite `hz`, the goal using `[mem_ball_zero_iff]`. Rewrite using `[norm_half_smul]`. Combine the linear relations using `[norm_nonneg z]`.
-/
private theorem half_mem_ball {r : ℝ} {z : E} (hz : z ∈ Metric.ball (0 : E) r) :
    (2 : ℂ)⁻¹ • z ∈ Metric.ball (0 : E) r := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_half_smul]
  linarith [norm_nonneg z]

/- English proof (translation)
Rewrite `hz`, the goal using `[mem_ball_zero_iff]`. Rewrite using `[norm_neg]` and apply the resulting hypothesis.
-/
private theorem neg_mem_ball' {r : ℝ} {z : E} (hz : z ∈ Metric.ball (0 : E) r) :
    -z ∈ Metric.ball (0 : E) r := by
  rw [mem_ball_zero_iff] at hz ⊢
  rwa [norm_neg]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact hh.comp (by fun_prop) fun z hz => half_mem_ball hz`. Consider the case `succ n ih`. Establish `h1 : DifferentiableOn ℂ (fun z : E => doublingIterate h n ((2 : ℂ)⁻¹ • z)) (Metric.ball 0 r)` using `ih.comp (by fun_prop) fun z hz => half_mem_ball hz`. Establish `h2 : DifferentiableOn ℂ (fun z : E => doublingIterate h n (-((2 : ℂ)⁻¹ • z))) (Metric.ball 0 r)` using `ih.comp (by fun_prop) fun z hz => neg_mem_ball' (half_mem_ball hz)`.

Conclude with `(h1.const_mul 3).add h2`.
-/
theorem differentiableOn_doublingIterate {h : E → ℂ} {r : ℝ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 r)) (n : ℕ) :
    DifferentiableOn ℂ (doublingIterate h n) (Metric.ball 0 r) := by
  induction n with
  | zero => exact hh.comp (by fun_prop) fun z hz => half_mem_ball hz
  | succ n ih =>
    have h1 : DifferentiableOn ℂ (fun z : E => doublingIterate h n ((2 : ℂ)⁻¹ • z))
        (Metric.ball 0 r) := ih.comp (by fun_prop) fun z hz => half_mem_ball hz
    have h2 : DifferentiableOn ℂ (fun z : E => doublingIterate h n (-((2 : ℂ)⁻¹ • z)))
        (Metric.ball 0 r) := ih.comp (by fun_prop) fun z hz => neg_mem_ball' (half_mem_ball hz)
    exact (h1.const_mul 3).add h2

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `z hz`. Establish `h1` using `hh _ (half_mem_ball hz)`. Rewrite `h1` using `[norm_half_smul]`.

Establish `h2 : 0 ≤ C * ‖z‖ ^ 3` using `by positivity`. Express the relevant statement in the definitionally equal form `‖h ((2 : ℂ)⁻¹ • z)‖ ≤ _`. Use the polynomial consequences of the given equalities and inequalities. Consider the case `succ n ih`. Introduce `z hz`.

Establish `h1` using `ih _ (half_mem_ball hz)`. Establish `h2` using `ih _ (neg_mem_ball' (half_mem_ball hz))`. Rewrite `h2` using `[norm_neg]`. Rewrite `h1`, `h2` using `[norm_half_smul]`. Express the relevant statement in the definitionally equal form `‖3 * doublingIterate h n ((2 : ℂ)⁻¹ • z) + doublingIterate h n (-((2 : ℂ)⁻¹ • z))‖ ≤ _`.

Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Establish `h3 : ‖(3 : ℂ)‖ = 3` using `by simp`. Rewrite using `[h3]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_doublingIterate_le {h : E → ℂ} {r C : ℝ} (hC : 0 ≤ C)
    (hh : ∀ z ∈ Metric.ball (0 : E) r, ‖h z‖ ≤ C * ‖z‖ ^ 3) (n : ℕ) :
    ∀ z ∈ Metric.ball (0 : E) r, ‖doublingIterate h n z‖ ≤ (1 / 2) ^ n * (C * ‖z‖ ^ 3) := by
  induction n with
  | zero =>
    intro z hz
    have h1 := hh _ (half_mem_ball hz)
    rw [norm_half_smul] at h1
    have h2 : 0 ≤ C * ‖z‖ ^ 3 := by positivity
    change ‖h ((2 : ℂ)⁻¹ • z)‖ ≤ _
    nlinarith
  | succ n ih =>
    intro z hz
    have h1 := ih _ (half_mem_ball hz)
    have h2 := ih _ (neg_mem_ball' (half_mem_ball hz))
    rw [norm_neg] at h2
    rw [norm_half_smul] at h1 h2
    change ‖3 * doublingIterate h n ((2 : ℂ)⁻¹ • z)
      + doublingIterate h n (-((2 : ℂ)⁻¹ • z))‖ ≤ _
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have h3 : ‖(3 : ℂ)‖ = 3 := by simp
    rw [h3]
    calc _ ≤ 3 * ((1 / 2) ^ n * (C * (‖z‖ / 2) ^ 3)) + (1 / 2) ^ n * (C * (‖z‖ / 2) ^ 3) := by
          gcongr
      _ = _ := by ring

/- English proof (translation)
Take `⟨C, hC, hO⟩` from `hO.exists_nonneg`. Take `⟨r, hr, hball⟩` from `Metric.eventually_nhds_iff_ball.mp (hO.bound.and ha.eventually_analyticAt)`. Establish `hd : DifferentiableOn ℂ h (Metric.ball 0 r)` using `fun z hz => (hball z hz).2.differentiableAt.differentiableWithinAt`. Establish `hb : ∀ z ∈ Metric.ball (0 : E) r, ‖h z‖ ≤ C * ‖z‖ ^ 3` using `fun z hz => by`. Simplify using `using (hball z hz).1`.

Establish `hB` using `norm_doublingIterate_le hC hb`. Establish `hgeom : ∀ c : ℝ, HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n * c) (2 * c)` using `fun c => hasSum_geometric_two.mul_right c`. Establish `hS : ∀ z ∈ Metric.ball (0 : E) r, Summable fun n => doublingIterate h n z` using `fun z hz => Summable.of_norm_bounded (hgeom _).summable fun n => hB n z hz`. Use `⟨fun z => ∑' n, doublingIterate h n z, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `SCV.analyticAt_of_differentiableOn (s := Metric.ball 0 r) (SCV.differentiableOn_tsum_of_locally_normal Metric.isOpen_ball (differentiableOn_doublingIterate hd) fun x hx => ⟨Metric.ball 0 r, Metric.isOpen_ball.mem_nhds hx, _, (hgeom (C * r ^ 3)).summable, fun n z hz => (hB n z hz) …` and prove the remaining obligations.

Use `(mem_ball_zero_iff.mp hz).le` as an intermediate fact. Use `gcongr`. Use `Asymptotics.IsBigO.of_bound (2 * C) ?_ filter_upwards [Metric.ball_mem_nhds 0 hr] with z hz` and prove the remaining obligations. Use `(tsum_of_norm_bounded (hgeom _) fun n => hB n z hz).trans_eq ?_` and prove the remaining obligations. Simplify using `[mul_assoc]`.

Use `filter_upwards [Metric.ball_mem_nhds (0 : E) (half_pos hr)] with z hz`. Rewrite `hz` using `[mem_ball_zero_iff]`. Establish `hz1 : z ∈ Metric.ball (0 : E) r`. Rewrite using `[mem_ball_zero_iff]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hz2 : (2 : ℂ) • z ∈ Metric.ball (0 : E) r`. Rewrite using `[mem_ball_zero_iff, norm_smul]`. Establish `: ‖(2 : ℂ)‖ = 2` using `by simp`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e : (2 : ℂ)⁻¹ • (2 : ℂ) • z = z` using `inv_smul_smul₀ two_ne_zero z`. Rewrite using `[(hS _ hz2).tsum_eq_zero_add]`. Simplify using `only [doublingIterate, e]`. Rewrite using `[((hS z hz1).mul_left 3).tsum_add (hS _ (neg_mem_ball' hz1)), tsum_mul_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_doubling_solution [FiniteDimensional ℂ E] (h : E → ℂ) (ha : AnalyticAt ℂ h 0)
    (hO : h =O[𝓝 0] (fun z => ‖z‖ ^ 3)) :
    ∃ k : E → ℂ, AnalyticAt ℂ k 0 ∧ k =O[𝓝 0] (fun z => ‖z‖ ^ 3) ∧
      ∀ᶠ z in 𝓝 0, k ((2 : ℂ) • z) - 3 * k z - k (-z) = h z := by
  obtain ⟨C, hC, hO⟩ := hO.exists_nonneg
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hO.bound.and ha.eventually_analyticAt)
  have hd : DifferentiableOn ℂ h (Metric.ball 0 r) :=
    fun z hz => (hball z hz).2.differentiableAt.differentiableWithinAt
  have hb : ∀ z ∈ Metric.ball (0 : E) r, ‖h z‖ ≤ C * ‖z‖ ^ 3 := fun z hz => by
    simpa using (hball z hz).1
  have hB := norm_doublingIterate_le hC hb
  have hgeom : ∀ c : ℝ, HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n * c) (2 * c) :=
    fun c => hasSum_geometric_two.mul_right c
  have hS : ∀ z ∈ Metric.ball (0 : E) r, Summable fun n => doublingIterate h n z :=
    fun z hz => Summable.of_norm_bounded (hgeom _).summable fun n => hB n z hz
  refine ⟨fun z => ∑' n, doublingIterate h n z, ?_, ?_, ?_⟩
  · refine SCV.analyticAt_of_differentiableOn (s := Metric.ball 0 r)
      (SCV.differentiableOn_tsum_of_locally_normal Metric.isOpen_ball
        (differentiableOn_doublingIterate hd) fun x hx =>
          ⟨Metric.ball 0 r, Metric.isOpen_ball.mem_nhds hx, _, (hgeom (C * r ^ 3)).summable,
            fun n z hz => (hB n z hz).trans ?_⟩) (Metric.ball_mem_nhds 0 hr)
    have := (mem_ball_zero_iff.mp hz).le
    gcongr
  · refine Asymptotics.IsBigO.of_bound (2 * C) ?_
    filter_upwards [Metric.ball_mem_nhds 0 hr] with z hz
    refine (tsum_of_norm_bounded (hgeom _) fun n => hB n z hz).trans_eq ?_
    simp [mul_assoc]
  · filter_upwards [Metric.ball_mem_nhds (0 : E) (half_pos hr)] with z hz
    rw [mem_ball_zero_iff] at hz
    have hz1 : z ∈ Metric.ball (0 : E) r := by
      rw [mem_ball_zero_iff]
      linarith
    have hz2 : (2 : ℂ) • z ∈ Metric.ball (0 : E) r := by
      rw [mem_ball_zero_iff, norm_smul]
      have : ‖(2 : ℂ)‖ = 2 := by simp
      rw [this]
      linarith
    have e : (2 : ℂ)⁻¹ • (2 : ℂ) • z = z := inv_smul_smul₀ two_ne_zero z
    rw [(hS _ hz2).tsum_eq_zero_add]
    simp only [doublingIterate, e]
    rw [((hS z hz1).mul_left 3).tsum_add (hS _ (neg_mem_ball' hz1)), tsum_mul_left]
    ring

end

/- English proof (translation)
Introduce `_ h ha hO` and use `exists_doubling_solution h ha hO`.
-/
theorem exists_doubling_solution_pi :
    ∀ (g : ℕ) (h : (Fin g → ℂ) → ℂ), AnalyticAt ℂ h 0 → h =O[𝓝 0] (fun z => ‖z‖ ^ 3) →
      ∃ k : (Fin g → ℂ) → ℂ, AnalyticAt ℂ k 0 ∧ k =O[𝓝 0] (fun z => ‖z‖ ^ 3) ∧
        ∀ᶠ z in 𝓝 0, k ((2 : ℂ) • z) - 3 * k z - k (-z) = h z :=
  fun _ h ha hO => exists_doubling_solution h ha hO

end GlobalTheory
