import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfC
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.BallStein

variable {n : ℕ}

noncomputable def sqd (c : V n) (y : V n) : ℝ := ‖y - c‖ ^ 2

/- English proof (translation)
The claim follows from `(contDiff_norm_sq ℂ).comp (contDiff_id.sub contDiff_const)`.
-/
theorem contDiff_sqd (c : V n) : ContDiff ℝ ∞ (sqd c) :=
  (contDiff_norm_sq ℂ).comp (contDiff_id.sub contDiff_const)

/- English proof (translation)
Establish `h1 : ‖y - c‖ < r` using `by simpa [dist_eq_norm] using hy`. Establish `h0 : 0 ≤ ‖y - c‖` using `norm_nonneg _`. Unfold `sqd`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sqd_lt {c y : V n} {r : ℝ} (hy : y ∈ ball c r) : sqd c y < r ^ 2 := by
  have h1 : ‖y - c‖ < r := by simpa [dist_eq_norm] using hy
  have h0 : 0 ≤ ‖y - c‖ := norm_nonneg _
  unfold sqd
  nlinarith

/- English proof (translation)
Establish `hne : r ^ 2 - t ≠ 0` using `by linarith`. Use `((hasDerivAt_id t).const_sub (r ^ 2)).inv hne` as an intermediate fact. Use `this.congr_deriv ?_` and prove the remaining obligations. Simplify using `only [id]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_k (r t : ℝ) (ht : t < r ^ 2) :
    HasDerivAt (fun t : ℝ => (r ^ 2 - t)⁻¹) (((r ^ 2 - t) ^ 2)⁻¹) t := by
  have hne : r ^ 2 - t ≠ 0 := by linarith
  have := ((hasDerivAt_id t).const_sub (r ^ 2)).inv hne
  refine this.congr_deriv ?_
  simp only [id]
  ring

/- English proof (translation)
Establish `hne : (r ^ 2 - t) ^ 2 ≠ 0`. Establish `: r ^ 2 - t ≠ 0` using `by linarith`. Check the signs of the components of the expression. Establish `h1` using `(((hasDerivAt_id t).const_sub (r ^ 2)).pow 2).inv hne`. Use `h1.congr_deriv ?_` and prove the remaining obligations.

Simplify using `only [id, Pi.pow_apply]`. Evaluate the numerical expressions.
-/
theorem hasDerivAt_k' (r t : ℝ) (ht : t < r ^ 2) :
    HasDerivAt (fun t : ℝ => ((r ^ 2 - t) ^ 2)⁻¹) (2 * (r ^ 2 - t) / ((r ^ 2 - t) ^ 2) ^ 2) t := by
  have hne : (r ^ 2 - t) ^ 2 ≠ 0 := by
    have : r ^ 2 - t ≠ 0 := by linarith
    positivity
  have h1 := (((hasDerivAt_id t).const_sub (r ^ 2)).pow 2).inv hne
  refine h1.congr_deriv ?_
  simp only [id, Pi.pow_apply]
  norm_num

/- English proof (translation)
The claim follows from `(hasDerivAt_k r t ht).deriv`.
-/
theorem deriv_k (r t : ℝ) (ht : t < r ^ 2) :
    deriv (fun t : ℝ => (r ^ 2 - t)⁻¹) t = ((r ^ 2 - t) ^ 2)⁻¹ :=
  (hasDerivAt_k r t ht).deriv

/- English proof (translation)
Establish `hev : deriv (fun t : ℝ => (r ^ 2 - t)⁻¹) =ᶠ[𝓝 t] fun t : ℝ => ((r ^ 2 - t) ^ 2)⁻¹` using `by filter_upwards [Iio_mem_nhds ht] with u hu`. Conclude with `deriv_k r u hu`. Rewrite using `[hev.deriv_eq]`. Conclude with `(hasDerivAt_k' r t ht).deriv`.
-/
theorem deriv_deriv_k (r t : ℝ) (ht : t < r ^ 2) :
    deriv (deriv (fun t : ℝ => (r ^ 2 - t)⁻¹)) t = 2 * (r ^ 2 - t) / ((r ^ 2 - t) ^ 2) ^ 2 := by
  have hev : deriv (fun t : ℝ => (r ^ 2 - t)⁻¹) =ᶠ[𝓝 t] fun t : ℝ => ((r ^ 2 - t) ^ 2)⁻¹ := by
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact deriv_k r u hu
  rw [hev.deriv_eq]
  exact (hasDerivAt_k' r t ht).deriv

/- English proof (translation)
Set `u : Fin n → V n → ℝ` to `fun j y => Complex.normSq (EuclideanSpace.proj j (y - c))`. Establish `hfun : (fun y => ((sqd c y : ℝ) : ℂ)) = fun y => ((∑ j, u j y : ℝ) : ℂ)`. Use function extensionality and compare the values at `y`. Use `congr 1`. Simplify using `only [sqd, u, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]`.

Both sides reduce to the same expression. Establish `hg : ∀ j : Fin n, ContDiffAt ℂ 2 (fun y : V n => EuclideanSpace.proj j (y - c)) x` using `fun j => ((EuclideanSpace.proj j : V n →L[ℂ] ℂ).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt`. Establish `hu : ∀ j, ContDiffAt ℝ 2 (u j) x` using `fun j => by`. Establish `hu' : u j = fun y => ‖EuclideanSpace.proj j (y - c)‖ ^ 2`. Use function extensionality and compare the values at `y`.

Simplify using `only [u, Complex.normSq_eq_norm_sq]`. Rewrite using `[hu']`. Conclude with `(contDiff_norm_sq ℂ).contDiffAt.comp x ((hg j).restrict_scalars ℝ)`. Rewrite using `[hfun, leviV_ofReal_sum hu, Complex.re_sum]`. Conclude with `Finset.sum_nonneg fun j _ => ((logPshAt_normSq (hg j)).2 ξ).1`.
-/
theorem leviV_sqd_nonneg (c x : V n) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun y => ((sqd c y : ℝ) : ℂ)) x ξ).re := by
  let u : Fin n → V n → ℝ := fun j y => Complex.normSq (EuclideanSpace.proj j (y - c))
  have hfun : (fun y => ((sqd c y : ℝ) : ℂ)) = fun y => ((∑ j, u j y : ℝ) : ℂ) := by
    funext y
    congr 1
    simp only [sqd, u, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]
    rfl
  have hg : ∀ j : Fin n, ContDiffAt ℂ 2 (fun y : V n => EuclideanSpace.proj j (y - c)) x := fun j =>
    ((EuclideanSpace.proj j : V n →L[ℂ] ℂ).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hu : ∀ j, ContDiffAt ℝ 2 (u j) x := fun j => by
    have hu' : u j = fun y => ‖EuclideanSpace.proj j (y - c)‖ ^ 2 := by
      funext y; simp only [u, Complex.normSq_eq_norm_sq]
    rw [hu']
    exact (contDiff_norm_sq ℂ).contDiffAt.comp x ((hg j).restrict_scalars ℝ)
  rw [hfun, leviV_ofReal_sum hu, Complex.re_sum]
  exact Finset.sum_nonneg fun j _ => ((logPshAt_normSq (hg j)).2 ξ).1

end GlobalTheory.BallStein

namespace GlobalTheory.BallStein

variable {n : ℕ}

noncomputable def exh (c : V n) (r : ℝ) (y : V n) : ℝ := (r ^ 2 - sqd c y)⁻¹

/- English proof (translation)
The claim follows from `(contDiffOn_const.sub (contDiff_sqd c).contDiffOn).inv fun _ hy => (sub_pos.2 (sqd_lt hy)).ne'`.
-/
theorem contDiffOn_exh (c : V n) (r : ℝ) : ContDiffOn ℝ ∞ (exh c r) (ball c r) :=
  (contDiffOn_const.sub (contDiff_sqd c).contDiffOn).inv fun _ hy => (sub_pos.2 (sqd_lt hy)).ne'

/- English proof (translation)
Establish `hlt` using `sqd_lt hy`. Establish `hp : 0 < r ^ 2 - sqd c y` using `sub_pos.2 hlt`. Establish `hk : ContDiffAt ℝ 2 (fun t : ℝ => (r ^ 2 - t)⁻¹) (sqd c y)` using `(contDiffAt_const.sub contDiffAt_id).inv hp.ne'`. Establish `hc` using `leviChain n (fun t : ℝ => (r ^ 2 - t)⁻¹) (sqd c) y ξ (((contDiff_norm_sq ℂ).comp (contDiff_id.sub contDiff_const) : ContDiff ℝ 2 (sqd c)).contDiffAt) hk`. Establish `he : (fun w => ((exh c r w : ℝ) : ℂ)) = fun w => (((fun t : ℝ => (r ^ 2 - t)⁻¹) (sqd c w) : ℝ) : ℂ)` using `rfl`.

Rewrite using `[he, hc, deriv_k r _ hlt, deriv_deriv_k r _ hlt]`. Simplify using `only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]`. Establish `h1` using `leviV_sqd_nonneg c y ξ`. Establish `h2` using `Complex.normSq_nonneg (∑ j, wd n j (fun w => ((sqd c w : ℝ) : ℂ)) y * ξ j)`. Use `add_nonneg (mul_nonneg (by positivity) h1) (mul_nonneg (by positivity) h2)` and prove the remaining obligations.
-/
theorem leviV_exh_nonneg {c y : V n} {r : ℝ} (hy : y ∈ ball c r) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun w => ((exh c r w : ℝ) : ℂ)) y ξ).re := by
  have hlt := sqd_lt hy
  have hp : 0 < r ^ 2 - sqd c y := sub_pos.2 hlt
  have hk : ContDiffAt ℝ 2 (fun t : ℝ => (r ^ 2 - t)⁻¹) (sqd c y) :=
    (contDiffAt_const.sub contDiffAt_id).inv hp.ne'
  have hc := leviChain n (fun t : ℝ => (r ^ 2 - t)⁻¹) (sqd c) y ξ
    (((contDiff_norm_sq ℂ).comp (contDiff_id.sub contDiff_const) : ContDiff ℝ 2 (sqd c)).contDiffAt) hk
  have he : (fun w => ((exh c r w : ℝ) : ℂ)) =
      fun w => (((fun t : ℝ => (r ^ 2 - t)⁻¹) (sqd c w) : ℝ) : ℂ) := rfl
  rw [he, hc, deriv_k r _ hlt, deriv_deriv_k r _ hlt]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
  have h1 := leviV_sqd_nonneg c y ξ
  have h2 := Complex.normSq_nonneg (∑ j, wd n j (fun w => ((sqd c w : ℝ) : ℂ)) y * ξ j)
  refine add_nonneg (mul_nonneg (by positivity) h1) (mul_nonneg (by positivity) h2)

/- English proof (translation)
Distinguish the cases in `hr : r ≤ 0`. Establish `: {y | y ∈ ball c r ∧ exh c r y ≤ a} = ∅`. Use extensionality with `y`. Simplify using `[Metric.ball_eq_empty.2 hr]`. Rewrite using `[this]`.

Conclude with `isCompact_empty`. Use `push_neg at hr`. Distinguish the cases in `ha : a ≤ 0`. Establish `: {y | y ∈ ball c r ∧ exh c r y ≤ a} = ∅`. Use extensionality with `y`.

Simplify using `only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]`. Introduce `hy`. Establish `hp : 0 < r ^ 2 - sqd c y` using `sub_pos.2 (sqd_lt hy)`. Conclude with `lt_of_le_of_lt ha (inv_pos.2 hp)`. Rewrite using `[this]`.

Conclude with `isCompact_empty`. Use `push_neg at ha`. Establish `heq : {y | y ∈ ball c r ∧ exh c r y ≤ a} = {y | sqd c y ≤ r ^ 2 - a⁻¹}`. Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, exh]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hy, hle⟩`. Establish `hp : 0 < r ^ 2 - sqd c y` using `sub_pos.2 (sqd_lt hy)`. Use `(inv_le_comm₀ hp ha).1 hle` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `hle`. Establish `hai : 0 < a⁻¹` using `inv_pos.2 ha`. Establish `hp : 0 < r ^ 2 - sqd c y` using `by linarith`. Use `⟨?_, (inv_le_comm₀ hp ha).2 (by linarith)⟩` and prove the remaining obligations. Rewrite using `[mem_ball, dist_eq_norm]`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `: r ^ 2 ≤ sqd c y` using `by unfold sqd; nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[heq]`.

Use `Metric.isCompact_of_isClosed_isBounded (isClosed_le (contDiff_sqd c).continuous continuous_const) ?_` and prove the remaining obligations. Use `(Metric.isBounded_closedBall (x := c) (r := r)).subset fun y hy => ?_` and prove the remaining obligations. Establish `hai : 0 < a⁻¹` using `inv_pos.2 ha`. Establish `h1 : sqd c y ≤ r ^ 2` using `by simp only [Set.mem_setOf_eq] at hy; linarith`. Rewrite using `[mem_closedBall, dist_eq_norm]`.

Unfold `sqd at h1`. Use polynomial arithmetic with `[norm_nonneg (y - c)]`.
-/
theorem isCompact_exh (c : V n) (r a : ℝ) : IsCompact {y | y ∈ ball c r ∧ exh c r y ≤ a} := by
  by_cases hr : r ≤ 0
  · have : {y | y ∈ ball c r ∧ exh c r y ≤ a} = ∅ := by
      ext y; simp [Metric.ball_eq_empty.2 hr]
    rw [this]; exact isCompact_empty
  push_neg at hr
  by_cases ha : a ≤ 0
  · have : {y | y ∈ ball c r ∧ exh c r y ≤ a} = ∅ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
      intro hy
      have hp : 0 < r ^ 2 - sqd c y := sub_pos.2 (sqd_lt hy)
      exact lt_of_le_of_lt ha (inv_pos.2 hp)
    rw [this]; exact isCompact_empty
  push_neg at ha
  have heq : {y | y ∈ ball c r ∧ exh c r y ≤ a} = {y | sqd c y ≤ r ^ 2 - a⁻¹} := by
    ext y
    simp only [Set.mem_setOf_eq, exh]
    constructor
    · rintro ⟨hy, hle⟩
      have hp : 0 < r ^ 2 - sqd c y := sub_pos.2 (sqd_lt hy)
      have := (inv_le_comm₀ hp ha).1 hle
      linarith
    · intro hle
      have hai : 0 < a⁻¹ := inv_pos.2 ha
      have hp : 0 < r ^ 2 - sqd c y := by linarith
      refine ⟨?_, (inv_le_comm₀ hp ha).2 (by linarith)⟩
      rw [mem_ball, dist_eq_norm]
      by_contra hcon
      push_neg at hcon
      have : r ^ 2 ≤ sqd c y := by unfold sqd; nlinarith
      linarith
  rw [heq]
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (contDiff_sqd c).continuous continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := c) (r := r)).subset fun y hy => ?_
  have hai : 0 < a⁻¹ := inv_pos.2 ha
  have h1 : sqd c y ≤ r ^ 2 := by simp only [Set.mem_setOf_eq] at hy; linarith
  rw [mem_closedBall, dist_eq_norm]
  unfold sqd at h1
  nlinarith [norm_nonneg (y - c)]

/- English proof (translation)
Introduce `n c r`. Establish `hU : IsOpen (ball c r)` using `isOpen_ball`. Use `⟨{ z := Subtype.val isLocalHomeomorph := ReciprocityTheory.ChartRestriction.G.AR.Up.HE.val_lh hU e := fun x => exh c r x.1 smooth_e := ReciprocityTheory.ChartRestriction.G.AR.Up.HE.smoothR_val (contDiffOn_exh c r) levi_e := fun x ξ => by` and prove the remaining obligations. Rewrite using `[ReciprocityTheory.ChartRestriction.G.AR.Up.HE.levi_val hU]`. Conclude with `leviV_exh_nonneg x.2 ξ`.

Use `isCompact_le := fun a => by`. Rewrite using `[Subtype.isCompact_iff]`. Use `isCompact_exh c r a using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨x.2, hx⟩`. Introduce and unpack `⟨hy, hy'⟩`. Conclude with `⟨⟨y, hy⟩, hy', rfl⟩ }, rfl⟩`.
-/
theorem ball_etaleStein : ∀ (n : ℕ) (c : V n) (r : ℝ), ∃ X : EtaleStein n (ball c r), X.z = Subtype.val := by
  intro n c r
  have hU : IsOpen (ball c r) := isOpen_ball
  refine ⟨{ z := Subtype.val
            isLocalHomeomorph := ReciprocityTheory.ChartRestriction.G.AR.Up.HE.val_lh hU
            e := fun x => exh c r x.1
            smooth_e := ReciprocityTheory.ChartRestriction.G.AR.Up.HE.smoothR_val (contDiffOn_exh c r)
            levi_e := fun x ξ => by
              rw [ReciprocityTheory.ChartRestriction.G.AR.Up.HE.levi_val hU]
              exact leviV_exh_nonneg x.2 ξ
            isCompact_le := fun a => by
              rw [Subtype.isCompact_iff]
              convert isCompact_exh c r a using 1
              ext y
              constructor
              · rintro ⟨x, hx, rfl⟩
                exact ⟨x.2, hx⟩
              · rintro ⟨hy, hy'⟩
                exact ⟨⟨y, hy⟩, hy', rfl⟩ }, rfl⟩

end GlobalTheory.BallStein
