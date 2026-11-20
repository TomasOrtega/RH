import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit

open PositivityTheory.RgEis PositivityTheory.RgEis.TF

noncomputable section

namespace GlobalTheory.CompanionTheory.TestBump

variable {ι : Type} [Fintype ι]

def nsq (y : ι → ℂ) : ℝ := ∑ j, ‖y j‖ ^ 2

/- English proof (translation)
The claim follows from `(contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i)`.
-/
lemma contDiff_coordSq (i : ι) {n : WithTop ℕ∞} : ContDiff ℝ n fun y : ι → ℂ => ‖y i‖ ^ 2 :=
  (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i)

/- English proof (translation)
The claim follows from `ContDiff.sum fun j _ => contDiff_coordSq j`.
-/
lemma contDiff_nsq {n : WithTop ℕ∞} : ContDiff ℝ n (nsq : (ι → ℂ) → ℝ) :=
  ContDiff.sum fun j _ => contDiff_coordSq j

/- English proof (translation)
The claim follows from `Finset.single_le_sum (f := fun j => ‖y j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)`.
-/
lemma coordSq_le_nsq (y : ι → ℂ) (i : ι) : ‖y i‖ ^ 2 ≤ nsq y :=
  Finset.single_le_sum (f := fun j => ‖y j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)

/- English proof (translation)
Simplify using `only [nsq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]`.
-/
lemma nsq_smul (t : ℂ) (v : ι → ℂ) : nsq (t • v) = ‖t‖ ^ 2 * nsq v := by
  simp only [nsq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

def radial : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/- English proof (translation)
The claim follows from `radial.one_of_mem_closedBall (Metric.mem_closedBall_self radial.rIn_pos.le)`.
-/
lemma radial_one : radial 1 = 1 :=
  radial.one_of_mem_closedBall (Metric.mem_closedBall_self radial.rIn_pos.le)

/- English proof (translation)
Use `radial.zero_of_le_dist ?_` and prove the remaining obligations. Rewrite using `[Real.dist_eq, abs_of_nonpos (by linarith)]`. Express the relevant statement in the definitionally equal form `(1 / 2 : ℝ) ≤ _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma radial_zero_of_le {x : ℝ} (h : x ≤ 1 / 2) : radial x = 0 := by
  refine radial.zero_of_le_dist ?_
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  change (1 / 2 : ℝ) ≤ _
  linarith

/- English proof (translation)
Use `radial.zero_of_le_dist ?_` and prove the remaining obligations. Rewrite using `[Real.dist_eq, abs_of_nonneg (by linarith)]`. Express the relevant statement in the definitionally equal form `(1 / 2 : ℝ) ≤ _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma radial_zero_of_ge {x : ℝ} (h : 3 / 2 ≤ x) : radial x = 0 := by
  refine radial.zero_of_le_dist ?_
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  change (1 / 2 : ℝ) ≤ _
  linarith

def angular {δ : ℝ} (hδ : 0 < δ) : ContDiffBump (1 : ℝ) :=
  ⟨δ / 2, δ, by positivity, by linarith⟩

/- English proof (translation)
The claim follows from `(angular hδ).one_of_mem_closedBall (Metric.mem_closedBall_self (angular hδ).rIn_pos.le)`.
-/
lemma angular_one {δ : ℝ} (hδ : 0 < δ) : angular hδ 1 = 1 :=
  (angular hδ).one_of_mem_closedBall (Metric.mem_closedBall_self (angular hδ).rIn_pos.le)

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Use `h ((angular hδ).zero_of_le_dist ?_)` and prove the remaining obligations. Rewrite using `[Real.dist_eq, abs_of_nonpos (by linarith [not_lt.1 hx])]`. Express the relevant statement in the definitionally equal form `δ ≤ _`. Combine the linear relations using `[not_lt.1 hx]`.
-/
lemma lt_of_angular_ne {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (h : angular hδ x ≠ 0) : 1 - δ < x := by
  by_contra hx
  refine h ((angular hδ).zero_of_le_dist ?_)
  rw [Real.dist_eq, abs_of_nonpos (by linarith [not_lt.1 hx])]
  change δ ≤ _
  linarith [not_lt.1 hx]

def bigF (i₀ : ι) {δ : ℝ} (hδ : 0 < δ) (y : ι → ℂ) : ℝ :=
  radial (nsq y) * angular hδ (‖y i₀‖ ^ 2 / nsq y)

def smallF (t : ℂ) : ℝ := radial (‖t‖ ^ 2)

/- English proof (translation)
Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `y`. Distinguish the cases in `h : 0 < nsq y`. Conclude with `(radial.contDiff.contDiffAt.comp y contDiff_nsq.contDiffAt).mul ((angular hδ).contDiff.contDiffAt.comp y ((contDiff_coordSq i₀).contDiffAt.div contDiff_nsq.contDiffAt h.ne'))`. Establish `h0 : nsq y < 1 / 2` using `by linarith [not_lt.1 h]`.

Use `(contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [(contDiff_nsq (n := 0)).continuous.continuousAt.eventually (gt_mem_nhds h0)] with z hz`. Simplify using `[bigF, radial_zero_of_le (le_of_lt hz)]`.
-/
lemma contDiff_bigF (i₀ : ι) {δ : ℝ} (hδ : 0 < δ) {n : ℕ∞} :
    ContDiff ℝ (n : WithTop ℕ∞) (bigF i₀ hδ) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases h : 0 < nsq y
  · exact (radial.contDiff.contDiffAt.comp y contDiff_nsq.contDiffAt).mul
      ((angular hδ).contDiff.contDiffAt.comp y
        ((contDiff_coordSq i₀).contDiffAt.div contDiff_nsq.contDiffAt h.ne'))
  · have h0 : nsq y < 1 / 2 := by linarith [not_lt.1 h]
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(contDiff_nsq (n := 0)).continuous.continuousAt.eventually (gt_mem_nhds h0)] with z hz
    simp [bigF, radial_zero_of_le (le_of_lt hz)]

/- English proof (translation)
Use `HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℂ) 2) fun y hy => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hr : radial (nsq y) ≠ 0` using `fun h => hne (by simp [bigF, h])`. Establish `hlt : nsq y < 3 / 2`. Assume the negation of the conclusion as `hge`.

Conclude with `hr (radial_zero_of_ge (not_lt.1 hge))`. Use `hy ?_` and prove the remaining obligations. Rewrite using `[mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num)]`. Introduce `i`. Use `coordSq_le_nsq y i` as an intermediate fact.

Use polynomial arithmetic with `[norm_nonneg (y i)]`.
-/
lemma hasCompactSupport_bigF (i₀ : ι) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (bigF i₀ hδ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℂ) 2) fun y hy => ?_
  by_contra hne
  have hr : radial (nsq y) ≠ 0 := fun h => hne (by simp [bigF, h])
  have hlt : nsq y < 3 / 2 := by
    by_contra hge
    exact hr (radial_zero_of_ge (not_lt.1 hge))
  refine hy ?_
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  have := coordSq_le_nsq y i
  nlinarith [norm_nonneg (y i)]

/- English proof (translation)
The claim follows from `radial.contDiff.comp (contDiff_norm_sq ℝ)`.
-/
lemma contDiff_smallF {n : ℕ∞} : ContDiff ℝ (n : WithTop ℕ∞) smallF :=
  radial.contDiff.comp (contDiff_norm_sq ℝ)

/- English proof (translation)
Use `HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 2) fun t ht => ?_` and prove the remaining obligations. Use `radial_zero_of_ge ?_` and prove the remaining obligations. Establish `: 2 < ‖t‖` using `by simpa using ht`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma hasCompactSupport_smallF : HasCompactSupport smallF := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 2) fun t ht => ?_
  refine radial_zero_of_ge ?_
  have : 2 < ‖t‖ := by simpa using ht
  nlinarith

end GlobalTheory.CompanionTheory.TestBump

open GlobalTheory.CompanionTheory.TestBump in

/- English proof (translation)
Introduce `ι _ _ i₀ δ hδ`. Use `⟨bigF i₀ hδ, smallF, contDiff_bigF i₀ hδ, hasCompactSupport_bigF i₀ hδ, contDiff_smallF, hasCompactSupport_smallF, ?_, ?_, fun t => radial.nonneg, fun v => mul_nonneg radial.nonneg (angular hδ).nonneg, ?_⟩` and prove the remaining obligations. Establish `h1 : nsq (Pi.single i₀ 1 : ι → ℂ) = 1`. Simplify using `only [nsq]`. Rewrite using `[Finset.sum_eq_single i₀]`.

Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Pi.single_eq_of_ne hj]`. Simplify using the standard rewrite rules. Simplify using `[bigF, h1, radial_one, angular_one]`.

Introduce `t ht`. Simplify using `[smallF, ht, radial_one]`. Introduce `v hv`. Establish `hv1 : nsq v = 1` using `hv`. Establish `hFv : bigF i₀ hδ v = angular hδ (‖v i₀‖ ^ 2)`.

Simplify using `[bigF, hv1, radial_one]`. Use `⟨fun t => ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[hFv]`. Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality.

Establish `hz : radial (0 : ℝ) = 0` using `radial_zero_of_le (by norm_num)`. Simplify using `[bigF, smallF, nsq, hz]`. Establish `hn : nsq (t • v) = ‖t‖ ^ 2` using `by rw [nsq_smul, hv1, mul_one]`. Establish `ht2 : ‖t‖ ^ 2 ≠ 0` using `by positivity`. Simplify using `only [bigF, smallF, hn, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]`.

Rewrite using `[mul_div_cancel_left₀ _ ht2]`. Conclude with `lt_of_angular_ne hδ (by rwa [hFv] at h)`.
-/
theorem GlobalTheory.CompanionTheory.TestBump.cplxBump : CplxBump := by
  classical
  intro ι _ _ i₀ δ hδ
  refine ⟨bigF i₀ hδ, smallF, contDiff_bigF i₀ hδ, hasCompactSupport_bigF i₀ hδ, contDiff_smallF,
    hasCompactSupport_smallF, ?_, ?_, fun t => radial.nonneg, fun v => mul_nonneg radial.nonneg (angular hδ).nonneg, ?_⟩
  · have h1 : nsq (Pi.single i₀ 1 : ι → ℂ) = 1 := by
      simp only [nsq]
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp
    simp [bigF, h1, radial_one, angular_one]
  · intro t ht
    simp [smallF, ht, radial_one]
  · intro v hv
    have hv1 : nsq v = 1 := hv
    have hFv : bigF i₀ hδ v = angular hδ (‖v i₀‖ ^ 2) := by
      simp [bigF, hv1, radial_one]
    refine ⟨fun t => ?_, fun h => ?_⟩
    · rw [hFv]
      by_cases ht : t = 0
      · subst ht
        have hz : radial (0 : ℝ) = 0 := radial_zero_of_le (by norm_num)
        simp [bigF, smallF, nsq, hz]
      · have hn : nsq (t • v) = ‖t‖ ^ 2 := by rw [nsq_smul, hv1, mul_one]
        have ht2 : ‖t‖ ^ 2 ≠ 0 := by positivity
        simp only [bigF, smallF, hn, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
        rw [mul_div_cancel_left₀ _ ht2]
    · exact lt_of_angular_ne hδ (by rwa [hFv] at h)
