import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
open PositivityTheory.RgEis PositivityTheory.RgEis.TF

noncomputable section

namespace GlobalTheory.CompanionTheory.TestFun

/- English proof (translation)
Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `y`. Distinguish the cases in `hy : 0 < N y`. Conclude with `(hφ.comp hN).contDiffAt.mul (hH y hy)`. Establish `hlt : N y < 1 / 2` using `by linarith [not_lt.mp hy]`.

Establish `hev : ∀ᶠ z in nhds y, N z < 1 / 2` using `hN.continuous.continuousAt.eventually (gt_mem_nhds hlt)`. Use `(contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hev] with z hz`. Simplify using `[hφ0 _ hz]`.
-/
theorem contDiff_mul_of_vanish {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : E → ℝ} (hN : ContDiff ℝ (⊤ : ℕ∞) N) {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ0 : ∀ s, s < 1 / 2 → φ s = 0) {H : E → ℝ}
    (hH : ∀ y, 0 < N y → ContDiffAt ℝ (⊤ : ℕ∞) H y) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => φ (N y) * H y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0 < N y
  · exact (hφ.comp hN).contDiffAt.mul (hH y hy)
  · have hlt : N y < 1 / 2 := by linarith [not_lt.mp hy]
    have hev : ∀ᶠ z in nhds y, N z < 1 / 2 :=
      hN.continuous.continuousAt.eventually (gt_mem_nhds hlt)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with z hz
    simp [hφ0 _ hz]

def sqSum {ι : Type} [Fintype ι] (y : ι → ℝ) : ℝ := ∑ j, y j ^ 2

/- English proof (translation)
Unfold `sqSum`. Conclude with `ContDiff.sum fun j _ => (contDiff_apply ℝ ℝ j).pow 2`.
-/
theorem sqSum_contDiff {ι : Type} [Fintype ι] : ContDiff ℝ (⊤ : ℕ∞) (sqSum (ι := ι)) := by
  unfold sqSum
  exact ContDiff.sum fun j _ => (contDiff_apply ℝ ℝ j).pow 2

/- English proof (translation)
Unfold `sqSum`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by simp [mul_pow]`.
-/
theorem sqSum_smul {ι : Type} [Fintype ι] (t : ℝ) (v : ι → ℝ) :
    sqSum (t • v) = t ^ 2 * sqSum v := by
  unfold sqSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp [mul_pow]

/- English proof (translation)
Unfold `sqSum`. Conclude with `Finset.single_le_sum (f := fun j => y j ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)`.
-/
theorem sq_le_sqSum {ι : Type} [Fintype ι] (y : ι → ℝ) (j : ι) : y j ^ 2 ≤ sqSum y := by
  unfold sqSum
  exact Finset.single_le_sum (f := fun j => y j ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)

/- English proof (translation)
Use `HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℝ) 2) ?_` and prove the remaining obligations. Introduce `y hy`. Apply `h` to reduce the goal to its premises. Establish `hn : (2 : ℝ) < ‖y‖` using `by simpa [mem_closedBall_zero_iff] using hy`. Establish `: ∃ j, 2 < |y j|`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `: ‖y‖ ≤ 2` using `(pi_norm_le_iff_of_nonneg (by norm_num)).2 fun j => by`. Simplify `hc j` using `[Real.norm_eq_abs]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨j, hj⟩` from `this`. Establish `h4 : (2 : ℝ) ^ 2 < y j ^ 2`. Rewrite using `[← sq_abs (y j)]`. Conclude with `pow_lt_pow_left₀ hj (by norm_num) (by norm_num)`. Combine the linear relations using `[sq_le_sqSum y j]`.
-/
theorem hasCompactSupport_of_sqSum {ι : Type} [Fintype ι] {F : (ι → ℝ) → ℝ}
    (h : ∀ y, 2 < sqSum y → F y = 0) : HasCompactSupport F := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℝ) 2) ?_
  intro y hy
  apply h
  have hn : (2 : ℝ) < ‖y‖ := by simpa [mem_closedBall_zero_iff] using hy
  have : ∃ j, 2 < |y j| := by
    by_contra hc
    push Not at hc
    have : ‖y‖ ≤ 2 := (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun j => by
      simpa [Real.norm_eq_abs] using hc j
    linarith
  obtain ⟨j, hj⟩ := this
  have h4 : (2 : ℝ) ^ 2 < y j ^ 2 := by
    rw [← sq_abs (y j)]
    exact pow_lt_pow_left₀ hj (by norm_num) (by norm_num)
  linarith [sq_le_sqSum y j]

def phi0 : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/- English proof (translation)
The claim follows from `phi0.one_of_mem_closedBall (by simp [phi0])`.
-/
theorem bumpProfile_one : phi0 1 = 1 :=
  phi0.one_of_mem_closedBall (by simp [phi0])

/- English proof (translation)
Use `phi0.zero_of_le_dist ?_` and prove the remaining obligations. Use `show (1 / 2 : ℝ) ≤ dist s 1`. Rewrite using `[Real.dist_eq, abs_sub_comm]`. Conclude with `le_trans (by linarith) (le_abs_self _)`.
-/
theorem bumpProfile_eq_zero_of_lt_half (s : ℝ) (hs : s < 1 / 2) : phi0 s = 0 := by
  refine phi0.zero_of_le_dist ?_
  show (1 / 2 : ℝ) ≤ dist s 1
  rw [Real.dist_eq, abs_sub_comm]
  exact le_trans (by linarith) (le_abs_self _)

/- English proof (translation)
Use `phi0.zero_of_le_dist ?_` and prove the remaining obligations. Use `show (1 / 2 : ℝ) ≤ dist s 1`. Rewrite using `[Real.dist_eq]`. Conclude with `le_trans (by linarith) (le_abs_self _)`.
-/
theorem bumpProfile_eq_zero_of_two_lt (s : ℝ) (hs : 2 < s) : phi0 s = 0 := by
  refine phi0.zero_of_le_dist ?_
  show (1 / 2 : ℝ) ≤ dist s 1
  rw [Real.dist_eq]
  exact le_trans (by linarith) (le_abs_self _)

/- English proof (translation)
The claim follows from `phi0.contDiff`.
-/
theorem bumpProfile_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => phi0 s) := phi0.contDiff

def bumpAt (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (1 : ℝ) :=
  ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩

/- English proof (translation)
The claim follows from `(bumpAt δ hδ).one_of_mem_closedBall (by simp [bumpAt]; linarith)`.
-/
theorem bumpAt_one (δ : ℝ) (hδ : 0 < δ) : bumpAt δ hδ 1 = 1 :=
  (bumpAt δ hδ).one_of_mem_closedBall (by simp [bumpAt]; linarith)

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `h ((bumpAt δ hδ).zero_of_le_dist ?_)` and prove the remaining obligations. Use `show δ ≤ dist s 1`. Rewrite using `[Real.dist_eq, abs_sub_comm]`. Conclude with `le_trans (by linarith [not_lt.mp hc]) (le_abs_self _)`.
-/
theorem bumpAt_ne (δ : ℝ) (hδ : 0 < δ) {s : ℝ} (h : bumpAt δ hδ s ≠ 0) : 1 - δ < s := by
  by_contra hc
  refine h ((bumpAt δ hδ).zero_of_le_dist ?_)
  show δ ≤ dist s 1
  rw [Real.dist_eq, abs_sub_comm]
  exact le_trans (by linarith [not_lt.mp hc]) (le_abs_self _)

def angular {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (y : ι → ℝ) : ℝ :=
  bumpAt δ hδ (y i₀ ^ 2 / sqSum y) * (y i₀ / Real.sqrt (sqSum y)) ^ m

/- English proof (translation)
Establish `hN : ContDiffAt ℝ (⊤ : ℕ∞) (sqSum (ι` using `ι)) y := sqSum_contDiff.contDiffAt`. Establish `hc : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => y i₀) y` using `(contDiff_apply ℝ ℝ i₀).contDiffAt`. Establish `hq : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => y i₀ ^ 2 / sqSum y) y` using `(hc.pow 2).div hN hy.ne'`. Establish `hbc : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => bumpAt δ hδ s)` using `(bumpAt δ hδ).contDiff`. Establish `hb : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => bumpAt δ hδ (y i₀ ^ 2 / sqSum y)) y` using `ContDiff.comp_contDiffAt (g := fun s : ℝ => bumpAt δ hδ s) (f := fun y : ι → ℝ => y i₀ ^ 2 / sqSum y) y hbc hq`.

Establish `hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => Real.sqrt (sqSum y)) y` using `hN.sqrt hy.ne'`. Conclude with `hb.mul ((hc.div hs (Real.sqrt_pos.2 hy).ne').pow m)`.
-/
theorem angular_contDiffAt {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (y : ι → ℝ) (hy : 0 < sqSum y) : ContDiffAt ℝ (⊤ : ℕ∞) (angular i₀ m δ hδ) y := by
  have hN : ContDiffAt ℝ (⊤ : ℕ∞) (sqSum (ι := ι)) y := sqSum_contDiff.contDiffAt
  have hc : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => y i₀) y := (contDiff_apply ℝ ℝ i₀).contDiffAt
  have hq : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => y i₀ ^ 2 / sqSum y) y :=
    (hc.pow 2).div hN hy.ne'
  have hbc : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => bumpAt δ hδ s) := (bumpAt δ hδ).contDiff
  have hb : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => bumpAt δ hδ (y i₀ ^ 2 / sqSum y)) y :=
    ContDiff.comp_contDiffAt (g := fun s : ℝ => bumpAt δ hδ s)
      (f := fun y : ι → ℝ => y i₀ ^ 2 / sqSum y) y hbc hq
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => Real.sqrt (sqSum y)) y := hN.sqrt hy.ne'
  exact hb.mul ((hc.div hs (Real.sqrt_pos.2 hy).ne').pow m)

def bigF {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (y : ι → ℝ) : ℝ :=
  phi0 (sqSum y) * angular i₀ m δ hδ y

def smallF (m : ℕ) (t : ℝ) : ℝ := phi0 (t ^ 2) * (t / Real.sqrt (t ^ 2)) ^ m

/- English proof (translation)
Use `contDiff_mul_of_vanish (N := fun t : ℝ => t ^ 2) (contDiff_id.pow 2) bumpProfile_contDiff bumpProfile_eq_zero_of_lt_half (H := fun t => (t / Real.sqrt (t ^ 2)) ^ m) ?_` and prove the remaining obligations. Introduce `y hy`. Establish `hN : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => t ^ 2) y` using `(contDiff_id.pow 2).contDiffAt`. Conclude with `(contDiffAt_id.div (hN.sqrt hy.ne') (Real.sqrt_pos.2 hy).ne').pow m`.
-/
theorem smallF_contDiff (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (smallF m) := by
  refine contDiff_mul_of_vanish (N := fun t : ℝ => t ^ 2) (contDiff_id.pow 2) bumpProfile_contDiff
    bumpProfile_eq_zero_of_lt_half (H := fun t => (t / Real.sqrt (t ^ 2)) ^ m) ?_
  intro y hy
  have hN : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => t ^ 2) y := (contDiff_id.pow 2).contDiffAt
  exact (contDiffAt_id.div (hN.sqrt hy.ne') (Real.sqrt_pos.2 hy).ne').pow m

/- English proof (translation)
Use `HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 2) ?_` and prove the remaining obligations. Introduce `t ht`. Establish `hn : (2 : ℝ) < |t|` using `by simpa [mem_closedBall_zero_iff] using ht`. Establish `h4 : (2 : ℝ) ^ 2 < t ^ 2`. Rewrite using `[← sq_abs t]`.

Conclude with `pow_lt_pow_left₀ hn (by norm_num) (by norm_num)`. Simplify using `[smallF, bumpProfile_eq_zero_of_two_lt (t ^ 2) (by linarith)]`.
-/
theorem smallF_compact (m : ℕ) : HasCompactSupport (smallF m) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 2) ?_
  intro t ht
  have hn : (2 : ℝ) < |t| := by simpa [mem_closedBall_zero_iff] using ht
  have h4 : (2 : ℝ) ^ 2 < t ^ 2 := by
    rw [← sq_abs t]
    exact pow_lt_pow_left₀ hn (by norm_num) (by norm_num)
  simp [smallF, bumpProfile_eq_zero_of_two_lt (t ^ 2) (by linarith)]

/- English proof (translation)
Simplify using `[bigF, angular, hv, bumpProfile_one]`.
-/
theorem bigF_unit {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (v : ι → ℝ)
    (hv : sqSum v = 1) : bigF i₀ m δ hδ v = bumpAt δ hδ (v i₀ ^ 2) * v i₀ ^ m := by
  simp [bigF, angular, hv, bumpProfile_one]

/- English proof (translation)
Rewrite using `[bigF_unit i₀ m δ hδ v hv]`. Establish `hN : sqSum (t • v) = t ^ 2` using `by rw [sqSum_smul, hv, mul_one]`. Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Establish `h0 : sqSum (0 : ι → ℝ) = 0` using `by simp [sqSum]`.

Simplify using `[bigF, smallF, h0, bumpProfile_eq_zero_of_lt_half 0 (by norm_num)]`. Establish `ht2 : t ^ 2 ≠ 0` using `pow_ne_zero 2 ht`. Establish `hq : (t • v) i₀ ^ 2 / sqSum (t • v) = v i₀ ^ 2`. Rewrite using `[hN, Pi.smul_apply, smul_eq_mul, mul_pow]`. Clear the denominators using the available nonvanishing facts.

Establish `hr : (t • v) i₀ / Real.sqrt (sqSum (t • v)) = t / Real.sqrt (t ^ 2) * v i₀`. Rewrite using `[hN, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [bigF, angular, smallF]`. Rewrite using `[hq, hr, hN, mul_pow]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem bigF_smul {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (v : ι → ℝ)
    (hv : sqSum v = 1) (t : ℝ) :
    bigF i₀ m δ hδ (t • v) = smallF m t * bigF i₀ m δ hδ v := by
  rw [bigF_unit i₀ m δ hδ v hv]
  have hN : sqSum (t • v) = t ^ 2 := by rw [sqSum_smul, hv, mul_one]
  by_cases ht : t = 0
  · subst ht
    have h0 : sqSum (0 : ι → ℝ) = 0 := by simp [sqSum]
    simp [bigF, smallF, h0, bumpProfile_eq_zero_of_lt_half 0 (by norm_num)]
  · have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
    have hq : (t • v) i₀ ^ 2 / sqSum (t • v) = v i₀ ^ 2 := by
      rw [hN, Pi.smul_apply, smul_eq_mul, mul_pow]
      field_simp
    have hr : (t • v) i₀ / Real.sqrt (sqSum (t • v)) = t / Real.sqrt (t ^ 2) * v i₀ := by
      rw [hN, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [bigF, angular, smallF]
    rw [hq, hr, hN, mul_pow]
    ring

/- English proof (translation)
Introduce `ι _ _ i₀ m δ hδ`. Establish `hone : sqSum (Pi.single i₀ (1 : ℝ) : ι → ℝ) = 1`. Unfold `sqSum`. Rewrite using `[Finset.sum_eq_single i₀]`. Simplify using the standard rewrite rules.

Introduce `j _ hj`. Simplify using `[Pi.single_eq_of_ne hj]`. Simplify using the standard rewrite rules. Use `⟨bigF i₀ m δ hδ, smallF m, ?_, ?_, smallF_contDiff m, smallF_compact m, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `contDiff_mul_of_vanish sqSum_contDiff bumpProfile_contDiff bumpProfile_eq_zero_of_lt_half (angular_contDiffAt i₀ m δ hδ)`.

Use `hasCompactSupport_of_sqSum fun y hy => ?_` and prove the remaining obligations. Simplify using `[bigF, bumpProfile_eq_zero_of_two_lt _ hy]`. Rewrite using `[bigF_unit i₀ m δ hδ _ hone]`. Simplify using `[bumpAt_one]`. Simplify using `[smallF, bumpProfile_one]`.

Introduce `t ht`. Use `mul_nonneg phi0.nonneg (pow_nonneg (div_nonneg ht (Real.sqrt_nonneg _)) m)` and prove the remaining obligations. Introduce `t`. Simplify using `only [smallF, neg_sq, neg_div, neg_pow t]`. Put the polynomial expressions in normal form.

Introduce `v hv`. Establish `hv' : sqSum v = 1` using `hv`. Use `⟨bigF_smul i₀ m δ hδ v hv', ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Rewrite `h` using `[bigF_unit i₀ m δ hδ v hv']`.

Conclude with `bumpAt_ne δ hδ (left_ne_zero_of_mul h)`. Introduce `h`. Rewrite using `[bigF_unit i₀ m δ hδ v hv']`. Conclude with `mul_nonneg (bumpAt δ hδ).nonneg (pow_nonneg h.le m)`.
-/
theorem realBump : RealBump := by
  intro ι _ _ i₀ m δ hδ
  have hone : sqSum (Pi.single i₀ (1 : ℝ) : ι → ℝ) = 1 := by
    unfold sqSum
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  refine ⟨bigF i₀ m δ hδ, smallF m, ?_, ?_, smallF_contDiff m, smallF_compact m, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_mul_of_vanish sqSum_contDiff bumpProfile_contDiff bumpProfile_eq_zero_of_lt_half
      (angular_contDiffAt i₀ m δ hδ)
  · refine hasCompactSupport_of_sqSum fun y hy => ?_
    simp [bigF, bumpProfile_eq_zero_of_two_lt _ hy]
  · rw [bigF_unit i₀ m δ hδ _ hone]
    simp [bumpAt_one]
  · simp [smallF, bumpProfile_one]
  · intro t ht
    refine mul_nonneg phi0.nonneg (pow_nonneg (div_nonneg ht (Real.sqrt_nonneg _)) m)
  · intro t
    simp only [smallF, neg_sq, neg_div, neg_pow t]
    ring_nf
  · intro v hv
    have hv' : sqSum v = 1 := hv
    refine ⟨bigF_smul i₀ m δ hδ v hv', ?_, ?_⟩
    · intro h
      rw [bigF_unit i₀ m δ hδ v hv'] at h
      exact bumpAt_ne δ hδ (left_ne_zero_of_mul h)
    · intro h
      rw [bigF_unit i₀ m δ hδ v hv']
      exact mul_nonneg (bumpAt δ hδ).nonneg (pow_nonneg h.le m)

end GlobalTheory.CompanionTheory.TestFun
