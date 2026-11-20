import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshRegMax

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

def fsGk (k : Fin 2) : ℝ → ℝ := if k = 0 then fubiniStudyProfile else fubiniStudyProfileInv

/- English proof (translation)
Apply the tactic sequence `fin_cases k <;> simp`.
-/
theorem finset_fin_two_eq_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp

/- English proof (translation)
Simplify using `[fsGk]`.
-/
@[simp] theorem fsGk_zero : fsGk 0 = fubiniStudyProfile := by
  simp [fsGk]
/- English proof (translation)
Simplify using `[fsGk]`.
-/
@[simp] theorem fsGk_one : fsGk 1 = fubiniStudyProfileInv := by
  simp [fsGk]

/- English proof (translation)
Conclude with `mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))`.
-/
theorem fubiniStudy_first_term_nonneg {q : ℝ} (hq : 0 ≤ q) : 0 ≤ fubiniStudyProfile q := by
  exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))

/- English proof (translation)
Establish `h` using `inv_pos.mpr hq`. Conclude with `mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))`.
-/
theorem fubiniStudy_second_term_nonneg {q : ℝ} (hq : 0 < q) : 0 ≤ fubiniStudyProfileInv q := by
  have h := inv_pos.mpr hq
  exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))

/- English proof (translation)
Break down `finset_fin_two_eq_cases k with rfl | rfl` into its components or cases. Rewrite using `[fsGk_zero]`. Conclude with `fubiniStudy_first_term_nonneg hq`. Rewrite using `[fsGk_one]`. Conclude with `fubiniStudy_second_term_nonneg (hk rfl)`.
-/
theorem fsGk_nonneg (k : Fin 2) {q : ℝ} (hq : 0 ≤ q) (hk : k = 1 → 0 < q) : 0 ≤ fsGk k q := by
  rcases finset_fin_two_eq_cases k with rfl | rfl
  · rw [fsGk_zero]
    exact fubiniStudy_first_term_nonneg hq
  · rw [fsGk_one]
    exact fubiniStudy_second_term_nonneg (hk rfl)

/- English proof (translation)
Break down `finset_fin_two_eq_cases k with rfl | rfl` into its components or cases. Rewrite using `[fsGk_zero]`. Establish `h1 : (1 : ℝ) + q ≠ 0` using `by linarith`. Use `⟨fun t => (1 / 2) * (1 + t)⁻¹, (1 / 2) * (-1 / (1 + q) ^ 2), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(eventually_gt_nhds (by linarith : (-1 : ℝ) < q)).mono fun t ht => hasDerivAt_fubiniStudyProfile ht`.

Conclude with `(((hasDerivAt_id' q).const_add 1).inv h1).const_mul (1 / 2)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[fsGk_one]`. Establish `hq1` using `hk rfl`.

Establish `h1 : q * (q + 1) ≠ 0` using `by positivity`. Use `⟨fun t => -(1 / 2) * (t * (t + 1))⁻¹, -(1 / 2) * (-(1 * (q + 1) + q * 1) / (q * (q + 1)) ^ 2), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(eventually_gt_nhds hq1).mono fun t ht => hasDerivAt_fubiniStudyProfileInv ht`. Conclude with `(((hasDerivAt_id' q).mul ((hasDerivAt_id' q).add_const 1)).inv h1).const_mul (-(1 / 2))`. Establish `h2 : q + 1 ≠ 0` using `by positivity`.

Establish `h3 : q ≠ 0` using `hq1.ne'`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fsGk_data (k : Fin 2) {q : ℝ} (hq : 0 ≤ q) (hk : k = 1 → 0 < q) :
    ∃ (G' : ℝ → ℝ) (G'' : ℝ), (∀ᶠ t in 𝓝 q, HasDerivAt (fsGk k) (G' t) t) ∧
      HasDerivAt G' G'' q ∧ q * G'' + G' q = 1 / (2 * (1 + q) ^ 2) := by
  rcases finset_fin_two_eq_cases k with rfl | rfl
  · rw [fsGk_zero]
    have h1 : (1 : ℝ) + q ≠ 0 := by linarith
    refine ⟨fun t => (1 / 2) * (1 + t)⁻¹, (1 / 2) * (-1 / (1 + q) ^ 2), ?_, ?_, ?_⟩
    · exact (eventually_gt_nhds (by linarith : (-1 : ℝ) < q)).mono fun t ht => hasDerivAt_fubiniStudyProfile ht
    · exact (((hasDerivAt_id' q).const_add 1).inv h1).const_mul (1 / 2)
    · field_simp
      ring
  · rw [fsGk_one]
    have hq1 := hk rfl
    have h1 : q * (q + 1) ≠ 0 := by positivity
    refine ⟨fun t => -(1 / 2) * (t * (t + 1))⁻¹,
      -(1 / 2) * (-(1 * (q + 1) + q * 1) / (q * (q + 1)) ^ 2), ?_, ?_, ?_⟩
    · exact (eventually_gt_nhds hq1).mono fun t ht => hasDerivAt_fubiniStudyProfileInv ht
    · exact (((hasDerivAt_id' q).mul ((hasDerivAt_id' q).add_const 1)).inv h1).const_mul (-(1 / 2))
    · have h2 : q + 1 ≠ 0 := by positivity
      have h3 : q ≠ 0 := hq1.ne'
      field_simp
      ring

/- English proof (translation)
Establish `hr0 : 0 < r` using `by linarith`. Establish `hr0' : r ≠ 0` using `hr0.ne'`. Establish `e : (a * Gk2 - (2 * Gj2 * r - 2 * Gj1 * (2 * Gj1)) / r ^ 2) * q + (a * Gk1 - 2 * Gj1 / r) = a * (q * Gk2 + Gk1) - 2 / r * (q * Gj2 + Gj1) + 4 * q * Gj1 ^ 2 / r ^ 2`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, hk, hj]`. Establish `h1 : 2 / r ≤ 1`. Rewrite using `[div_le_one hr0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : 0 ≤ 4 * q * Gj1 ^ 2 / r ^ 2` using `by positivity`.

Establish `h3 : 2 / r * κ ≤ a * κ` using `mul_le_mul_of_nonneg_right (le_trans h1 ha) hκ`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem combo_alg {a q r κ Gk1 Gk2 Gj1 Gj2 : ℝ} (hr : 2 < r) (ha : 1 ≤ a) (hq : 0 ≤ q)
    (hκ : 0 ≤ κ) (hk : q * Gk2 + Gk1 = κ) (hj : q * Gj2 + Gj1 = κ) :
    0 ≤ (a * Gk2 - (2 * Gj2 * r - 2 * Gj1 * (2 * Gj1)) / r ^ 2) * q + (a * Gk1 - 2 * Gj1 / r) := by
  have hr0 : 0 < r := by linarith
  have hr0' : r ≠ 0 := hr0.ne'
  have e : (a * Gk2 - (2 * Gj2 * r - 2 * Gj1 * (2 * Gj1)) / r ^ 2) * q + (a * Gk1 - 2 * Gj1 / r)
      = a * (q * Gk2 + Gk1) - 2 / r * (q * Gj2 + Gj1) + 4 * q * Gj1 ^ 2 / r ^ 2 := by
    field_simp
    ring
  rw [e, hk, hj]
  have h1 : 2 / r ≤ 1 := by
    rw [div_le_one hr0]
    linarith
  have h2 : 0 ≤ 4 * q * Gj1 ^ 2 / r ^ 2 := by positivity
  have h3 : 2 / r * κ ≤ a * κ := mul_le_mul_of_nonneg_right (le_trans h1 ha) hκ
  linarith

/- English proof (translation)
Establish `h` using `Real.exp_one_gt_d9`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem two_lt_exp_one : (2 : ℝ) < Real.exp 1 := by
  have h := Real.exp_one_gt_d9
  linarith

/- English proof (translation)
Take `⟨q, hq_def⟩ : ∃ q : ℝ, q = ‖y 0‖ ^ 2` from `⟨_, rfl⟩`. Establish `hq : 0 ≤ q`. Rewrite using `[hq_def]`. Check the signs of the components of the expression. Establish `hkq : k = 1 → 0 < q` using `fun h => by`.

Rewrite using `[hq_def]`. Conclude with `pow_pos (norm_pos_iff.mpr (hk h)) 2`. Establish `hjq : j = 1 → 0 < q` using `fun h => by`. Rewrite using `[hq_def]`. Conclude with `pow_pos (norm_pos_iff.mpr (hj h)) 2`.

Take `⟨Gk', Gk'', hkd, hkd2, hkid⟩` from `fsGk_data k hq hkq`. Take `⟨Gj', Gj'', hjd, hjd2, hjid⟩` from `fsGk_data j hq hjq`. Establish `hR : 2 < Real.exp 1 + 2 * fsGk j q`. Establish `h1` using `fsGk_nonneg j hq hjq`. Establish `h2` using `two_lt_exp_one`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hR0 : (0 : ℝ) < Real.exp 1 + 2 * fsGk j q` using `by linarith`. Establish `hdj : HasDerivAt (fun t => Real.exp 1 + 2 * fsGk j t) (2 * Gj' q) q` using `(hjd.self_of_nhds.const_mul 2).const_add _`. Establish `hpos_ev : ∀ᶠ t in 𝓝 q, 0 < Real.exp 1 + 2 * fsGk j t` using `hdj.continuousAt.eventually (lt_mem_nhds hR0)`. Establish `hG : ∀ᶠ t in 𝓝 q, HasDerivAt (fun t => a * fsGk k t + b - Real.log (Real.exp 1 + 2 * fsGk j t)) (a * Gk' t - 2 * Gj' t / (Real.exp 1 + 2 * fsGk j t)) t` using `by filter_upwards [hkd, hjd, hpos_ev] with t h1 h2 h3`.

Conclude with `((h1.const_mul a).add_const b).sub (((h2.const_mul 2).const_add _).log h3.ne')`. Establish `hG2 : HasDerivAt (fun t => a * Gk' t - 2 * Gj' t / (Real.exp 1 + 2 * fsGk j t)) (a * Gk'' - (2 * Gj'' * (Real.exp 1 + 2 * fsGk j q) - 2 * Gj' q * (2 * Gj' q)) / (Real.exp 1 + 2 * fsGk j q) ^ 2) q` using `(hkd2.const_mul a).sub ((hjd2.const_mul 2).div hdj hR0.ne')`. Establish `hκ : (0 : ℝ) ≤ 1 / (2 * (1 + q) ^ 2)` using `by positivity`. Establish `hnn` using `combo_alg hR ha hq hκ hkid hjid`. Substitute `hq_def` using the available equality.

Conclude with `projLine_leviForm_radial_nonneg (hF.mono fun w hw => by rw [hw]; rfl) hG hG2 hnn v`.
-/
theorem levi_combo_nonneg {F : (Fin 1 → ℂ) → ℝ} {y : Fin 1 → ℂ} {a b : ℝ} (ha : 1 ≤ a)
    (k j : Fin 2) (hk : k = 1 → y 0 ≠ 0) (hj : j = 1 → y 0 ≠ 0)
    (hF : ∀ᶠ w in 𝓝 y, F w = a * fsGk k (fsQ w) + b - Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)))
    (v : Fin 1 → ℂ) : 0 ≤ levi F y v := by
  obtain ⟨q, hq_def⟩ : ∃ q : ℝ, q = ‖y 0‖ ^ 2 := ⟨_, rfl⟩
  have hq : 0 ≤ q := by
    rw [hq_def]
    positivity
  have hkq : k = 1 → 0 < q := fun h => by
    rw [hq_def]
    exact pow_pos (norm_pos_iff.mpr (hk h)) 2
  have hjq : j = 1 → 0 < q := fun h => by
    rw [hq_def]
    exact pow_pos (norm_pos_iff.mpr (hj h)) 2
  obtain ⟨Gk', Gk'', hkd, hkd2, hkid⟩ := fsGk_data k hq hkq
  obtain ⟨Gj', Gj'', hjd, hjd2, hjid⟩ := fsGk_data j hq hjq
  have hR : 2 < Real.exp 1 + 2 * fsGk j q := by
    have h1 := fsGk_nonneg j hq hjq
    have h2 := two_lt_exp_one
    linarith
  have hR0 : (0 : ℝ) < Real.exp 1 + 2 * fsGk j q := by linarith
  have hdj : HasDerivAt (fun t => Real.exp 1 + 2 * fsGk j t) (2 * Gj' q) q :=
    (hjd.self_of_nhds.const_mul 2).const_add _
  have hpos_ev : ∀ᶠ t in 𝓝 q, 0 < Real.exp 1 + 2 * fsGk j t :=
    hdj.continuousAt.eventually (lt_mem_nhds hR0)
  have hG : ∀ᶠ t in 𝓝 q,
      HasDerivAt (fun t => a * fsGk k t + b - Real.log (Real.exp 1 + 2 * fsGk j t))
        (a * Gk' t - 2 * Gj' t / (Real.exp 1 + 2 * fsGk j t)) t := by
    filter_upwards [hkd, hjd, hpos_ev] with t h1 h2 h3
    exact ((h1.const_mul a).add_const b).sub (((h2.const_mul 2).const_add _).log h3.ne')
  have hG2 : HasDerivAt (fun t => a * Gk' t - 2 * Gj' t / (Real.exp 1 + 2 * fsGk j t))
      (a * Gk'' - (2 * Gj'' * (Real.exp 1 + 2 * fsGk j q) - 2 * Gj' q * (2 * Gj' q)) /
        (Real.exp 1 + 2 * fsGk j q) ^ 2) q :=
    (hkd2.const_mul a).sub ((hjd2.const_mul 2).div hdj hR0.ne')
  have hκ : (0 : ℝ) ≤ 1 / (2 * (1 + q) ^ 2) := by positivity
  have hnn := combo_alg hR ha hq hκ hkid hjid
  subst hq_def
  exact projLine_leviForm_radial_nonneg (hF.mono fun w hw => by rw [hw]; rfl) hG hG2 hnn v

/- English proof (translation)
Take `⟨q, hq_def⟩ : ∃ q : ℝ, q = ‖y 0‖ ^ 2` from `⟨_, rfl⟩`. Establish `hq : 0 ≤ q`. Rewrite using `[hq_def]`. Check the signs of the components of the expression. Establish `hkq : k = 1 → 0 < q` using `fun h => by`.

Rewrite using `[hq_def]`. Conclude with `pow_pos (norm_pos_iff.mpr (hk h)) 2`. Take `⟨Gk', Gk'', hkd, hkd2, hkid⟩` from `fsGk_data k hq hkq`. Establish `hG : ∀ᶠ t in 𝓝 q, HasDerivAt (fun t => a * fsGk k t + b) (a * Gk' t) t` using `hkd.mono fun t h1 => (h1.const_mul a).add_const b`. Establish `hG2 : HasDerivAt (fun t => a * Gk' t) (a * Gk'') q` using `hkd2.const_mul a`.

Establish `hnn : 0 ≤ a * Gk'' * q + a * Gk' q`. Establish `e : a * Gk'' * q + a * Gk' q = a * (q * Gk'' + Gk' q)` using `by ring`. Rewrite using `[e, hkid]`. Conclude with `mul_nonneg ha (by positivity)`. Substitute `hq_def` using the available equality.

Conclude with `projLine_leviForm_radial_nonneg (hF.mono fun w hw => by rw [hw]; rfl) hG hG2 hnn v`.
-/
theorem levi_simple_nonneg {F : (Fin 1 → ℂ) → ℝ} {y : Fin 1 → ℂ} {a b : ℝ} (ha : 0 ≤ a)
    (k : Fin 2) (hk : k = 1 → y 0 ≠ 0) (hF : ∀ᶠ w in 𝓝 y, F w = a * fsGk k (fsQ w) + b)
    (v : Fin 1 → ℂ) : 0 ≤ levi F y v := by
  obtain ⟨q, hq_def⟩ : ∃ q : ℝ, q = ‖y 0‖ ^ 2 := ⟨_, rfl⟩
  have hq : 0 ≤ q := by
    rw [hq_def]
    positivity
  have hkq : k = 1 → 0 < q := fun h => by
    rw [hq_def]
    exact pow_pos (norm_pos_iff.mpr (hk h)) 2
  obtain ⟨Gk', Gk'', hkd, hkd2, hkid⟩ := fsGk_data k hq hkq
  have hG : ∀ᶠ t in 𝓝 q, HasDerivAt (fun t => a * fsGk k t + b) (a * Gk' t) t :=
    hkd.mono fun t h1 => (h1.const_mul a).add_const b
  have hG2 : HasDerivAt (fun t => a * Gk' t) (a * Gk'') q := hkd2.const_mul a
  have hnn : 0 ≤ a * Gk'' * q + a * Gk' q := by
    have e : a * Gk'' * q + a * Gk' q = a * (q * Gk'' + Gk' q) := by ring
    rw [e, hkid]
    exact mul_nonneg ha (by positivity)
  subst hq_def
  exact projLine_leviForm_radial_nonneg (hF.mono fun w hw => by rw [hw]; rfl) hG hG2 hnn v

/- English proof (translation)
Break down `finset_fin_two_eq_cases k with rfl | rfl` into its components or cases. Simplify using `only [fsGk_zero]`. Conclude with `contDiff_fubiniStudyProfile_normSqFirst.contDiffOn`. Simplify using `only [fsGk_one]`. Conclude with `contDiffOn_fubiniStudyProfileInv_normSqFirst.mono fun w hw => by simpa using hw`.
-/
theorem contDiffOn_fsGk (k : Fin 2) :
    ContDiffOn ℝ ∞ (fun w => fsGk k (fsQ w)) {w : Fin 1 → ℂ | k = 1 → w 0 ≠ 0} := by
  rcases finset_fin_two_eq_cases k with rfl | rfl
  · simp only [fsGk_zero]
    exact contDiff_fubiniStudyProfile_normSqFirst.contDiffOn
  · simp only [fsGk_one]
    exact contDiffOn_fubiniStudyProfileInv_normSqFirst.mono fun w hw => by simpa using hw

/- English proof (translation)
Break down `finset_fin_two_eq_cases k with rfl | rfl` into its components or cases. Establish `e : {w : Fin 1 → ℂ | (0 : Fin 2) = 1 → w 0 ≠ 0} = Set.univ`. Use extensionality with `w`. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Conclude with `isOpen_univ`. Establish `e : {w : Fin 1 → ℂ | (1 : Fin 2) = 1 → w 0 ≠ 0} = {w | w 0 ≠ 0}`. Use extensionality with `w`. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Conclude with `isOpen_ne_fun (continuous_apply 0) continuous_const`.
-/
theorem isOpen_goodSet (k : Fin 2) : IsOpen {w : Fin 1 → ℂ | k = 1 → w 0 ≠ 0} := by
  rcases finset_fin_two_eq_cases k with rfl | rfl
  · have e : {w : Fin 1 → ℂ | (0 : Fin 2) = 1 → w 0 ≠ 0} = Set.univ := by
      ext w
      simp
    rw [e]
    exact isOpen_univ
  · have e : {w : Fin 1 → ℂ | (1 : Fin 2) = 1 → w 0 ≠ 0} = {w | w 0 ≠ 0} := by
      ext w
      simp
    rw [e]
    exact isOpen_ne_fun (continuous_apply 0) continuous_const

/- English proof (translation)
Conclude with `fsGk_nonneg k (by unfold fsQ; positivity) (fun h => by unfold fsQ; exact pow_pos (norm_pos_iff.mpr (hw h)) 2)`.
-/
theorem fsGk_fsQ_nonneg (k : Fin 2) {w : Fin 1 → ℂ} (hw : k = 1 → w 0 ≠ 0) :
    0 ≤ fsGk k (fsQ w) := by
  exact fsGk_nonneg k (by unfold fsQ; positivity)
    (fun h => by unfold fsQ; exact pow_pos (norm_pos_iff.mpr (hw h)) 2)

/- English proof (translation)
Rewrite using `[projLineSection_infty, infiniteCoord_infty]`.
-/
theorem projectiveLine_section_self_infty : projectiveLinePairSection (OnePoint.infty : OnePoint ℂ) (OnePoint.infty : OnePoint ℂ) = 0 := by
  rw [projLineSection_infty, infiniteCoord_infty]

/- English proof (translation)
Rewrite using `[projLineSection_coe]`.
-/
theorem projectiveLine_section_self_coe (z : ℂ) : projectiveLinePairSection (z : OnePoint ℂ) z = 1 := by
  rw [projLineSection_coe]

/- English proof (translation)
Proceed by induction on `y using OnePoint.rec with`. Consider the case `infty => simp [bdry, projectiveLine_section_self_infty]`. Consider the case `coe z => simp [bdry, projectiveLine_section_self_coe]`.
-/
theorem mem_boundary_projectiveLine (y : OnePoint ℂ) : y ∈ bdry projectiveLinePairSection ↔ y = (OnePoint.infty : OnePoint ℂ) := by
  induction y using OnePoint.rec with
  | infty => simp [bdry, projectiveLine_section_self_infty]
  | coe z => simp [bdry, projectiveLine_section_self_coe]

/- English proof (translation)
Simplify using `only [logNormSec, projectiveLine_section_self_coe, fsPot_φ_coe, finiteCoord_coe, norm_one, one_mul, Real.log_exp, fubiniStudyProfile]`.
-/
theorem logNormSec_coe (z : ℂ) : logNormSec fsPot projectiveLinePairSection z = -fubiniStudyProfile (‖z‖ ^ 2) := by
  simp only [logNormSec, projectiveLine_section_self_coe, fsPot_φ_coe, finiteCoord_coe, norm_one, one_mul, Real.log_exp,
    fubiniStudyProfile]

/- English proof (translation)
Simplify using `[logNormSec, projectiveLine_section_self_infty]`.
-/
theorem logNormSec_infty : logNormSec fsPot projectiveLinePairSection (OnePoint.infty : OnePoint ℂ) = 0 := by
  simp [logNormSec, projectiveLine_section_self_infty]

/- English proof (translation)
Simplify using `only [rW, logNormSec_coe]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rW_coe (z : ℂ) : rW fsPot projectiveLinePairSection z = Real.exp 1 + 2 * fubiniStudyProfile (‖z‖ ^ 2) := by
  simp only [rW, logNormSec_coe]
  ring

/- English proof (translation)
Simplify using `[rW, logNormSec_infty]`.
-/
theorem rW_infty : rW fsPot projectiveLinePairSection (OnePoint.infty : OnePoint ℂ) = Real.exp 1 := by
  simp [rW, logNormSec_infty]

/- English proof (translation)
Proceed by induction on `y using OnePoint.rec with`. Consider the case `infty => rw [rW_infty]`. Consider the case `coe z`. Rewrite using `[rW_coe]`. Establish `h` using `fubiniStudy_first_term_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 2)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem projectiveLine_weight_ge_exp_one (y : OnePoint ℂ) : Real.exp 1 ≤ rW fsPot projectiveLinePairSection y := by
  induction y using OnePoint.rec with
  | infty => rw [rW_infty]
  | coe z =>
    rw [rW_coe]
    have h := fubiniStudy_first_term_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 2)
    linarith

/- English proof (translation)
Conclude with `lt_of_lt_of_le (Real.exp_pos 1) (projectiveLine_weight_ge_exp_one y)`.
-/
theorem rW_pos (y : OnePoint ℂ) : 0 < rW fsPot projectiveLinePairSection y := by
  exact lt_of_lt_of_le (Real.exp_pos 1) (projectiveLine_weight_ge_exp_one y)

/- English proof (translation)
Proceed by induction on `y using OnePoint.rec with`. Consider the case `infty => rw [logNormSec_infty]`. Consider the case `coe z`. Rewrite using `[logNormSec_coe]`. Establish `h` using `fubiniStudy_first_term_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 2)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem logNormSec_nonpos (y : OnePoint ℂ) : logNormSec fsPot projectiveLinePairSection y ≤ 0 := by
  induction y using OnePoint.rec with
  | infty => rw [logNormSec_infty]
  | coe z =>
    rw [logNormSec_coe]
    have h := fubiniStudy_first_term_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 2)
    linarith

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem one_le_log_rW (y : OnePoint ℂ) : 1 ≤ Real.log (rW fsPot projectiveLinePairSection y) := by
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (rW fsPot projectiveLinePairSection y) := Real.log_le_log (Real.exp_pos 1) (projectiveLine_weight_ge_exp_one y)

/- English proof (translation)
Rewrite using `[Set.mem_range]`. Conclude with `OnePoint.ne_infty_iff_exists`.
-/
theorem ne_infty_iff_mem_range (x : OnePoint ℂ) :
    x ≠ (OnePoint.infty : OnePoint ℂ) ↔ x ∈ Set.range ((↑) : ℂ → OnePoint ℂ) := by
  rw [Set.mem_range]
  exact OnePoint.ne_infty_iff_exists

/- English proof (translation)
Break down `finset_fin_two_eq_cases j with rfl | rfl` into its components or cases. Rewrite using `[projLineAtlas_chart0, projLineChart0_symm_apply]`. Simplify using the standard rewrite rules. Rewrite using `[projLineAtlas_chart1, ne_infty_iff_mem_range, projLineChart1_symm_mem_range]`. Simplify using the standard rewrite rules.
-/
theorem chart_symm_ne_infty (j : Fin 2) (w : Fin 1 → ℂ) :
    (p1.chart j).symm w ≠ (OnePoint.infty : OnePoint ℂ) ↔ (j = 1 → w 0 ≠ 0) := by
  rcases finset_fin_two_eq_cases j with rfl | rfl
  · rw [projLineAtlas_chart0, projLineChart0_symm_apply]
    simp
  · rw [projLineAtlas_chart1, ne_infty_iff_mem_range, projLineChart1_symm_mem_range]
    simp

/- English proof (translation)
Take `⟨z, hz⟩` from `projLineChart1_symm_mem_range.mpr h`. Establish `h1` using `infiniteCoord_projLineChart1_symm w`. Rewrite `h1` using `[← hz, infiniteCoord_coe]`. Rewrite using `[← hz, ← h1, inv_inv]`.
-/
theorem projectiveLine_second_chart_symm_of_ne {w : Fin 1 → ℂ} (h : w 0 ≠ 0) :
    projectiveLineChartAtInfinity.symm w = (((w 0)⁻¹ : ℂ) : OnePoint ℂ) := by
  obtain ⟨z, hz⟩ := projLineChart1_symm_mem_range.mpr h
  have h1 := infiniteCoord_projLineChart1_symm w
  rw [← hz, infiniteCoord_coe] at h1
  rw [← hz, ← h1, inv_inv]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Conclude with `(projLineChart1_symm_mem_range.mp ((ne_infty_iff_mem_range _).mp hne)) h`.
-/
theorem projectiveLine_second_chart_symm_of_eq {w : Fin 1 → ℂ} (h : w 0 = 0) : projectiveLineChartAtInfinity.symm w = (OnePoint.infty : OnePoint ℂ) := by
  by_contra hne
  exact (projLineChart1_symm_mem_range.mp ((ne_infty_iff_mem_range _).mp hne)) h

def llw (y : OnePoint ℂ) : ℝ := -Real.log (rW fsPot projectiveLinePairSection y)

/- English proof (translation)
Unfold `llw`. Rewrite using `[rW_coe]`.
-/
theorem projectiveLineLogLog_coe (z : ℂ) :
    llw z = -Real.log (Real.exp 1 + 2 * fubiniStudyProfile (‖z‖ ^ 2)) := by
  unfold llw
  rw [rW_coe]

/- English proof (translation)
Break down `finset_fin_two_eq_cases j with rfl | rfl` into its components or cases. Rewrite using `[projLineAtlas_chart0, projLineChart0_symm_apply, projectiveLineLogLog_coe, fsGk_zero]`. Both sides reduce to the same expression. Rewrite using `[projLineAtlas_chart1, projectiveLine_second_chart_symm_of_ne (hw rfl), projectiveLineLogLog_coe, fsGk_one]`. Simplify using `only [fubiniStudyProfile, fubiniStudyProfileInv, fsQ, norm_inv, inv_pow]`.
-/
theorem projectiveLineLogLog_chart (j : Fin 2) (w : Fin 1 → ℂ) (hw : j = 1 → w 0 ≠ 0) :
    llw ((p1.chart j).symm w) = -Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)) := by
  rcases finset_fin_two_eq_cases j with rfl | rfl
  · rw [projLineAtlas_chart0, projLineChart0_symm_apply, projectiveLineLogLog_coe, fsGk_zero]
    rfl
  · rw [projLineAtlas_chart1, projectiveLine_second_chart_symm_of_ne (hw rfl), projectiveLineLogLog_coe, fsGk_one]
    simp only [fubiniStudyProfile, fubiniStudyProfileInv, fsQ, norm_inv, inv_pow]

/- English proof (translation)
Unfold `llw`. Establish `h` using `one_le_log_rW y`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem projectiveLineLogLog_le_neg_one (y : OnePoint ℂ) : llw y ≤ -1 := by
  unfold llw
  have h := one_le_log_rW y
  linarith

/- English proof (translation)
Rewrite using `[one_div, Real.log_inv]`. Establish `h` using `Real.log_le_log ht htB`. Rewrite `h` using `[Real.log_exp]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ell_ge {t B : ℝ} (ht : 0 < t) (htB : t ≤ Real.exp (-B)) : B ≤ Real.log (1 / t) := by
  rw [one_div, Real.log_inv]
  have h := Real.log_le_log ht htB
  rw [Real.log_exp] at h
  linarith

/- English proof (translation)
Establish `h` using `Real.add_one_le_exp 1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_exp_one : (1 : ℝ) ≤ Real.exp 1 := by
  have h := Real.add_one_le_exp 1
  linarith

/- English proof (translation)
Conclude with `ell_ge ht ht0`.
-/
theorem ell_big {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    Real.exp (Real.exp 1) ≤ Real.log (1 / t) := by
  exact ell_ge ht ht0

/- English proof (translation)
Conclude with `le_trans (Real.exp_le_exp.mpr one_le_exp_one) (ell_big ht ht0)`.
-/
theorem ell_ge_e {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    Real.exp 1 ≤ Real.log (1 / t) := by
  exact le_trans (Real.exp_le_exp.mpr one_le_exp_one) (ell_big ht ht0)

/- English proof (translation)
Conclude with `lt_of_lt_of_le (Real.exp_pos 1) (ell_ge_e ht ht0)`.
-/
theorem ell_pos {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    0 < Real.log (1 / t) := by
  exact lt_of_lt_of_le (Real.exp_pos 1) (ell_ge_e ht ht0)

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem logell_big {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    Real.exp 1 ≤ Real.log (Real.log (1 / t)) := by
  calc Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := (Real.log_exp _).symm
    _ ≤ Real.log (Real.log (1 / t)) := Real.log_le_log (Real.exp_pos _) (ell_big ht ht0)

/- English proof (translation)
Conclude with `lt_of_lt_of_le (Real.exp_pos 1) (logell_big ht ht0)`.
-/
theorem logell_pos {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    0 < Real.log (Real.log (1 / t)) := by
  exact lt_of_lt_of_le (Real.exp_pos 1) (logell_big ht ht0)

/- English proof (translation)
Unfold `epsT`. Conclude with `div_pos (mul_pos one_pos (logell_pos ht ht0)) (ell_pos ht ht0)`.
-/
theorem eps_pos {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    0 < epsT 1 t := by
  unfold epsT
  exact div_pos (mul_pos one_pos (logell_pos ht ht0)) (ell_pos ht ht0)

/- English proof (translation)
Unfold `epsT`. Rewrite using `[div_le_one (ell_pos ht ht0), one_mul]`. Establish `h` using `Real.log_le_sub_one_of_pos (ell_pos ht ht0)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eps_le_one {t : ℝ} (ht : 0 < t) (ht0 : t ≤ Real.exp (-Real.exp (Real.exp 1))) :
    epsT 1 t ≤ 1 := by
  unfold epsT
  rw [div_le_one (ell_pos ht ht0), one_mul]
  have h := Real.log_le_sub_one_of_pos (ell_pos ht ht0)
  linarith

/- English proof (translation)
Unfold `epsT`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem epsT_two (t : ℝ) : epsT 2 t = 2 * epsT 1 t := by
  unfold epsT
  ring

/- English proof (translation)
Conclude with `Real.log_le_log (one_div_pos.mpr (lt_of_lt_of_le ht htt')) (one_div_le_one_div_of_le ht htt')`.
-/
theorem ell_anti {t t' : ℝ} (ht : 0 < t) (htt' : t ≤ t') : Real.log (1 / t') ≤ Real.log (1 / t) := by
  exact Real.log_le_log (one_div_pos.mpr (lt_of_lt_of_le ht htt')) (one_div_le_one_div_of_le ht htt')

/- English proof (translation)
Establish `ht' : 0 < t'` using `lt_of_lt_of_le ht htt'`. Establish `h1 : Real.exp 1 ≤ Real.log (1 / t')` using `ell_ge_e ht' ht0`. Establish `h2 : Real.exp 1 ≤ Real.log (1 / t)` using `ell_ge_e ht (le_trans htt' ht0)`. Establish `h3 : Real.log (1 / t') ≤ Real.log (1 / t)` using `ell_anti ht htt'`. Unfold `epsT`.

Simplify using `only [one_mul]`. Conclude with `Real.log_div_self_antitoneOn h1 h2 h3`.
-/
theorem eps_mono {t t' : ℝ} (ht : 0 < t) (htt' : t ≤ t')
    (ht0 : t' ≤ Real.exp (-Real.exp (Real.exp 1))) : epsT 1 t ≤ epsT 1 t' := by
  have ht' : 0 < t' := lt_of_lt_of_le ht htt'
  have h1 : Real.exp 1 ≤ Real.log (1 / t') := ell_ge_e ht' ht0
  have h2 : Real.exp 1 ≤ Real.log (1 / t) := ell_ge_e ht (le_trans htt' ht0)
  have h3 : Real.log (1 / t') ≤ Real.log (1 / t) := ell_anti ht htt'
  unfold epsT
  simp only [one_mul]
  exact Real.log_div_self_antitoneOn h1 h2 h3

end

end ReciprocityTheory.AnForm.P
