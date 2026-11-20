import ReciprocityTheory.AnalyticForms.LeviForms.ProjectiveLineSecondChartSymmOfNe

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

def llT (t : ℝ) (y : OnePoint ℂ) : ℝ :=
  if projectiveLinePairSection y y = 0 then -Real.log (Real.log (1 / t)) else
    ReciprocityTheory.AnForm.A.regMax (epsT 1 t) ![llw y, -Real.log (Real.log (1 / t))]

abbrev T0 : ℝ := Real.exp (-Real.exp (Real.exp 1))

/- English proof (translation)
Use `norm_cast`.
-/
theorem two_le_inf : (2 : WithTop ℕ∞) ≤ ∞ := by norm_cast

section RM

open ReciprocityTheory.AnForm.A

/- English proof (translation)
The claim follows from `le_trans (by simpa using le_tmax ![a, b] 0) (regMax_ge η _)`.
-/
theorem rm_ge_left (η a b : ℝ) : a ≤ regMax η ![a, b] :=
  le_trans (by simpa using le_tmax ![a, b] 0) (regMax_ge η _)

/- English proof (translation)
The claim follows from `le_trans (by simpa using le_tmax ![a, b] 1) (regMax_ge η _)`.
-/
theorem rm_ge_right (η a b : ℝ) : b ≤ regMax η ![a, b] :=
  le_trans (by simpa using le_tmax ![a, b] 1) (regMax_ge η _)

/- English proof (translation)
Apply the tactic sequence `have : tmax ![a, b] ≤ m := tmax_le (fun i => by rcases finset_fin_two_eq_cases i with rfl | rfl <;> simpa)`. Combine the linear relations using `[regMax_le hη ![a, b]]`.
-/
theorem rm_le {η a b m : ℝ} (hη : 0 ≤ η) (ha : a ≤ m) (hb : b ≤ m) :
    regMax η ![a, b] ≤ m + η / 2 := by
  have : tmax ![a, b] ≤ m := tmax_le (fun i => by rcases finset_fin_two_eq_cases i with rfl | rfl <;> simpa)
  linarith [regMax_le hη ![a, b]]

/- English proof (translation)
Use `regMax_eq_of_dom hη ![a, b] 0 (fun j hj => by` as an intermediate fact. Break down `finset_fin_two_eq_cases j with rfl | rfl` into its components or cases. Conclude with `absurd rfl hj`. Simplify using `using h)`. Simplify using `using this`.
-/
theorem rm_eq_left {η a b : ℝ} (hη : 0 ≤ η) (h : b + η ≤ a) : regMax η ![a, b] = a := by
  have := regMax_eq_of_dom hη ![a, b] 0 (fun j hj => by
    rcases finset_fin_two_eq_cases j with rfl | rfl
    · exact absurd rfl hj
    · simpa using h)
  simpa using this

/- English proof (translation)
Use `regMax_eq_of_dom hη ![a, b] 1 (fun j hj => by` as an intermediate fact. Break down `finset_fin_two_eq_cases j with rfl | rfl` into its components or cases. Simplify using `using h`. Conclude with `absurd rfl hj)`. Simplify using `using this`.
-/
theorem rm_eq_right {η a b : ℝ} (hη : 0 ≤ η) (h : a + η ≤ b) : regMax η ![a, b] = b := by
  have := regMax_eq_of_dom hη ![a, b] 1 (fun j hj => by
    rcases finset_fin_two_eq_cases j with rfl | rfl
    · simpa using h
    · exact absurd rfl hj)
  simpa using this

end RM

/- English proof (translation)
Simplify using `[llT, projectiveLine_section_self_infty]`.
-/
theorem llT_infty (t : ℝ) : llT t OnePoint.infty = -Real.log (Real.log (1 / t)) := by
  simp [llT, projectiveLine_section_self_infty]

/- English proof (translation)
Rewrite using `[llT, if_neg (show ¬ (projectiveLinePairSection y y = 0) from fun h => hy ((mem_boundary_projectiveLine y).1 h))]`.
-/
theorem llT_ne (t : ℝ) {y : OnePoint ℂ} (hy : y ≠ OnePoint.infty) :
    llT t y = ReciprocityTheory.AnForm.A.regMax (epsT 1 t) ![llw y, -Real.log (Real.log (1 / t))] := by
  rw [llT, if_neg (show ¬ (projectiveLinePairSection y y = 0) from fun h => hy ((mem_boundary_projectiveLine y).1 h))]

/- English proof (translation)
Break down `finset_fin_two_eq_cases j with rfl | rfl` into its components or cases. Rewrite using `[projLineAtlas_chart0]`. Conclude with `projLineChart0_target`. Rewrite using `[projLineAtlas_chart1]`. Conclude with `projLineChart1_target`.
-/
theorem projLine_chart_target (j : Fin 2) : (p1.chart j).target = Set.univ := by
  rcases finset_fin_two_eq_cases j with rfl | rfl
  · rw [projLineAtlas_chart0]; exact projLineChart0_target
  · rw [projLineAtlas_chart1]; exact projLineChart1_target

/- English proof (translation)
Break down `fsPot_chart x j with h | ⟨h, hs⟩` into its components or cases. Conclude with `⟨0, fun w => by rw [fsGk_zero]; exact congrFun h w, fun w _ h1 => absurd h1 (by decide)⟩`. Conclude with `⟨1, fun w => by rw [fsGk_one]; exact congrFun h w, fun w hw _ => hs w hw⟩`.
-/
theorem fsPot_chart' (x : OnePoint ℂ) (j : Fin 2) : ∃ k : Fin 2,
    (∀ w, fsPot.φ x ((p1.chart j).symm w) = fsGk k (fsQ w)) ∧
    ∀ w ∈ (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x, k = 1 → w 0 ≠ 0 := by
  rcases fsPot_chart x j with h | ⟨h, hs⟩
  · exact ⟨0, fun w => by rw [fsGk_zero]; exact congrFun h w, fun w _ h1 => absurd h1 (by decide)⟩
  · exact ⟨1, fun w => by rw [fsGk_one]; exact congrFun h w, fun w hw _ => hs w hw⟩

/- English proof (translation)
Rewrite using `[← chart_symm_ne_infty j w, projLine_chart_target j]`. Simplify using `[mem_boundary_projectiveLine]`.
-/
theorem chartV_iff (j : Fin 2) (w : Fin 1 → ℂ) :
    w ∈ (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' (bdry projectiveLinePairSection)ᶜ ↔ (j = 1 → w 0 ≠ 0) := by
  rw [← chart_symm_ne_infty j w, projLine_chart_target j]
  simp [mem_boundary_projectiveLine]

/- English proof (translation)
Rewrite using `[llT_ne t ((chart_symm_ne_infty j w).2 hw), projectiveLineLogLog_chart j w hw]`.
-/
theorem llT_chart_eq (t : ℝ) (j : Fin 2) (w : Fin 1 → ℂ) (hw : j = 1 → w 0 ≠ 0) :
    llT t ((p1.chart j).symm w) = ReciprocityTheory.AnForm.A.regMax (epsT 1 t)
      ![-Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)), -Real.log (Real.log (1 / t))] := by
  rw [llT_ne t ((chart_symm_ne_infty j w).2 hw), projectiveLineLogLog_chart j w hw]

/- English proof (translation)
The claim follows from `((contDiffOn_const.add (contDiffOn_const.mul (contDiffOn_fsGk j))).log (fun w hw => ne_of_gt (by have := fsGk_fsQ_nonneg j hw; have := Real.exp_pos 1; linarith))).neg`.
-/
theorem contDiffOn_llwChart (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun w => -Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)))
      {w : Fin 1 → ℂ | j = 1 → w 0 ≠ 0} :=
  ((contDiffOn_const.add (contDiffOn_const.mul (contDiffOn_fsGk j))).log (fun w hw =>
    ne_of_gt (by have := fsGk_fsQ_nonneg j hw; have := Real.exp_pos 1; linarith))).neg

/- English proof (translation)
Use `(ReciprocityTheory.AnForm.A.regMax_contDiff (ι := Fin 2) (eps_pos ht ht0)).comp_contDiffOn ?_` and prove the remaining obligations. Use `contDiffOn_pi.2 fun i => ?_` and prove the remaining obligations. Break down `finset_fin_two_eq_cases i with rfl | rfl` into its components or cases. Conclude with `(contDiffOn_llwChart j).congr (fun w _ => by simp)`. Conclude with `(contDiffOn_const (c := -Real.log (Real.log (1 / t)))).congr (fun w _ => by simp)`.
-/
theorem contDiffOn_llTChart (t : ℝ) (ht : 0 < t) (ht0 : t ≤ T0) (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun w => ReciprocityTheory.AnForm.A.regMax (epsT 1 t)
      ![-Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)), -Real.log (Real.log (1 / t))])
      {w : Fin 1 → ℂ | j = 1 → w 0 ≠ 0} := by
  refine (ReciprocityTheory.AnForm.A.regMax_contDiff (ι := Fin 2) (eps_pos ht ht0)).comp_contDiffOn ?_
  refine contDiffOn_pi.2 fun i => ?_
  rcases finset_fin_two_eq_cases i with rfl | rfl
  · exact (contDiffOn_llwChart j).congr (fun w _ => by simp)
  · exact (contDiffOn_const (c := -Real.log (Real.log (1 / t)))).congr (fun w _ => by simp)

/- English proof (translation)
Establish `hℓ` using `ell_pos ht ht0`. Establish `hM : 0 < Real.log (1 / t) * Real.exp (epsT 1 t)` using `mul_pos hℓ (Real.exp_pos _)`. Use `⟨Real.exp (-(Real.log (1 / t) * Real.exp (epsT 1 t))), Real.exp_pos _, fun w hw => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h0 : w 0 = 0`. Rewrite using `[projectiveLine_second_chart_symm_of_eq h0, llT_infty]`.

Establish `e1` using `llT_chart_eq t 1 w (fun _ => h0)`. Rewrite `e1` using `[projLineAtlas_chart1]`. Rewrite using `[e1]`. Apply `rm_eq_right (eps_pos ht ht0).le` to reduce the goal to its premises. Establish `hq : 0 < fsQ w` using `by unfold fsQ; have := norm_pos_iff.2 h0; positivity`.

Establish `hinv : Real.exp (Real.log (1 / t) * Real.exp (epsT 1 t)) < (fsQ w)⁻¹` using `(lt_inv_comm₀ (Real.exp_pos _) hq).2 (by rwa [← Real.exp_neg])`. Establish `h2 : 2 * fsGk 1 (fsQ w) = Real.log (1 + (fsQ w)⁻¹)` using `by rw [fsGk_one, fubiniStudyProfileInv]; ring`. Establish `h3 : Real.log (1 / t) * Real.exp (epsT 1 t) < Real.log (1 + (fsQ w)⁻¹)`. Use `Real.log_lt_log (Real.exp_pos _) (show Real.exp (Real.log (1 / t) * Real.exp (epsT 1 t)) < 1 + (fsQ w)⁻¹ by linarith)` as an intermediate fact. Rewrite `this` using `[Real.log_exp]`. Then use the resulting hypothesis.

Establish `h4 : Real.log (Real.log (1 / t) * Real.exp (epsT 1 t)) ≤ Real.log (Real.exp 1 + 2 * fsGk 1 (fsQ w))` using `Real.log_le_log hM (by rw [h2]; linarith [Real.exp_pos 1])`. Establish `h5 : Real.log (Real.log (1 / t) * Real.exp (epsT 1 t)) = Real.log (Real.log (1 / t)) + epsT 1 t`. Rewrite using `[Real.log_mul hℓ.ne' (Real.exp_pos _).ne', Real.log_exp]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem llT_near_pole (t : ℝ) (ht : 0 < t) (ht0 : t ≤ T0) : ∃ δ > 0, ∀ w : Fin 1 → ℂ,
    fsQ w < δ → llT t (projectiveLineChartAtInfinity.symm w) = -Real.log (Real.log (1 / t)) := by
  have hℓ := ell_pos ht ht0
  have hM : 0 < Real.log (1 / t) * Real.exp (epsT 1 t) := mul_pos hℓ (Real.exp_pos _)
  refine ⟨Real.exp (-(Real.log (1 / t) * Real.exp (epsT 1 t))), Real.exp_pos _, fun w hw => ?_⟩
  by_cases h0 : w 0 = 0
  · rw [projectiveLine_second_chart_symm_of_eq h0, llT_infty]
  · have e1 := llT_chart_eq t 1 w (fun _ => h0)
    rw [projLineAtlas_chart1] at e1
    rw [e1]
    apply rm_eq_right (eps_pos ht ht0).le
    have hq : 0 < fsQ w := by unfold fsQ; have := norm_pos_iff.2 h0; positivity
    have hinv : Real.exp (Real.log (1 / t) * Real.exp (epsT 1 t)) < (fsQ w)⁻¹ :=
      (lt_inv_comm₀ (Real.exp_pos _) hq).2 (by rwa [← Real.exp_neg])
    have h2 : 2 * fsGk 1 (fsQ w) = Real.log (1 + (fsQ w)⁻¹) := by rw [fsGk_one, fubiniStudyProfileInv]; ring
    have h3 : Real.log (1 / t) * Real.exp (epsT 1 t) < Real.log (1 + (fsQ w)⁻¹) := by
      have := Real.log_lt_log (Real.exp_pos _)
        (show Real.exp (Real.log (1 / t) * Real.exp (epsT 1 t)) < 1 + (fsQ w)⁻¹ by linarith)
      rwa [Real.log_exp] at this
    have h4 : Real.log (Real.log (1 / t) * Real.exp (epsT 1 t)) ≤
        Real.log (Real.exp 1 + 2 * fsGk 1 (fsQ w)) :=
      Real.log_le_log hM (by rw [h2]; linarith [Real.exp_pos 1])
    have h5 : Real.log (Real.log (1 / t) * Real.exp (epsT 1 t)) = Real.log (Real.log (1 / t)) + epsT 1 t := by
      rw [Real.log_mul hℓ.ne' (Real.exp_pos _).ne', Real.log_exp]
    linarith

/- English proof (translation)
Take `⟨δ, hδ, hpole⟩` from `llT_near_pole t ht ht0`. Introduce `w _`. Use `ContDiffAt.contDiffWithinAt ?_` and prove the remaining obligations. Distinguish the cases in `hw : j = 1 → w 0 ≠ 0`. Establish `hmem : {w : Fin 1 → ℂ | j = 1 → w 0 ≠ 0} ∈ 𝓝 w` using `(isOpen_goodSet j).mem_nhds hw`.

Use `((contDiffOn_llTChart t ht ht0 j).contDiffAt hmem).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hmem] with w' hw'`. Conclude with `llT_chart_eq t j w' hw'`. Use `push Not at hw`. Take `⟨rfl, hw0⟩` from `hw`.

Establish `hmem : {w : Fin 1 → ℂ | fsQ w < δ} ∈ 𝓝 w` using `(isOpen_lt contDiff_fsQ.continuous continuous_const).mem_nhds (by simp [fsQ, hw0, hδ])`. Use `(contDiffAt_const (c := -Real.log (Real.log (1 / t)))).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hmem] with w' hw'`. Use `show llT t ((p1.chart (1 : Fin 2)).symm w') = _`. Rewrite using `[projLineAtlas_chart1]`.

Conclude with `hpole w' hw'`.
-/
theorem llT_smooth_chart (t : ℝ) (ht : 0 < t) (ht0 : t ≤ T0) (j : Fin 2) :
    ContDiffOn ℝ ∞ (llT t ∘ (p1.chart j).symm) ((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' Set.univ) := by
  obtain ⟨δ, hδ, hpole⟩ := llT_near_pole t ht ht0
  intro w _
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases hw : j = 1 → w 0 ≠ 0
  · have hmem : {w : Fin 1 → ℂ | j = 1 → w 0 ≠ 0} ∈ 𝓝 w := (isOpen_goodSet j).mem_nhds hw
    refine ((contDiffOn_llTChart t ht ht0 j).contDiffAt hmem).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with w' hw'
    exact llT_chart_eq t j w' hw'
  · push Not at hw
    obtain ⟨rfl, hw0⟩ := hw
    have hmem : {w : Fin 1 → ℂ | fsQ w < δ} ∈ 𝓝 w :=
      (isOpen_lt contDiff_fsQ.continuous continuous_const).mem_nhds (by simp [fsQ, hw0, hδ])
    refine (contDiffAt_const (c := -Real.log (Real.log (1 / t)))).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with w' hw'
    show llT t ((p1.chart (1 : Fin 2)).symm w') = _
    rw [projLineAtlas_chart1]
    exact hpole w' hw'

/- English proof (translation)
Introduce `j` and use `llT_smooth_chart t ht ht0 j`.
-/
theorem llT_smooth (t : ℝ) (ht : 0 < t) (ht0 : t ≤ T0) : p1.Smooth (llT t) :=
  fun j => llT_smooth_chart t ht ht0 j

/- English proof (translation)
Take `⟨k, hφw, hk⟩` from `fsPot_chart' x j`. Establish `hDo : IsOpen ((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x)` using `(p1.chart j).isOpen_inter_preimage_symm (fsPot.isOpen_U x)`. Establish `hη` using `eps_pos ht ht0`. Establish `ha : 1 ≤ 1 + epsT 2 t` using `by rw [epsT_two]; linarith`. Establish `hyk : k = 1 → y 0 ≠ 0` using `hk y hy`.

Distinguish the cases in `hyj : j = 1 → y 0 ≠ 0`. Establish `hNo : IsOpen (((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x) ∩ {w : Fin 1 → ℂ | j = 1 → w 0 ≠ 0})` using `hDo.inter (isOpen_goodSet j)`. Establish `hyN : y ∈ ((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x) ∩ {w : Fin 1 → ℂ | j = 1 → w 0 ≠ 0}` using `⟨hy, hyj⟩`. Establish `hEq : (fun w => fsPot.φ x ((p1.chart j).symm w) + llT t ((p1.chart j).symm w) + epsT 2 t * fsPot.φ x ((p1.chart j).symm w)) =ᶠ[𝓝 y] fun w => ReciprocityTheory.AnForm.A.regMax (epsT 1 t) (fun i => ![-Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)), -Real.log (Real.log (1 / t))] i + (1 …` using `by filter_upwards [hNo.mem_nhds hyN] with w hw`. Rewrite using `[hφw, llT_chart_eq t j w hw.2, ReciprocityTheory.AnForm.A.regMax_add_const]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[levi_congr hEq]`. Use `ReciprocityTheory.AnForm.A.regMaxLevi_thm 1 (Fin 2) (epsT 1 t) _ (fun i w => ![-Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)), -Real.log (Real.log (1 / t))] i + (1 + epsT 2 t) * fsGk k (fsQ w)) hNo hη ?_ y hyN v 0 ?_` and prove the remaining obligations. Introduce `i`. Establish `hG : ContDiffOn ℝ ∞ (fun w => fsGk k (fsQ w)) (((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x) ∩ {w : Fin 1 → ℂ | j = 1 → w 0 ≠ 0})` using `(contDiffOn_fsGk k).mono (fun w hw => hk w hw.1)`.

Break down `finset_fin_two_eq_cases i with rfl | rfl` into its components or cases. Conclude with `((((contDiffOn_llwChart j).mono (fun w hw => hw.2)).add ((contDiffOn_const (c := 1 + epsT 2 t)).mul hG)).of_le two_le_inf).congr (fun w _ => by simp)`. Conclude with `(((contDiffOn_const (c := -Real.log (Real.log (1 / t)))).add ((contDiffOn_const (c := 1 + epsT 2 t)).mul hG)).of_le two_le_inf).congr (fun w _ => by simp)`. Introduce `i`. Break down `finset_fin_two_eq_cases i with rfl | rfl` into its components or cases.

Conclude with `levi_combo_nonneg (a := 1 + epsT 2 t) (b := 0) ha k j hyk hyj (Eventually.of_forall fun w => by`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]`. Use the proof step `ring) v`. Conclude with `levi_simple_nonneg (a := 1 + epsT 2 t) (b := -Real.log (Real.log (1 / t))) (by linarith) k hyk (Eventually.of_forall fun w => by`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]`.

Use the proof step `ring) v`. Use `push Not at hyj`. Take `⟨rfl, hy0⟩` from `hyj`. Take `⟨δ, hδ, hpole⟩` from `llT_near_pole t ht ht0`. Establish `hW : {w : Fin 1 → ℂ | fsQ w < δ} ∈ 𝓝 y` using `(isOpen_lt contDiff_fsQ.continuous continuous_const).mem_nhds (by simp [fsQ, hy0, hδ])`.

Use `levi_simple_nonneg (a := 1 + epsT 2 t) (b := -Real.log (Real.log (1 / t))) (by linarith) k hyk ?_ v` and prove the remaining obligations. Use `filter_upwards [hW] with w hw`. Rewrite using `[hφw, projLineAtlas_chart1, hpole w hw]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem llT_psh_chart (t : ℝ) (ht : 0 < t) (ht0 : t ≤ T0) (x : OnePoint ℂ) (j : Fin 2)
    (y : Fin 1 → ℂ) (hy : y ∈ (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x)
    (v : Fin 1 → ℂ) :
    0 ≤ levi (fun w => fsPot.φ x ((p1.chart j).symm w) + llT t ((p1.chart j).symm w) +
      epsT 2 t * fsPot.φ x ((p1.chart j).symm w)) y v := by
  obtain ⟨k, hφw, hk⟩ := fsPot_chart' x j
  have hDo : IsOpen ((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x) :=
    (p1.chart j).isOpen_inter_preimage_symm (fsPot.isOpen_U x)
  have hη := eps_pos ht ht0
  have ha : 1 ≤ 1 + epsT 2 t := by rw [epsT_two]; linarith
  have hyk : k = 1 → y 0 ≠ 0 := hk y hy
  by_cases hyj : j = 1 → y 0 ≠ 0
  · have hNo : IsOpen (((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x) ∩
        {w : Fin 1 → ℂ | j = 1 → w 0 ≠ 0}) := hDo.inter (isOpen_goodSet j)
    have hyN : y ∈ ((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x) ∩
        {w : Fin 1 → ℂ | j = 1 → w 0 ≠ 0} := ⟨hy, hyj⟩
    have hEq : (fun w => fsPot.φ x ((p1.chart j).symm w) + llT t ((p1.chart j).symm w) +
        epsT 2 t * fsPot.φ x ((p1.chart j).symm w)) =ᶠ[𝓝 y]
        fun w => ReciprocityTheory.AnForm.A.regMax (epsT 1 t) (fun i =>
          ![-Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)), -Real.log (Real.log (1 / t))] i +
            (1 + epsT 2 t) * fsGk k (fsQ w)) := by
      filter_upwards [hNo.mem_nhds hyN] with w hw
      rw [hφw, llT_chart_eq t j w hw.2, ReciprocityTheory.AnForm.A.regMax_add_const]
      ring
    rw [levi_congr hEq]
    refine ReciprocityTheory.AnForm.A.regMaxLevi_thm 1 (Fin 2) (epsT 1 t) _
      (fun i w => ![-Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)), -Real.log (Real.log (1 / t))] i +
        (1 + epsT 2 t) * fsGk k (fsQ w)) hNo hη ?_ y hyN v 0 ?_
    · intro i
      have hG : ContDiffOn ℝ ∞ (fun w => fsGk k (fsQ w))
          (((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x) ∩
            {w : Fin 1 → ℂ | j = 1 → w 0 ≠ 0}) :=
        (contDiffOn_fsGk k).mono (fun w hw => hk w hw.1)
      rcases finset_fin_two_eq_cases i with rfl | rfl
      · exact ((((contDiffOn_llwChart j).mono (fun w hw => hw.2)).add
          ((contDiffOn_const (c := 1 + epsT 2 t)).mul hG)).of_le two_le_inf).congr (fun w _ => by simp)
      · exact (((contDiffOn_const (c := -Real.log (Real.log (1 / t)))).add
          ((contDiffOn_const (c := 1 + epsT 2 t)).mul hG)).of_le two_le_inf).congr (fun w _ => by simp)
    · intro i
      rcases finset_fin_two_eq_cases i with rfl | rfl
      · exact levi_combo_nonneg (a := 1 + epsT 2 t) (b := 0) ha k j hyk hyj
          (Eventually.of_forall fun w => by
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; ring) v
      · exact levi_simple_nonneg (a := 1 + epsT 2 t) (b := -Real.log (Real.log (1 / t)))
          (by linarith) k hyk (Eventually.of_forall fun w => by
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; ring) v
  · push Not at hyj
    obtain ⟨rfl, hy0⟩ := hyj
    obtain ⟨δ, hδ, hpole⟩ := llT_near_pole t ht ht0
    have hW : {w : Fin 1 → ℂ | fsQ w < δ} ∈ 𝓝 y :=
      (isOpen_lt contDiff_fsQ.continuous continuous_const).mem_nhds (by simp [fsQ, hy0, hδ])
    refine levi_simple_nonneg (a := 1 + epsT 2 t) (b := -Real.log (Real.log (1 / t)))
      (by linarith) k hyk ?_ v
    filter_upwards [hW] with w hw
    rw [hφw, projLineAtlas_chart1, hpole w hw]
    ring

/- English proof (translation)
Introduce `x j y hy v`. Conclude with `llT_psh_chart t ht ht0 x j y ⟨hy.1, hy.2.1.1⟩ v`.
-/
theorem llT_psh (t : ℝ) (ht : 0 < t) (ht0 : t ≤ T0) :
    IsPsh p1 (fsPot + LocPot.ofFun (llT t) + fsPot.rsmul (epsT 2 t)) := by
  intro x j y hy v
  exact llT_psh_chart t ht ht0 x j y ⟨hy.1, hy.2.1.1⟩ v

/- English proof (translation)
Take `⟨k, hφw, hk⟩` from `fsPot_chart' x j`. Establish `hDo : IsOpen ((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x)` using `(p1.chart j).isOpen_inter_preimage_symm (fsPot.isOpen_U x)`. Establish `hNo` using `hDo.inter (isOpen_goodSet j)`. Use `levi_combo_nonneg (a := 1) (b := 0) le_rfl k j (hk y hy) hyj ?_ v` and prove the remaining obligations. Use `filter_upwards [hNo.mem_nhds ⟨hy, hyj⟩] with w hw`.

Rewrite using `[hφw, projectiveLineLogLog_chart j w hw.2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem llw_psh_chart (x : OnePoint ℂ) (j : Fin 2) (y : Fin 1 → ℂ)
    (hy : y ∈ (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x)
    (hyj : j = 1 → y 0 ≠ 0) (v : Fin 1 → ℂ) :
    0 ≤ levi (fun w => fsPot.φ x ((p1.chart j).symm w) + llw ((p1.chart j).symm w)) y v := by
  obtain ⟨k, hφw, hk⟩ := fsPot_chart' x j
  have hDo : IsOpen ((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x) :=
    (p1.chart j).isOpen_inter_preimage_symm (fsPot.isOpen_U x)
  have hNo := hDo.inter (isOpen_goodSet j)
  refine levi_combo_nonneg (a := 1) (b := 0) le_rfl k j (hk y hy) hyj ?_ v
  filter_upwards [hNo.mem_nhds ⟨hy, hyj⟩] with w hw
  rw [hφw, projectiveLineLogLog_chart j w hw.2]
  ring

/- English proof (translation)
Establish `hs : (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' (bdry projectiveLinePairSection)ᶜ = {w | j = 1 → w 0 ≠ 0}` using `Set.ext fun w => chartV_iff j w`. Rewrite using `[hs]`. Conclude with `(contDiffOn_llwChart j).congr (fun w hw => projectiveLineLogLog_chart j w hw)`.
-/
theorem llw_smoothOn_chart (j : Fin 2) :
    ContDiffOn ℝ ∞ (llw ∘ (p1.chart j).symm)
      ((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' (bdry projectiveLinePairSection)ᶜ) := by
  have hs : (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' (bdry projectiveLinePairSection)ᶜ =
      {w | j = 1 → w 0 ≠ 0} := Set.ext fun w => chartV_iff j w
  rw [hs]
  exact (contDiffOn_llwChart j).congr (fun w hw => projectiveLineLogLog_chart j w hw)

/- English proof (translation)
Use `⟨projLine_isSmoothPotential, fun j => llw_smoothOn_chart j, ?_, fun y _ => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce `x j y hy v`. Conclude with `llw_psh_chart x j y ⟨hy.1, hy.2.1.1⟩ ((chartV_iff j y).1 ⟨hy.1, hy.2.2⟩) v`. Rewrite using `[llw]`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear relations using `[projectiveLineLogLog_le_neg_one y]`.
-/
theorem singWeight : IsSingWeight p1 fsPot projectiveLinePairSection fsPot llw 1 := by
  refine ⟨projLine_isSmoothPotential, fun j => llw_smoothOn_chart j, ?_, fun y _ => ⟨?_, ?_⟩⟩
  · intro x j y hy v
    exact llw_psh_chart x j y ⟨hy.1, hy.2.1.1⟩ ((chartV_iff j y).1 ⟨hy.1, hy.2.2⟩) v
  · rw [llw]; linarith
  · linarith [projectiveLineLogLog_le_neg_one y]

end

end ReciprocityTheory.AnForm.P
