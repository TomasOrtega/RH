import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt

namespace ReciprocityTheory.AnForm.P.RegularChartScaling

open MeasureTheory Metric Filter Topology Set
open ReciprocityTheory.AnForm.A

noncomputable section

variable {D : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1.mono hVU, fun z w hzw => h.2 z w fun ζ hζ => hVU (hzw ζ hζ)⟩`.
-/
lemma isPsh_mono {U V : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} (h : IsPsh U φ) (hVU : V ⊆ U) :
    IsPsh V φ :=
  ⟨h.1.mono hVU, fun z w hzw => h.2 z w fun ζ hζ => hVU (hzw ζ hζ)⟩

/- English proof (translation)
Use `⟨fun y hy t ht => ?_, fun z w hzw => ?_⟩` and prove the remaining obligations. Establish `hc : ContinuousWithinAt (fun y : Fin D → ℂ => c • y) {y | c • y ∈ U} y` using `(continuous_const_smul c).continuousWithinAt`. Conclude with `(hc.tendsto_nhdsWithin (fun y hy => hy)).eventually (h.1 (c • y) hy t ht)`. Establish `e : ∀ ζ : ℂ, c • (z + ζ • w) = c • z + ζ • (c • w)` using `fun ζ => by`. Rewrite using `[smul_add, smul_comm c ζ w]`.

Use `h.2 (c • z) (c • w) fun ζ hζ => by` as an intermediate fact. Rewrite using `[← e]`. Conclude with `hzw ζ hζ`. Simplify using `only [e]`. Conclude with `this`.
-/
lemma isPsh_scale {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} (h : IsPsh U φ) (c : ℝ) :
    IsPsh {y | c • y ∈ U} (fun y => φ (c • y)) := by
  refine ⟨fun y hy t ht => ?_, fun z w hzw => ?_⟩
  · have hc : ContinuousWithinAt (fun y : Fin D → ℂ => c • y) {y | c • y ∈ U} y :=
      (continuous_const_smul c).continuousWithinAt
    exact (hc.tendsto_nhdsWithin (fun y hy => hy)).eventually (h.1 (c • y) hy t ht)
  · have e : ∀ ζ : ℂ, c • (z + ζ • w) = c • z + ζ • (c • w) := fun ζ => by
      rw [smul_add, smul_comm c ζ w]
    have := h.2 (c • z) (c • w) fun ζ hζ => by
      rw [← e]
      exact hzw ζ hζ
    simp only [e]
    exact this

/- English proof (translation)
Set `u : Fin D → ℂ` to `fun i => if z i = 0 then 1 else z i / (‖z i‖ : ℂ)`. Establish `hu : ∀ i, ‖u i‖ = 1`. Introduce `i`. Distinguish the cases in `h : z i = 0`. Simplify using `[u, h]`.

Simplify using `only [u, if_neg h, norm_div, Complex.norm_real, norm_norm]`. Conclude with `div_self (norm_ne_zero_iff.mpr h)`. Set `w : Fin D → ℂ` to `fun i => (s : ℂ) * u i`. Establish `hw : ‖w‖ ≤ s`. Use `(pi_norm_le_iff_of_nonneg hs.le).mpr fun i => ?_` and prove the remaining obligations.

Simplify using `[w, norm_mul, hu, abs_of_pos hs]`. Use `⟨z + w, ?_, fun i => ?_, (norm_add_le _ _).trans (by linarith)⟩` and prove the remaining obligations. Rewrite using `[mem_closedBall, dist_eq_norm, add_sub_cancel_left]`. Conclude with `hw`. Distinguish the cases in `h : z i = 0`.

Simplify using `[w, u, h, abs_of_pos hs]`. Establish `hzi : 0 < ‖z i‖` using `norm_pos_iff.mpr h`. Establish `hc : (‖z i‖ : ℂ) ≠ 0` using `by exact_mod_cast hzi.ne'`. Establish `e : (z + w) i = ((‖z i‖ + s) / ‖z i‖ : ℝ) * z i`. Simplify using `only [Pi.add_apply, w, u, if_neg h]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_cancel₀ _ hzi.ne']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma exists_far_point (z : Fin D → ℂ) {s : ℝ} (hs : 0 < s) :
    ∃ x ∈ closedBall z s, (∀ i, s ≤ ‖x i‖) ∧ ‖x‖ ≤ ‖z‖ + s := by
  classical
  let u : Fin D → ℂ := fun i => if z i = 0 then 1 else z i / (‖z i‖ : ℂ)
  have hu : ∀ i, ‖u i‖ = 1 := by
    intro i
    by_cases h : z i = 0
    · simp [u, h]
    · simp only [u, if_neg h, norm_div, Complex.norm_real, norm_norm]
      exact div_self (norm_ne_zero_iff.mpr h)
  let w : Fin D → ℂ := fun i => (s : ℂ) * u i
  have hw : ‖w‖ ≤ s := by
    refine (pi_norm_le_iff_of_nonneg hs.le).mpr fun i => ?_
    simp [w, norm_mul, hu, abs_of_pos hs]
  refine ⟨z + w, ?_, fun i => ?_, (norm_add_le _ _).trans (by linarith)⟩
  · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact hw
  · by_cases h : z i = 0
    · simp [w, u, h, abs_of_pos hs]
    · have hzi : 0 < ‖z i‖ := norm_pos_iff.mpr h
      have hc : (‖z i‖ : ℂ) ≠ 0 := by exact_mod_cast hzi.ne'
      have e : (z + w) i = ((‖z i‖ + s) / ‖z i‖ : ℝ) * z i := by
        simp only [Pi.add_apply, w, u, if_neg h]
        push_cast
        field_simp
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
        div_mul_cancel₀ _ hzi.ne']
      linarith

/- English proof (translation)
Introduce and unpack `⟨i, -, hi⟩`. Use `h i` as an intermediate fact. Rewrite `this` using `[hi, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma not_mem_coordDiv_of {S : Finset (Fin D)} {x : Fin D → ℂ} {s : ℝ} (hs : 0 < s)
    (h : ∀ i, s ≤ ‖x i‖) : x ∉ coordDiv S := by
  rintro ⟨i, -, hi⟩
  have := h i
  rw [hi, norm_zero] at this
  linarith

/- English proof (translation)
Simplify using `only [coordDiv, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_zero, hc, false_or]`.
-/
lemma smul_mem_coordDiv_iff {S : Finset (Fin D)} {c : ℝ} (hc : c ≠ 0) (x : Fin D → ℂ) :
    c • x ∈ coordDiv S ↔ x ∈ coordDiv S := by
  simp only [coordDiv, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_zero, hc, false_or]

/- English proof (translation)
Simplify using `only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hR]`. Conclude with `mul_lt_iff_lt_one_right hR`.
-/
lemma mem_ball_smul_iff {R : ℝ} (hR : 0 < R) (y : Fin D → ℂ) :
    R • y ∈ ball (0 : Fin D → ℂ) R ↔ y ∈ ball (0 : Fin D → ℂ) 1 := by
  simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  exact mul_lt_iff_lt_one_right hR

/- English proof (translation)
Rewrite using `[Metric.mem_closure_iff]`. Introduce `ε hε`. Establish `hyR : ‖y‖ < R` using `by simpa using hy`. Use `set m := min ε (R - ‖y‖) with hm`. Establish `hm0 : 0 < m` using `lt_min hε (by linarith)`.

Establish `hfin : {t : ℝ | ∃ i, y i + (t : ℂ) = 0}.Finite`. Establish `hsub : {t : ℝ | ∃ i, y i + (t : ℂ) = 0} ⊆ Set.range (fun i => -(y i).re)`. Introduce and unpack `t ⟨i, hi⟩`. Use `⟨i, ?_⟩` and prove the remaining obligations. Use `congrArg Complex.re hi` as an intermediate fact.

Simplify using `only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at this`. Use `show -(y i).re = t`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(Set.finite_range _).subset hsub`. Take `⟨t, ⟨ht0, htm⟩, htbad⟩` from `((Set.Ioo_infinite hm0).diff hfin).nonempty`.

Establish `hc : ‖fun _ : Fin D => (t : ℂ)‖ ≤ t` using `(pi_norm_le_iff_of_nonneg ht0.le).mpr fun i => by simp [abs_of_pos ht0]`. Use `⟨y + fun _ => (t : ℂ), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_ball, dist_zero_right]`. Use `min_le_right ε (R - ‖y‖)` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.

Introduce and unpack `⟨i, -, hi⟩`. Conclude with `htbad ⟨i, by simpa using hi⟩`. Rewrite using `[dist_eq_norm, sub_add_cancel_left, norm_neg]`. Use `min_le_left ε (R - ‖y‖)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma mem_closure_off (S : Finset (Fin D)) {R : ℝ} {y : Fin D → ℂ} (hy : y ∈ ball (0 : Fin D → ℂ) R) :
    y ∈ closure (ball (0 : Fin D → ℂ) R \ coordDiv S) := by
  classical
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hyR : ‖y‖ < R := by simpa using hy
  set m := min ε (R - ‖y‖) with hm
  have hm0 : 0 < m := lt_min hε (by linarith)
  have hfin : {t : ℝ | ∃ i, y i + (t : ℂ) = 0}.Finite := by
    have hsub : {t : ℝ | ∃ i, y i + (t : ℂ) = 0} ⊆ Set.range (fun i => -(y i).re) := by
      rintro t ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have := congrArg Complex.re hi
      simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at this
      show -(y i).re = t
      linarith
    exact (Set.finite_range _).subset hsub
  obtain ⟨t, ⟨ht0, htm⟩, htbad⟩ := ((Set.Ioo_infinite hm0).diff hfin).nonempty
  have hc : ‖fun _ : Fin D => (t : ℂ)‖ ≤ t :=
    (pi_norm_le_iff_of_nonneg ht0.le).mpr fun i => by simp [abs_of_pos ht0]
  refine ⟨y + fun _ => (t : ℂ), ⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball, dist_zero_right]
    have := min_le_right ε (R - ‖y‖)
    calc ‖y + fun _ => (t : ℂ)‖ ≤ ‖y‖ + ‖fun _ : Fin D => (t : ℂ)‖ := norm_add_le _ _
      _ < R := by linarith
  · rintro ⟨i, -, hi⟩
    exact htbad ⟨i, by simpa using hi⟩
  · rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
    have := min_le_left ε (R - ‖y‖)
    linarith

open Classical in

def extT (S : Finset (Fin D)) (R : ℝ) (v : (Fin D → ℂ) → ℝ) (κ : ℝ) (x : Fin D → ℂ) : ℝ :=
  limsupExt (ball (0 : Fin D → ℂ) 1) (coordDiv S) (fun y => max (v (R • y)) (-κ)) (R⁻¹ • x)

/- English proof (translation)
Use `set v : (Fin D → ℂ) → ℝ := fun y => u (R • y) with hv`. Establish `hmemR : ∀ y : Fin D → ℂ, R • y ∈ ball (0 : Fin D → ℂ) R \ coordDiv S ↔ y ∈ ball (0 : Fin D → ℂ) 1 \ coordDiv S`. Introduce `y`. Rewrite using `[Set.mem_diff, Set.mem_diff, mem_ball_smul_iff hR, smul_mem_coordDiv_iff hR.ne']`. Establish `hset : {y : Fin D → ℂ | R • y ∈ ball (0 : Fin D → ℂ) R \ coordDiv S} = ball (0 : Fin D → ℂ) 1 \ coordDiv S`.

Use extensionality with `y`. Conclude with `hmemR y`. Establish `hvc : ContinuousOn v (ball (0 : Fin D → ℂ) 1 \ coordDiv S)` using `hc.comp (continuous_const_smul R).continuousOn fun y hy => (hmemR y).mpr hy`. Establish `hvp : IsPsh (ball (0 : Fin D → ℂ) 1 \ coordDiv S) v`. Use `isPsh_scale hp R` as an intermediate fact.

Rewrite `this` using `[hset]`. Then use the resulting hypothesis. Establish `hvb : ∀ z ∈ ball (0 : Fin D → ℂ) 1 \ coordDiv S, v z ≤ B * Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖z i‖⁻¹)`. Introduce `z hz`. Establish `h1 : v z ≤ B` using `hub _ ((hmemR z).mpr hz)`. Establish `hsum : 0 ≤ ∑ i ∈ S, Real.log ‖z i‖⁻¹`.

Use `Finset.sum_nonneg fun i hi => ?_` and prove the remaining obligations. Establish `hzi : z i ≠ 0` using `fun h0 => hz.2 ⟨i, hi, h0⟩`. Establish `hlt : ‖z i‖ ≤ 1`. Establish `h3` using `norm_le_pi_norm z i`. Establish `h2 : ‖z‖ < 1` using `by simpa using hz.1`.

Combine the linear equalities and inequalities to obtain the conclusion. Apply `Real.log_nonneg` to reduce the goal to its premises. Rewrite using `[one_le_inv₀ (norm_pos_iff.mpr hzi)]`. Conclude with `hlt`. Establish `hlog : 1 ≤ Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖z i‖⁻¹)`.

Rewrite using `[Real.le_log_iff_exp_le (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hlog hB]`. Establish `hext` using `(pshExtension_thm D S (ball 0 1) v B isOpen_ball subset_rfl hvc hvp hvb).2 κ`. Use `⟨extT S R u κ, rfl, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `h4` using `isPsh_scale hext R⁻¹`. Establish `hset2 : {x : Fin D → ℂ | R⁻¹ • x ∈ ball (0 : Fin D → ℂ) 1} = ball 0 R`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq]`. Rewrite using `[← mem_ball_smul_iff hR, smul_inv_smul₀ hR.ne']`.

Rewrite `h4` using `[hset2]`. Conclude with `h4`. Introduce `x hx`. Establish `hx' : R⁻¹ • x ∉ coordDiv S`. Rewrite using `[smul_mem_coordDiv_iff (inv_ne_zero hR.ne')]`.

Conclude with `hx.2`. Simplify using `only [extT, limsupExt, if_neg hx', smul_inv_smul₀ hR.ne']`. Introduce `x hx δ hδ`. Distinguish the cases in `hxA : x ∈ coordDiv S`. Use `set x' := R⁻¹ • x with hx'`.

Establish `hxeq : R • x' = x` using `by rw [hx', smul_inv_smul₀ hR.ne']`. Establish `hx'A : x' ∈ coordDiv S` using `(smul_mem_coordDiv_iff (inv_ne_zero hR.ne') x).mpr hxA`. Establish `hx'U : x' ∈ ball (0 : Fin D → ℂ) 1`. Rewrite using `[← mem_ball_smul_iff hR, hxeq]`. Conclude with `hx`.

Use `set F : (Fin D → ℂ) → ℝ := fun y => max (u (R • y)) (-κ) with hF`. Establish `hw : extT S R u κ x = limsup F (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x')`. Simplify using `only [extT, limsupExt]`. Rewrite using `[if_pos ((smul_mem_coordDiv_iff (inv_ne_zero hR.ne') x).mpr hxA)]`. Use `haveI : (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x').NeBot := mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_off S hx'U)`.

Establish `hcob : IsCoboundedUnder (· ≤ ·) (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x') F` using `isCoboundedUnder_le_of_le _ (fun y => le_max_right _ _)`. Establish `hfreq` using `frequently_lt_of_lt_limsup hcob (show limsup F (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x') - δ < limsup F (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x') by linarith)`. Establish `hev : ∀ᶠ y in 𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x', y ∈ ball (0 : Fin D → ℂ) 1 \ coordDiv S ∧ dist y x' < δ / R` using `Filter.Eventually.and eventually_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x' (div_pos hδ hR)))`. Take `⟨y, hy1, hy2, hy3⟩` from `(hfreq.and_eventually hev).exists`. Use `⟨R • y, (hmemR y).mpr hy2, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hxeq, dist_smul₀, Real.norm_eq_abs, abs_of_pos hR]`. Combine the equalities or inequalities in the displayed calculation. Establish `hFy : F y = max (u (R • y)) (-κ)` using `rfl`. Rewrite using `[hw]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hx' : R⁻¹ • x ∉ coordDiv S`. Rewrite using `[smul_mem_coordDiv_iff (inv_ne_zero hR.ne')]`. Conclude with `hxA`. Establish `hwx : extT S R u κ x = max (u x) (-κ)`. Simplify using `only [extT, limsupExt, if_neg hx', smul_inv_smul₀ hR.ne']`.

Conclude with `⟨x, ⟨hx, hxA⟩, by simp [hδ], by linarith⟩`.
-/
lemma ext_exists (S : Finset (Fin D)) {R : ℝ} (hR : 0 < R) {u : (Fin D → ℂ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hc : ContinuousOn u (ball 0 R \ coordDiv S))
    (hp : IsPsh (ball 0 R \ coordDiv S) u) (hub : ∀ x ∈ ball 0 R \ coordDiv S, u x ≤ B)
    (κ : ℝ) :
    ∃ w : (Fin D → ℂ) → ℝ, w = extT S R u κ ∧ IsPsh (ball 0 R) w ∧
      (∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, w x = max (u x) (-κ)) ∧
      ∀ x ∈ ball (0 : Fin D → ℂ) R, ∀ δ > 0, ∃ y ∈ ball (0 : Fin D → ℂ) R \ coordDiv S,
        dist y x < δ ∧ w x ≤ max (u y) (-κ) + δ := by
  classical
  set v : (Fin D → ℂ) → ℝ := fun y => u (R • y) with hv
  have hmemR : ∀ y : Fin D → ℂ, R • y ∈ ball (0 : Fin D → ℂ) R \ coordDiv S ↔
      y ∈ ball (0 : Fin D → ℂ) 1 \ coordDiv S := by
    intro y
    rw [Set.mem_diff, Set.mem_diff, mem_ball_smul_iff hR, smul_mem_coordDiv_iff hR.ne']
  have hset : {y : Fin D → ℂ | R • y ∈ ball (0 : Fin D → ℂ) R \ coordDiv S} =
      ball (0 : Fin D → ℂ) 1 \ coordDiv S := by
    ext y
    exact hmemR y
  have hvc : ContinuousOn v (ball (0 : Fin D → ℂ) 1 \ coordDiv S) :=
    hc.comp (continuous_const_smul R).continuousOn fun y hy => (hmemR y).mpr hy
  have hvp : IsPsh (ball (0 : Fin D → ℂ) 1 \ coordDiv S) v := by
    have := isPsh_scale hp R
    rwa [hset] at this
  have hvb : ∀ z ∈ ball (0 : Fin D → ℂ) 1 \ coordDiv S,
      v z ≤ B * Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖z i‖⁻¹) := by
    intro z hz
    have h1 : v z ≤ B := hub _ ((hmemR z).mpr hz)
    have hsum : 0 ≤ ∑ i ∈ S, Real.log ‖z i‖⁻¹ := by
      refine Finset.sum_nonneg fun i hi => ?_
      have hzi : z i ≠ 0 := fun h0 => hz.2 ⟨i, hi, h0⟩
      have hlt : ‖z i‖ ≤ 1 := by
        have h3 := norm_le_pi_norm z i
        have h2 : ‖z‖ < 1 := by simpa using hz.1
        linarith
      apply Real.log_nonneg
      rw [one_le_inv₀ (norm_pos_iff.mpr hzi)]
      exact hlt
    have hlog : 1 ≤ Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖z i‖⁻¹) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hlog hB]
  have hext := (pshExtension_thm D S (ball 0 1) v B isOpen_ball subset_rfl hvc hvp hvb).2 κ
  refine ⟨extT S R u κ, rfl, ?_, ?_, ?_⟩
  · have h4 := isPsh_scale hext R⁻¹
    have hset2 : {x : Fin D → ℂ | R⁻¹ • x ∈ ball (0 : Fin D → ℂ) 1} = ball 0 R := by
      ext x
      simp only [Set.mem_setOf_eq]
      rw [← mem_ball_smul_iff hR, smul_inv_smul₀ hR.ne']
    rw [hset2] at h4
    exact h4
  · intro x hx
    have hx' : R⁻¹ • x ∉ coordDiv S := by
      rw [smul_mem_coordDiv_iff (inv_ne_zero hR.ne')]
      exact hx.2
    simp only [extT, limsupExt, if_neg hx', smul_inv_smul₀ hR.ne']
  · intro x hx δ hδ
    by_cases hxA : x ∈ coordDiv S
    · set x' := R⁻¹ • x with hx'
      have hxeq : R • x' = x := by rw [hx', smul_inv_smul₀ hR.ne']
      have hx'A : x' ∈ coordDiv S := (smul_mem_coordDiv_iff (inv_ne_zero hR.ne') x).mpr hxA
      have hx'U : x' ∈ ball (0 : Fin D → ℂ) 1 := by
        rw [← mem_ball_smul_iff hR, hxeq]
        exact hx
      set F : (Fin D → ℂ) → ℝ := fun y => max (u (R • y)) (-κ) with hF
      have hw : extT S R u κ x = limsup F (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x') := by
        simp only [extT, limsupExt]
        rw [if_pos ((smul_mem_coordDiv_iff (inv_ne_zero hR.ne') x).mpr hxA)]
      haveI : (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x').NeBot :=
        mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_off S hx'U)
      have hcob : IsCoboundedUnder (· ≤ ·) (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x') F :=
        isCoboundedUnder_le_of_le _ (fun y => le_max_right _ _)
      have hfreq := frequently_lt_of_lt_limsup hcob
        (show limsup F (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x') - δ <
          limsup F (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x') by linarith)
      have hev : ∀ᶠ y in 𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x',
          y ∈ ball (0 : Fin D → ℂ) 1 \ coordDiv S ∧ dist y x' < δ / R :=
        Filter.Eventually.and eventually_mem_nhdsWithin
          (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x' (div_pos hδ hR)))
      obtain ⟨y, hy1, hy2, hy3⟩ := (hfreq.and_eventually hev).exists
      refine ⟨R • y, (hmemR y).mpr hy2, ?_, ?_⟩
      · rw [← hxeq, dist_smul₀, Real.norm_eq_abs, abs_of_pos hR]
        calc R * dist y x' < R * (δ / R) := mul_lt_mul_of_pos_left hy3 hR
          _ = δ := by field_simp
      · have hFy : F y = max (u (R • y)) (-κ) := rfl
        rw [hw]
        linarith
    · have hx' : R⁻¹ • x ∉ coordDiv S := by
        rw [smul_mem_coordDiv_iff (inv_ne_zero hR.ne')]
        exact hxA
      have hwx : extT S R u κ x = max (u x) (-κ) := by
        simp only [extT, limsupExt, if_neg hx', smul_inv_smul₀ hR.ne']
      exact ⟨x, ⟨hx, hxA⟩, by simp [hδ], by linarith⟩

end

end ReciprocityTheory.AnForm.P.RegularChartScaling
