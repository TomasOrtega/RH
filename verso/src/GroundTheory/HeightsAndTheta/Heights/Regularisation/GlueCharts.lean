import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt shrink)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi)

noncomputable section

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

section ChangeOfChart

variable {ψ : OpenPartialHomeomorph X (Fin D → ℂ)}

/- English proof (translation)
Establish `h : ∀ᶠ y in 𝓝 (ψ x), ψ.symm y ∈ (A.chart i).source` using `(ψ.continuousAt_symm (ψ.map_source hx)).preimage_mem_nhds (by rw [ψ.left_inv hx]; exact (A.chart i).open_source.mem_nhds hxi)`. Use `filter_upwards [h] with y hy`. Simplify using `[(A.chart i).left_inv hy]`.
-/
theorem comp_symm_eventuallyEq {E : Type*} (g : X → E) {x : X} (hx : x ∈ ψ.source) (i : Fin A.n)
    (hxi : x ∈ (A.chart i).source) :
    (g ∘ (A.chart i).symm) ∘ (A.chart i ∘ ψ.symm) =ᶠ[𝓝 (ψ x)] g ∘ ψ.symm := by
  have h : ∀ᶠ y in 𝓝 (ψ x), ψ.symm y ∈ (A.chart i).source :=
    (ψ.continuousAt_symm (ψ.map_source hx)).preimage_mem_nhds
      (by rw [ψ.left_inv hx]; exact (A.chart i).open_source.mem_nhds hxi)
  filter_upwards [h] with y hy
  simp [(A.chart i).left_inv hy]

/- English proof (translation)
The claim follows from `(hψ i).2 (ψ x) ⟨ψ.map_source hx, by simp [ψ.left_inv hx, hxi]⟩`.
-/
theorem analyticAt_chart_comp_symm (hψ : IsCompatChart A ψ) {x : X} (hx : x ∈ ψ.source) (i : Fin A.n)
    (hxi : x ∈ (A.chart i).source) : AnalyticAt ℂ (A.chart i ∘ ψ.symm) (ψ x) :=
  (hψ i).2 (ψ x) ⟨ψ.map_source hx, by simp [ψ.left_inv hx, hxi]⟩

/- English proof (translation)
Establish `hτ` using `analyticAt_chart_comp_symm hψ hx i hxi`. Establish `hg' : AnalyticAt ℂ (g ∘ (A.chart i).symm) ((A.chart i ∘ ψ.symm) (ψ x))`. Simplify `hg` using `[ψ.left_inv hx]`. Conclude with `(hg'.comp hτ).congr (comp_symm_eventuallyEq g hx i hxi)`.
-/
theorem analyticAt_comp_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (hψ : IsCompatChart A ψ) {g : X → E} {x : X} (hx : x ∈ ψ.source) (i : Fin A.n)
    (hxi : x ∈ (A.chart i).source) (hg : AnalyticAt ℂ (g ∘ (A.chart i).symm) (A.chart i x)) :
    AnalyticAt ℂ (g ∘ ψ.symm) (ψ x) := by
  have hτ := analyticAt_chart_comp_symm hψ hx i hxi
  have hg' : AnalyticAt ℂ (g ∘ (A.chart i).symm) ((A.chart i ∘ ψ.symm) (ψ x)) := by
    simpa [ψ.left_inv hx] using hg
  exact (hg'.comp hτ).congr (comp_symm_eventuallyEq g hx i hxi)

/- English proof (translation)
Establish `hτ` using `(analyticAt_chart_comp_symm hψ hx i hxi).restrictScalars (𝕜 := ℝ)`. Establish `hg' : ContDiffAt ℝ n (g ∘ (A.chart i).symm) ((A.chart i ∘ ψ.symm) (ψ x))`. Simplify `hg` using `[ψ.left_inv hx]`. Conclude with `(hg'.comp (ψ x) hτ.contDiffAt).congr_of_eventuallyEq (comp_symm_eventuallyEq g hx i hxi).symm`.
-/
theorem contDiffAt_comp_symm (hψ : IsCompatChart A ψ) {n : WithTop ℕ∞} {g : X → ℝ} {x : X}
    (hx : x ∈ ψ.source) (i : Fin A.n) (hxi : x ∈ (A.chart i).source)
    (hg : ContDiffAt ℝ n (g ∘ (A.chart i).symm) (A.chart i x)) :
    ContDiffAt ℝ n (g ∘ ψ.symm) (ψ x) := by
  have hτ := (analyticAt_chart_comp_symm hψ hx i hxi).restrictScalars (𝕜 := ℝ)
  have hg' : ContDiffAt ℝ n (g ∘ (A.chart i).symm) ((A.chart i ∘ ψ.symm) (ψ x)) := by
    simpa [ψ.left_inv hx] using hg
  exact (hg'.comp (ψ x) hτ.contDiffAt).congr_of_eventuallyEq
    (comp_symm_eventuallyEq g hx i hxi).symm

/- English proof (translation)
Take `⟨i, hi⟩` from `A.cover x`. Use `analyticAt_comp_symm hψ hx i hi ((hψ' i).1 (A.chart i x) ⟨(A.chart i).map_source hi, ?_⟩)` and prove the remaining obligations. Simplify using `[(A.chart i).left_inv hi, hx']`.
-/
theorem analyticAt_transition {ψ' : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ)
    (hψ' : IsCompatChart A ψ') {x : X} (hx : x ∈ ψ.source) (hx' : x ∈ ψ'.source) :
    AnalyticAt ℂ (ψ' ∘ ψ.symm) (ψ x) := by
  obtain ⟨i, hi⟩ := A.cover x
  refine analyticAt_comp_symm hψ hx i hi ((hψ' i).1 (A.chart i x) ⟨(A.chart i).map_source hi, ?_⟩)
  simp [(A.chart i).left_inv hi, hx']

/- English proof (translation)
Take `⟨i, hi⟩` from `A.cover x`. Conclude with `contDiffAt_comp_symm hψ hx i hi (smoothOn_contDiffAt hU hf hi hxU)`. Use `where smoothOn_contDiffAt {U : Set X} (hU : IsOpen U) {f : X → ℝ} (hf : A.SmoothOn U f) {i : Fin A.n} {x : X} (hi : x ∈ (A.chart i).source) (hxU : x ∈ U) : ContDiffAt ℝ ∞ (f ∘ (A.chart i).symm) (A.chart i x) := (hf i).contDiffAt (((A.chart i).continuousOn_symm.isOpen_inter_preima …`.
-/
theorem contDiffAt_comp_symm_of_smoothOn (hψ : IsCompatChart A ψ) {U : Set X} (hU : IsOpen U)
    {f : X → ℝ} (hf : A.SmoothOn U f) {x : X} (hxU : x ∈ U) (hx : x ∈ ψ.source) :
    ContDiffAt ℝ ∞ (f ∘ ψ.symm) (ψ x) := by
  obtain ⟨i, hi⟩ := A.cover x
  exact contDiffAt_comp_symm hψ hx i hi (smoothOn_contDiffAt hU hf hi hxU)
where

  smoothOn_contDiffAt {U : Set X} (hU : IsOpen U) {f : X → ℝ} (hf : A.SmoothOn U f) {i : Fin A.n}
      {x : X} (hi : x ∈ (A.chart i).source) (hxU : x ∈ U) :
      ContDiffAt ℝ ∞ (f ∘ (A.chart i).symm) (A.chart i x) :=
    (hf i).contDiffAt (((A.chart i).continuousOn_symm.isOpen_inter_preimage
      (A.chart i).open_target hU).mem_nhds ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hxU]⟩)

/- English proof (translation)
Take `⟨i, hi⟩` from `A.cover x`. Conclude with `analyticAt_comp_symm hψ hx i hi (hG i (A.chart i x) ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hxW]⟩)`.
-/
theorem analyticAt_comp_symm_of_holoOn (hψ : IsCompatChart A ψ) {W : Set X}
    {G : X → ℂ} (hG : A.HoloOn W G) {x : X} (hxW : x ∈ W) (hx : x ∈ ψ.source) :
    AnalyticAt ℂ (G ∘ ψ.symm) (ψ x) := by
  obtain ⟨i, hi⟩ := A.cover x
  exact analyticAt_comp_symm hψ hx i hi
    (hG i (A.chart i x) ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hxW]⟩)

end ChangeOfChart

/- English proof (translation)
Use `⟨fun z hz y hy => ?_, fun z w hd => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ᶠ x in 𝓝[U] z, φ x < y` using `hφ.1 z hz y (by show φ z < y; rw [h hz]; exact hy) filter_upwards [h1, self_mem_nhdsWithin] with x hx hxU`. Rewrite using `[← h hxU]` and apply the resulting hypothesis. Establish `hs : EqOn (fun ζ : ℂ => φ (z + ζ • w)) (fun ζ => ψ (z + ζ • w)) (sphere 0 |(1 : ℝ)|)` using `fun ζ hζ => h (hd ζ (by simp at hζ; rw [hζ]))`. Take `⟨h1, h2⟩` from `hφ.2 z w hd`.

Use `⟨(circleIntegrable_congr hs).1 h1, ?_⟩` and prove the remaining obligations. Establish `hz : z ∈ U` using `by simpa using hd 0 (by simp)`. Rewrite using `[← Real.circleAverage_congr_sphere hs, ← h hz]`. Conclude with `h2`.
-/
theorem isPsh_congr {U : Set (Fin D → ℂ)} {φ ψ : (Fin D → ℂ) → ℝ} (h : EqOn φ ψ U)
    (hφ : IsPsh U φ) : IsPsh U ψ := by
  refine ⟨fun z hz y hy => ?_, fun z w hd => ?_⟩
  · have h1 : ∀ᶠ x in 𝓝[U] z, φ x < y := hφ.1 z hz y (by show φ z < y; rw [h hz]; exact hy)
    filter_upwards [h1, self_mem_nhdsWithin] with x hx hxU
    rwa [← h hxU]
  · have hs : EqOn (fun ζ : ℂ => φ (z + ζ • w)) (fun ζ => ψ (z + ζ • w)) (sphere 0 |(1 : ℝ)|) :=
      fun ζ hζ => h (hd ζ (by simp at hζ; rw [hζ]))
    obtain ⟨h1, h2⟩ := hφ.2 z w hd
    refine ⟨(circleIntegrable_congr hs).1 h1, ?_⟩
    have hz : z ∈ U := by simpa using hd 0 (by simp)
    rw [← Real.circleAverage_congr_sphere hs, ← h hz]
    exact h2

namespace RegChartData

variable (R : RegChartData A)

/- English proof (translation)
Use `isOpen_iff_mem_nhds.2 fun x hx => ?_` and prove the remaining obligations. Take `⟨j, hj⟩` from `R.cover x`. Establish `hxs : x ∈ (R.chart j).source` using `R.mid_subset_source j (R.inner_subset_mid j hj)`. Establish `hV : IsOpen ((R.chart j).source ∩ R.chart j ⁻¹' (coordDiv (R.S j))ᶜ)` using `(R.chart j).continuousOn.isOpen_inter_preimage (R.chart j).open_source (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _).isOpen_compl`. Use `Filter.mem_of_superset (hV.mem_nhds ⟨hxs, (R.mem_Yo j x hxs).1 hx⟩) fun y hy => ?_` and prove the remaining obligations.

Conclude with `(R.mem_Yo j y hy.1).2 hy.2`.
-/
theorem isOpen_Yo : IsOpen R.Yo := by
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  obtain ⟨j, hj⟩ := R.cover x
  have hxs : x ∈ (R.chart j).source := R.mid_subset_source j (R.inner_subset_mid j hj)
  have hV : IsOpen ((R.chart j).source ∩ R.chart j ⁻¹' (coordDiv (R.S j))ᶜ) :=
    (R.chart j).continuousOn.isOpen_inter_preimage (R.chart j).open_source
      (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _).isOpen_compl
  refine Filter.mem_of_superset (hV.mem_nhds ⟨hxs, (R.mem_Yo j x hxs).1 hx⟩) fun y hy => ?_
  exact (R.mem_Yo j y hy.1).2 hy.2

/- English proof (translation)
The claim follows from `(R.mem_Yo j _ ((R.chart j).map_target hy)).2 (by rwa [(R.chart j).right_inv hy])`.
-/
theorem symm_mem_Yo (j : Fin R.N) {y : Fin D → ℂ} (hy : y ∈ (R.chart j).target)
    (hyA : y ∉ coordDiv (R.S j)) : (R.chart j).symm y ∈ R.Yo :=
  (R.mem_Yo j _ ((R.chart j).map_target hy)).2 (by rwa [(R.chart j).right_inv hy])

/- English proof (translation)
Introduce `y hy`. Establish `hq : ContinuousAt (R.q j) y` using `((R.q_smooth j).continuousOn).continuousAt ((R.chart j).open_target.mem_nhds hy.1)`. Establish `hx : (R.chart j).symm y ∈ (R.chart j).source` using `(R.chart j).map_target hy.1`. Establish `hph` using `contDiffAt_comp_symm_of_smoothOn (R.compat j) R.isOpen_Yo R.ph_smooth (R.symm_mem_Yo j hy.1 hy.2) hx`. Rewrite `hph` using `[(R.chart j).right_inv hy.1]`.

Conclude with `(hq.add hph.continuousAt).continuousWithinAt`.
-/
theorem continuousOn_u (j : Fin R.N) :
    ContinuousOn (R.u j) ((R.chart j).target \ coordDiv (R.S j)) := by
  intro y hy
  have hq : ContinuousAt (R.q j) y :=
    ((R.q_smooth j).continuousOn).continuousAt ((R.chart j).open_target.mem_nhds hy.1)
  have hx : (R.chart j).symm y ∈ (R.chart j).source := (R.chart j).map_target hy.1
  have hph := contDiffAt_comp_symm_of_smoothOn (R.compat j) R.isOpen_Yo R.ph_smooth
    (R.symm_mem_Yo j hy.1 hy.2) hx
  rw [(R.chart j).right_inv hy.1] at hph
  exact (hq.add hph.continuousAt).continuousWithinAt

/- English proof (translation)
Take `⟨δ, hδ, hδsub⟩` from `(isCompact_closedBall z t).exists_cthickening_subset_open (R.chart j).open_target hz`. Rewrite `hδsub` using `[cthickening_closedBall hδ.le ht.le]`. Use `set U' := ball z (δ + t) with hU'`. Establish `hU'sub : U' ⊆ (R.chart j).target` using `ball_subset_closedBall.trans hδsub`. Take `⟨M, hM⟩` from `(isCompact_closedBall z (δ + t)).bddAbove_image ((R.q_smooth j).continuousOn.mono hδsub)`.

Establish `hcont : ContinuousOn (R.u j) (U' \ coordDiv (R.S j))` using `(R.continuousOn_u j).mono (sdiff_subset_sdiff_left hU'sub)`. Establish `hpsh : IsPsh (U' \ coordDiv (R.S j)) (R.u j)` using `isPsh_mono (R.u_psh j) (sdiff_subset_sdiff_left hU'sub)`. Establish `hbound : ∀ y ∈ U' \ coordDiv (R.S j), R.u j y ≤ |M + R.Cph| * Real.log (Real.exp 1 + ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹)`. Introduce `y hy`. Establish `hyt : y ∈ (R.chart j).target` using `hU'sub hy.1`.

Establish `h1 : R.q j y ≤ M` using `hM ⟨y, ball_subset_closedBall hy.1, rfl⟩`. Establish `h2 : R.ph ((R.chart j).symm y) ≤ R.Cph` using `R.ph_le _ (R.symm_mem_Yo j hyt hy.2)`. Establish `hy1 : ‖y‖ < 1` using `by simpa using R.target_subset j hyt`. Establish `hs : 0 ≤ ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹` using `Finset.sum_nonneg fun i _ => by`. Rewrite using `[Real.log_inv]`.

Conclude with `neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) ((norm_le_pi_norm y i).trans hy1.le))`. Establish `hL : 1 ≤ Real.log (Real.exp 1 + ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹)`. Use `Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hs (a := Real.exp 1))` as an intermediate fact. Rewrite `this` using `[Real.log_exp]`. Then use the resulting hypothesis. Establish `: R.u j y = R.q j y + R.ph ((R.chart j).symm y)` using `rfl`.

Combine the equalities or inequalities in the displayed calculation. Establish `hext` using `(ReciprocityTheory.AnForm.A.pshExtension_thm D (R.S j) U' (R.u j) |M + R.Cph| isOpen_ball (hU'sub.trans (R.target_subset j)) hcont hpsh hbound).2 K`. Establish `heq : EqOn (limsupExt U' (coordDiv (R.S j)) (fun y => max (R.u j y) (-K))) (R.trunc K j) U'`. Introduce `y hy`. Simplify using `only [RegChartData.trunc, limsupExt]`.

Use `split_ifs with hA`. Use `congr 1`. Rewrite using `[nhdsWithin_restrict ((R.chart j).target \ coordDiv (R.S j)) hy isOpen_ball]`. Use `congr 1`. Use extensionality with `v`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hv1, hv2⟩`. Conclude with `⟨⟨hU'sub hv1, hv2⟩, hv1⟩`. Introduce and unpack `⟨⟨-, hv2⟩, hv1⟩`. Conclude with `⟨hv1, hv2⟩`.

Both sides reduce to the same expression. Establish `htr : IsPsh U' (R.trunc K j)` using `isPsh_congr heq hext`. Take `⟨hopen, hsm, hpm, -⟩` from `(ReciprocityTheory.AnForm.A.mollify_thm D ρ U' (R.trunc K j) isOpen_ball htr).1 t ht`. Establish `hz' : z ∈ shrink U' t` using `closedBall_subset_ball (lt_add_of_pos_left t hδ)`. Establish `hlevi` using `(ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm D (shrink U' t) _ hopen (hsm.of_le (WithTop.coe_le_coe.mpr le_top))).1 hpm`.

Conclude with `⟨hsm.contDiffAt (hopen.mem_nhds hz'), fun w => hlevi.2 z hz' w⟩`.
-/
theorem smoothed_local (ρ : Mollifier D) (K : ℝ) {t : ℝ} (ht : 0 < t) (j : Fin R.N)
    {z : Fin D → ℂ} (hz : closedBall z t ⊆ (R.chart j).target) :
    ContDiffAt ℝ ∞ (R.smoothed ρ K t j) z ∧ ∀ w, 0 ≤ levi (R.smoothed ρ K t j) z w := by
  obtain ⟨δ, hδ, hδsub⟩ :=
    (isCompact_closedBall z t).exists_cthickening_subset_open (R.chart j).open_target hz
  rw [cthickening_closedBall hδ.le ht.le] at hδsub
  set U' := ball z (δ + t) with hU'
  have hU'sub : U' ⊆ (R.chart j).target := ball_subset_closedBall.trans hδsub
  obtain ⟨M, hM⟩ := (isCompact_closedBall z (δ + t)).bddAbove_image
    ((R.q_smooth j).continuousOn.mono hδsub)

  have hcont : ContinuousOn (R.u j) (U' \ coordDiv (R.S j)) :=
    (R.continuousOn_u j).mono (sdiff_subset_sdiff_left hU'sub)
  have hpsh : IsPsh (U' \ coordDiv (R.S j)) (R.u j) :=
    isPsh_mono (R.u_psh j) (sdiff_subset_sdiff_left hU'sub)
  have hbound : ∀ y ∈ U' \ coordDiv (R.S j), R.u j y ≤
      |M + R.Cph| * Real.log (Real.exp 1 + ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹) := by
    intro y hy
    have hyt : y ∈ (R.chart j).target := hU'sub hy.1
    have h1 : R.q j y ≤ M := hM ⟨y, ball_subset_closedBall hy.1, rfl⟩
    have h2 : R.ph ((R.chart j).symm y) ≤ R.Cph := R.ph_le _ (R.symm_mem_Yo j hyt hy.2)
    have hy1 : ‖y‖ < 1 := by simpa using R.target_subset j hyt
    have hs : 0 ≤ ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹ := Finset.sum_nonneg fun i _ => by
      rw [Real.log_inv]
      exact neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) ((norm_le_pi_norm y i).trans hy1.le))
    have hL : 1 ≤ Real.log (Real.exp 1 + ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹) := by
      have := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hs (a := Real.exp 1))
      rwa [Real.log_exp] at this
    have : R.u j y = R.q j y + R.ph ((R.chart j).symm y) := rfl
    calc R.u j y ≤ M + R.Cph := by rw [this]; linarith
      _ ≤ |M + R.Cph| := le_abs_self _
      _ ≤ _ := le_mul_of_one_le_right (abs_nonneg _) hL
  have hext := (ReciprocityTheory.AnForm.A.pshExtension_thm D (R.S j) U' (R.u j) |M + R.Cph| isOpen_ball
    (hU'sub.trans (R.target_subset j)) hcont hpsh hbound).2 K

  have heq : EqOn (limsupExt U' (coordDiv (R.S j)) (fun y => max (R.u j y) (-K)))
      (R.trunc K j) U' := by
    intro y hy
    simp only [RegChartData.trunc, limsupExt]
    split_ifs with hA
    · congr 1
      rw [nhdsWithin_restrict ((R.chart j).target \ coordDiv (R.S j)) hy isOpen_ball]
      congr 1
      ext v
      constructor
      · rintro ⟨hv1, hv2⟩; exact ⟨⟨hU'sub hv1, hv2⟩, hv1⟩
      · rintro ⟨⟨-, hv2⟩, hv1⟩; exact ⟨hv1, hv2⟩
    · rfl
  have htr : IsPsh U' (R.trunc K j) := isPsh_congr heq hext
  obtain ⟨hopen, hsm, hpm, -⟩ := (ReciprocityTheory.AnForm.A.mollify_thm D ρ U' (R.trunc K j) isOpen_ball htr).1 t ht
  have hz' : z ∈ shrink U' t := closedBall_subset_ball (lt_add_of_pos_left t hδ)
  have hlevi := (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm D (shrink U' t) _ hopen
    (hsm.of_le (WithTop.coe_le_coe.mpr le_top))).1 hpm
  exact ⟨hsm.contDiffAt (hopen.mem_nhds hz'), fun w => hlevi.2 z hz' w⟩

end RegChartData

end

end GroundTheory.Heights₂.Heights.Regular
