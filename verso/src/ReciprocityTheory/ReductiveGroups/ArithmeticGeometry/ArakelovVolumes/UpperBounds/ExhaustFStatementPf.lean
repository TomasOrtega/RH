import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfE

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Topology Filter ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ContDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `h1 : e.symm w ∈ e.source` using `e.map_target hw`. Rewrite using `[he h1]`. Conclude with `e.right_inv hw`.
-/
private theorem val_chart_symm_apply {n : ℕ} {U : Set (V n)} (e : OpenPartialHomeomorph U (V n))
    (he : IsChart n Subtype.val e) {w : V n} (hw : w ∈ e.target) : ((e.symm w : U) : V n) = w := by
  have h1 : e.symm w ∈ e.source := e.map_target hw
  rw [he h1]
  exact e.right_inv hw

/- English proof (translation)
Use `filter_upwards [e.open_target.mem_nhds hw] with y hy`. Simplify using `only [Function.comp_apply]`. Rewrite using `[val_chart_symm_apply e he hy]`.
-/
private theorem comp_chart_symm_eventuallyEq_of_mem_target {n : ℕ} {U : Set (V n)} (e : OpenPartialHomeomorph U (V n))
    (he : IsChart n Subtype.val e) (g : V n → ℂ) {w : V n} (hw : w ∈ e.target) :
    (fun y : U => g y.1) ∘ e.symm =ᶠ[nhds w] g := by
  filter_upwards [e.open_target.mem_nhds hw] with y hy
  simp only [Function.comp_apply]
  rw [val_chart_symm_apply e he hy]

/- English proof (translation)
Take `⟨e, hy, he⟩` from `hz y`. Conclude with `⟨e, fun a _ => by rw [he], hy⟩`.
-/
private theorem exists_isChart_subtype_val {n : ℕ} {U : Set (V n)} (hz : IsLocalHomeomorph (Subtype.val : U → V n))
    (y : U) : ∃ e : OpenPartialHomeomorph U (V n), IsChart n Subtype.val e ∧ y ∈ e.source := by
  obtain ⟨e, hy, he⟩ := hz y
  exact ⟨e, fun a _ => by rw [he], hy⟩

/- English proof (translation)
Establish `hex` using `exists_isChart_subtype_val hz y`. Unfold `db`. Rewrite using `[dif_pos hex]`. Establish `hc` using `Classical.choose_spec hex`. Establish `hw : y.1 ∈ (Classical.choose hex).target`.

Rewrite using `[hc.1 hc.2]`. Conclude with `(Classical.choose hex).map_source hc.2`. Unfold `wdb`. Rewrite using `[(comp_chart_symm_eventuallyEq_of_mem_target _ hc.1 g hw).fderiv_eq]`.
-/
private theorem db_subtype_val_eq_wdb {n : ℕ} {U : Set (V n)} (hz : IsLocalHomeomorph (Subtype.val : U → V n))
    (g : V n → ℂ) (k : Fin n) (y : U) : db n Subtype.val k (fun y : U => g y.1) y = wdb n k g y.1 := by
  have hex := exists_isChart_subtype_val hz y
  unfold db
  rw [dif_pos hex]
  have hc := Classical.choose_spec hex
  have hw : y.1 ∈ (Classical.choose hex).target := by
    rw [hc.1 hc.2]
    exact (Classical.choose hex).map_source hc.2
  unfold wdb
  rw [(comp_chart_symm_eventuallyEq_of_mem_target _ hc.1 g hw).fderiv_eq]

/- English proof (translation)
Establish `hex` using `exists_isChart_subtype_val hz y`. Unfold `d`. Rewrite using `[dif_pos hex]`. Establish `hc` using `Classical.choose_spec hex`. Establish `hw : y.1 ∈ (Classical.choose hex).target`.

Rewrite using `[hc.1 hc.2]`. Conclude with `(Classical.choose hex).map_source hc.2`. Unfold `wd`. Rewrite using `[(comp_chart_symm_eventuallyEq_of_mem_target _ hc.1 g hw).fderiv_eq]`.
-/
private theorem d_subtype_val_eq_wd {n : ℕ} {U : Set (V n)} (hz : IsLocalHomeomorph (Subtype.val : U → V n))
    (g : V n → ℂ) (k : Fin n) (y : U) : d n Subtype.val k (fun y : U => g y.1) y = wd n k g y.1 := by
  have hex := exists_isChart_subtype_val hz y
  unfold d
  rw [dif_pos hex]
  have hc := Classical.choose_spec hex
  have hw : y.1 ∈ (Classical.choose hex).target := by
    rw [hc.1 hc.2]
    exact (Classical.choose hex).map_source hc.2
  unfold wd
  rw [(comp_chart_symm_eventuallyEq_of_mem_target _ hc.1 g hw).fderiv_eq]

/- English proof (translation)
Unfold `Levi leviV`. Use `beta_reduce`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h1 : db n Subtype.val k (fun y : U => ((ph y.1 : ℝ) : ℂ)) = fun y : U => wdb n k (fun w => ((ph w : ℝ) : ℂ)) y.1`. Use function extensionality and compare the values at `fun y => db_subtype_val_eq_wdb hz (fun w => ((ph w : ℝ) : ℂ)) k y`.

Rewrite using `[h1, d_subtype_val_eq_wd hz (wdb n k (fun w => ((ph w : ℝ) : ℂ))) j x]`.
-/
private theorem levi_lemma_6 {n : ℕ} {U : Set (V n)} (hz : IsLocalHomeomorph (Subtype.val : U → V n))
    (ph : V n → ℝ) (x : U) (ξ : Fin n → ℂ) :
    Levi n Subtype.val (fun y : U => ph y.1) x ξ = leviV n (fun w => ((ph w : ℝ) : ℂ)) x.1 ξ := by
  unfold Levi leviV
  beta_reduce
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have h1 : db n Subtype.val k (fun y : U => ((ph y.1 : ℝ) : ℂ)) =
      fun y : U => wdb n k (fun w => ((ph w : ℝ) : ℂ)) y.1 :=
    funext fun y => db_subtype_val_eq_wdb hz (fun w => ((ph w : ℝ) : ℂ)) k y
  rw [h1, d_subtype_val_eq_wd hz (wdb n k (fun w => ((ph w : ℝ) : ℂ))) j x]

/- English proof (translation)
Establish `hev : ∀ k, wdb n k (fun w => g1 w + g2 w) =ᶠ[nhds y] fun w => wdb n k g1 w + wdb n k g2 w`. Introduce `k`. Use `filter_upwards [h1, h2] with w hw1 hw2`. Apply the tactic sequence `have d1 : DifferentiableAt ℝ g1 w := hw1.differentiableAt (by first | norm_num | simp)`. Apply the tactic sequence `have d2 : DifferentiableAt ℝ g2 w := hw2.differentiableAt (by first | norm_num | simp)`.

Unfold `wdb`. Use `first`. Consider the case `rw [fderiv_fun_add d1 d2]`. Consider the case `rw [fderiv_add' d1 d2]`. Consider the case `rw [show (fun w => g1 w + g2 w) = g1 + g2 from rfl, fderiv_add d1 d2]`.

Simplify using `only [ContinuousLinearMap.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdiff : ∀ g : V n → ℂ, ContDiffAt ℝ ∞ g y → ∀ k, DifferentiableAt ℝ (wdb n k g) y`. Introduce `g hg k`. Establish `hf : ContDiffAt ℝ 1 (fderiv ℝ g) y` using `hg.fderiv_right (by first`.

Consider the case `exact WithTop.coe_le_coe.mpr le_top`. Consider the case `exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)`. Consider the case `(norm_num; done)`. Consider the case `(simp; done))`. Apply the tactic sequence `have hfd : DifferentiableAt ℝ (fderiv ℝ g) y := hf.differentiableAt (by first | exact one_ne_zero | exact le_rfl | simp)`.

Establish `ha : DifferentiableAt ℝ (fun w => fderiv ℝ g w (bas n k)) y` using `hfd.clm_apply (differentiableAt_const _)`. Establish `hb : DifferentiableAt ℝ (fun w => fderiv ℝ g w (Complex.I • bas n k)) y` using `hfd.clm_apply (differentiableAt_const _)`. Unfold `wdb`. Use `first`. Consider the case `exact (ha.fun_add (hb.const_mul Complex.I)).div_const 2`.

Consider the case `exact (ha.add (hb.const_mul Complex.I)).div_const 2`. Consider the case `fun_prop`. Unfold `leviV`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `e1 : wd n j (wdb n k (fun w => g1 w + g2 w)) y = wd n j (wdb n k g1) y + wd n j (wdb n k g2) y`. Unfold `wd`. Rewrite using `[(hev k).fderiv_eq]`.

Use `first`. Consider the case `rw [fderiv_fun_add (hdiff g1 h1.self_of_nhds k) (hdiff g2 h2.self_of_nhds k)]`. Consider the case `rw [fderiv_add' (hdiff g1 h1.self_of_nhds k) (hdiff g2 h2.self_of_nhds k)]`. Consider the case `rw [show (fun w => wdb n k g1 w + wdb n k g2 w) = wdb n k g1 + wdb n k g2 from rfl, fderiv_add (hdiff g1 h1.self_of_nhds k) (hdiff g2 h2.self_of_nhds k)]`. Simplify using `only [ContinuousLinearMap.add_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem leviV_add {n : ℕ} (g1 g2 : V n → ℂ) (y : V n)
    (h1 : ∀ᶠ w in nhds y, ContDiffAt ℝ ∞ g1 w) (h2 : ∀ᶠ w in nhds y, ContDiffAt ℝ ∞ g2 w)
    (ξ : Fin n → ℂ) :
    leviV n (fun w => g1 w + g2 w) y ξ = leviV n g1 y ξ + leviV n g2 y ξ := by
  have hev : ∀ k, wdb n k (fun w => g1 w + g2 w) =ᶠ[nhds y] fun w => wdb n k g1 w + wdb n k g2 w := by
    intro k
    filter_upwards [h1, h2] with w hw1 hw2
    have d1 : DifferentiableAt ℝ g1 w := hw1.differentiableAt (by first | norm_num | simp)
    have d2 : DifferentiableAt ℝ g2 w := hw2.differentiableAt (by first | norm_num | simp)
    unfold wdb
    first
      | rw [fderiv_fun_add d1 d2]
      | rw [fderiv_add' d1 d2]
      | rw [show (fun w => g1 w + g2 w) = g1 + g2 from rfl, fderiv_add d1 d2]
    simp only [ContinuousLinearMap.add_apply]
    ring
  have hdiff : ∀ g : V n → ℂ, ContDiffAt ℝ ∞ g y → ∀ k, DifferentiableAt ℝ (wdb n k g) y := by
    intro g hg k
    have hf : ContDiffAt ℝ 1 (fderiv ℝ g) y := hg.fderiv_right (by
      first
        | exact WithTop.coe_le_coe.mpr le_top
        | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
        | (norm_num; done)
        | (simp; done))
    have hfd : DifferentiableAt ℝ (fderiv ℝ g) y := hf.differentiableAt (by first | exact one_ne_zero | exact le_rfl | simp)
    have ha : DifferentiableAt ℝ (fun w => fderiv ℝ g w (bas n k)) y :=
      hfd.clm_apply (differentiableAt_const _)
    have hb : DifferentiableAt ℝ (fun w => fderiv ℝ g w (Complex.I • bas n k)) y :=
      hfd.clm_apply (differentiableAt_const _)
    unfold wdb
    first
      | exact (ha.fun_add (hb.const_mul Complex.I)).div_const 2
      | exact (ha.add (hb.const_mul Complex.I)).div_const 2
      | fun_prop
  unfold leviV
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 : wd n j (wdb n k (fun w => g1 w + g2 w)) y =
      wd n j (wdb n k g1) y + wd n j (wdb n k g2) y := by
    unfold wd
    rw [(hev k).fderiv_eq]
    first
      | rw [fderiv_fun_add (hdiff g1 h1.self_of_nhds k) (hdiff g2 h2.self_of_nhds k)]
      | rw [fderiv_add' (hdiff g1 h1.self_of_nhds k) (hdiff g2 h2.self_of_nhds k)]
      | rw [show (fun w => wdb n k g1 w + wdb n k g2 w) = wdb n k g1 + wdb n k g2 from rfl,
          fderiv_add (hdiff g1 h1.self_of_nhds k) (hdiff g2 h2.self_of_nhds k)]
    simp only [ContinuousLinearMap.add_apply]
    ring
  rw [e1]
  ring

/- English proof (translation)
Introduce `r X x0 ho`. Establish `hU : IsOpen (OmF X x0)` using `ExF.isOpen_OmF X x0`. Establish `hz : IsLocalHomeomorph (Subtype.val : OmF X x0 → _)` using `by first`. Consider the case `exact hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph`. Consider the case `exact hU.openEmbedding_subtype_val.isLocalHomeomorph`.

Establish `hgE : ∀ w ∈ OmF X x0, ContDiffAt ℝ ∞ (fun w => ((eF X x0 w : ℝ) : ℂ)) w` using `fun w hw => Complex.ofRealCLM.contDiff.contDiffAt.comp w (ExF.eF_contDiffAt X x0 ho hw)`. Establish `hg1 : ∀ w ∈ OmF X x0, ContDiffAt ℝ ∞ (fun w => ((rhF X x0 w : ℝ) : ℂ)) w` using `fun w hw => Complex.ofRealCLM.contDiff.contDiffAt.comp w (ExF.rhF_contDiffAt X x0 ho hw)`. Establish `hg2 : ∀ {m : ℕ} (w : V m), ContDiffAt ℝ ∞ (fun w : V m => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ)) w` using `fun w => Complex.ofRealCLM.contDiff.contDiffAt.comp w ((contDiff_const.add (contDiff_norm_sq ℂ)).log fun w => by positivity).contDiffAt`. Use `⟨{ z := Subtype.val isLocalHomeomorph := hz e := (fun y => eF X x0 y.1) smooth_e := ?_ levi_e := ?_ isCompact_le := ?_ }, rfl, rfl⟩` and prove the remaining obligations. Unfold `SmoothR Smooth`.

Introduce `e he`. Use `ContDiffOn.congr (f := fun w => ((eF X x0 w : ℝ) : ℂ)) (fun w hw => (hgE w ?_).contDiffWithinAt) (fun w hw => ?_)` and prove the remaining obligations. Rewrite using `[← val_chart_symm_apply e he hw]`. Conclude with `(e.symm w).2`. Simplify using `only [Function.comp_apply]`.

Rewrite using `[val_chart_symm_apply e he hw]`. Unfold `LeviNonneg`. Introduce `x ξ`. Rewrite using `[levi_lemma_6 hz (eF X x0) x ξ]`. Establish `hsplit : (fun w => ((eF X x0 w : ℝ) : ℂ)) = fun w => ((rhF X x0 w : ℝ) : ℂ) + ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ)`.

Use function extensionality and compare the values at `w`. Simplify using `[eF]`. Establish `hev1 : ∀ᶠ w in nhds x.1, ContDiffAt ℝ ∞ (fun w => ((rhF X x0 w : ℝ) : ℂ)) w` using `Filter.eventually_of_mem (hU.mem_nhds x.2) hg1`. Establish `hev2 : ∀ᶠ w in nhds x.1, ContDiffAt ℝ ∞ (fun w => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ)) w` using `Filter.Eventually.of_forall fun w => hg2 w`. Rewrite using `[hsplit, leviV_add _ _ _ hev1 hev2, Complex.add_re]`.

Conclude with `add_nonneg (ExF.levi_rhF_nonneg X x0 ho x.2 ξ) (ExF.leviT_nonneg _ ξ)`. Introduce `a`. Establish `hc` using `ExF.isCompact_subF X x0 ho a`. Rewrite using `[Subtype.isCompact_iff]`. Use `hc using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y.2, hy⟩`. Introduce and unpack `⟨hw, ha⟩`.

Conclude with `⟨⟨w, hw⟩, ha, rfl⟩`.
-/
theorem exhaustF_holds : ExhaustFStatement (E := E) := by
  intro r X x0 ho
  have hU : IsOpen (OmF X x0) := ExF.isOpen_OmF X x0
  have hz : IsLocalHomeomorph (Subtype.val : OmF X x0 → _) := by
    first
      | exact hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph
      | exact hU.openEmbedding_subtype_val.isLocalHomeomorph
  have hgE : ∀ w ∈ OmF X x0, ContDiffAt ℝ ∞ (fun w => ((eF X x0 w : ℝ) : ℂ)) w := fun w hw =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp w (ExF.eF_contDiffAt X x0 ho hw)
  have hg1 : ∀ w ∈ OmF X x0, ContDiffAt ℝ ∞ (fun w => ((rhF X x0 w : ℝ) : ℂ)) w := fun w hw =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp w (ExF.rhF_contDiffAt X x0 ho hw)
  have hg2 : ∀ {m : ℕ} (w : V m), ContDiffAt ℝ ∞ (fun w : V m => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ)) w :=
    fun w => Complex.ofRealCLM.contDiff.contDiffAt.comp w
      ((contDiff_const.add (contDiff_norm_sq ℂ)).log fun w => by positivity).contDiffAt
  refine ⟨{
      z := Subtype.val
      isLocalHomeomorph := hz
      e := (fun y => eF X x0 y.1)
      smooth_e := ?_
      levi_e := ?_
      isCompact_le := ?_ }, rfl, rfl⟩
  · unfold SmoothR Smooth
    intro e he
    refine ContDiffOn.congr (f := fun w => ((eF X x0 w : ℝ) : ℂ))
      (fun w hw => (hgE w ?_).contDiffWithinAt) (fun w hw => ?_)
    · rw [← val_chart_symm_apply e he hw]
      exact (e.symm w).2
    · simp only [Function.comp_apply]
      rw [val_chart_symm_apply e he hw]
  · unfold LeviNonneg
    intro x ξ
    rw [levi_lemma_6 hz (eF X x0) x ξ]
    have hsplit : (fun w => ((eF X x0 w : ℝ) : ℂ)) =
        fun w => ((rhF X x0 w : ℝ) : ℂ) + ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ) := by
      funext w
      simp [eF]
    have hev1 : ∀ᶠ w in nhds x.1, ContDiffAt ℝ ∞ (fun w => ((rhF X x0 w : ℝ) : ℂ)) w :=
      Filter.eventually_of_mem (hU.mem_nhds x.2) hg1
    have hev2 : ∀ᶠ w in nhds x.1, ContDiffAt ℝ ∞ (fun w => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ)) w :=
      Filter.Eventually.of_forall fun w => hg2 w
    rw [hsplit, leviV_add _ _ _ hev1 hev2, Complex.add_re]
    exact add_nonneg (ExF.levi_rhF_nonneg X x0 ho x.2 ξ) (ExF.leviT_nonneg _ ξ)
  · intro a
    have hc := ExF.isCompact_subF X x0 ho a
    rw [Subtype.isCompact_iff]
    convert hc using 1
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hw, ha⟩
      exact ⟨⟨w, hw⟩, ha, rfl⟩

end ReciprocityTheory.ChartRestriction.G.AR.Up
