import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {e : ℕ}

/- English proof (translation)
Introduce `z hz`. Take `⟨j, hj⟩` from `R.A.cover z`. Establish `ha : AnalyticAt ℂ ((fun w => R.lift x w p) ∘ (R.A.chart j).symm) (R.A.chart j z)` using `R.holo x p j _ ⟨(R.A.chart j).map_source hj, by`. Simplify using `only [Set.mem_preimage, (R.A.chart j).left_inv hj]`. Conclude with `hz⟩`.

Establish `hc : ContinuousAt (((fun w => R.lift x w p) ∘ (R.A.chart j).symm) ∘ (R.A.chart j)) z` using `ha.continuousAt.comp ((R.A.chart j).continuousAt hj)`. Use `(hc.congr ?_).continuousWithinAt` and prove the remaining obligations. Use `filter_upwards [(R.A.chart j).open_source.mem_nhds hj] with w hw`. Simplify using `only [Function.comp_apply, (R.A.chart j).left_inv hw]`.
-/
theorem continuousOn_lift (R : AnLogRes P J e) (x : R.X) (p : Σ k, ι k) :
    ContinuousOn (fun z => R.lift x z p) (R.U x) := by
  intro z hz
  obtain ⟨j, hj⟩ := R.A.cover z
  have ha : AnalyticAt ℂ ((fun w => R.lift x w p) ∘ (R.A.chart j).symm) (R.A.chart j z) :=
    R.holo x p j _ ⟨(R.A.chart j).map_source hj, by
      simp only [Set.mem_preimage, (R.A.chart j).left_inv hj]; exact hz⟩
  have hc : ContinuousAt (((fun w => R.lift x w p) ∘ (R.A.chart j).symm) ∘ (R.A.chart j)) z :=
    ha.continuousAt.comp ((R.A.chart j).continuousAt hj)
  refine (hc.congr ?_).continuousWithinAt
  filter_upwards [(R.A.chart j).open_source.mem_nhds hj] with w hw
  simp only [Function.comp_apply, (R.A.chart j).left_inv hw]

/- English proof (translation)
Introduce `j`. Establish `hlift : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => R.lift x ((R.A.chart j).symm w)) ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x)`. Use `contDiffOn_pi.mpr fun p => ?_` and prove the remaining obligations. Conclude with `((R.holo x p j).contDiffOn ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).uniqueDiffOn).restrict_scalars ℝ`. Establish `hcomp` using `(hL : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L.h _).comp hlift (fun w hw => (R.mem x _ hw.2).1)`.

Conclude with `hcomp.log fun w hw => (L.pos _ (R.mem x _ hw.2).1).ne'`.
-/
private theorem smoothOn_potOf_of_isSmoothHerm (R : AnLogRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L)
    (x : R.X) : R.A.SmoothOn ((potOf R L).U x) ((potOf R L).φ x) := by
  intro j
  have hlift : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => R.lift x ((R.A.chart j).symm w))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) := by
    refine contDiffOn_pi.mpr fun p => ?_
    exact ((R.holo x p j).contDiffOn ((R.A.chart j).isOpen_inter_preimage_symm
      (R.isOpen_U x)).uniqueDiffOn).restrict_scalars ℝ
  have hcomp := (hL : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L.h _).comp hlift (fun w hw => (R.mem x _ hw.2).1)
  exact hcomp.log fun w hw => (L.pos _ (R.mem x _ hw.2).1).ne'

/- English proof (translation)
Take `⟨c, hc, hxy⟩` from `R.compat x x' y hy`. Use `choose i hi using (R.mem x' y hy.2).1`. Establish `hVo : IsOpen (R.U x ∩ R.U x')` using `(R.isOpen_U x).inter (R.isOpen_U x')`. Establish `hcx : ∀ p, ContinuousOn (fun z => R.lift x z p) (R.U x ∩ R.U x')` using `fun p => (continuousOn_lift R x p).mono Set.inter_subset_left`. Establish `hcx' : ∀ p, ContinuousOn (fun z => R.lift x' z p) (R.U x ∩ R.U x')` using `fun p => (continuousOn_lift R x' p).mono Set.inter_subset_right`.

Set `r : K → R.X → ℂ` to `fun k z => R.lift x z ⟨k, i k⟩ / R.lift x' z ⟨k, i k⟩ / c k`. Set `D : K → Set R.X` to `fun k => (R.U x ∩ R.U x') ∩ (fun z => R.lift x' z ⟨k, i k⟩) ⁻¹' {0}ᶜ`. Establish `hD : ∀ k, IsOpen (D k)` using `fun k => (hcx' _).isOpen_inter_preimage hVo isOpen_compl_singleton`. Establish `hr : ∀ k, ContinuousOn (r k) (D k)` using `fun k => (((hcx _).mono Set.inter_subset_left).div ((hcx' _).mono Set.inter_subset_left) (fun z hz => hz.2)).div_const _`. Set `W : Set R.X` to `(R.U x ∩ R.U x') ∩ ⋂ k, (D k ∩ r k ⁻¹' Complex.slitPlane)`.

Establish `hW : IsOpen W` using `hVo.inter (isOpen_iInter_of_finite fun k => (hr k).isOpen_inter_preimage (hD k) Complex.isOpen_slitPlane)`. Establish `hlk : ∀ k, R.lift x y ⟨k, i k⟩ = c k * R.lift x' y ⟨k, i k⟩` using `fun k => congrFun hxy _`. Establish `hyW : y ∈ W`. Use `⟨hy, Set.mem_iInter.mpr fun k => ⟨⟨hy, hi k⟩, ?_⟩⟩` and prove the remaining obligations. Establish `: r k y = 1`.

Simplify using `only [r, hlk k]`. Clear denominators, using `[hi k, hc k]` for the nonvanishing conditions. Simplify using `only [Set.mem_preimage, this]`. Conclude with `Complex.one_mem_slitPlane`. Use `⟨W, hW, hyW, fun z => ∑ k, (L.a k : ℂ) * (Complex.log (r k z) + (Real.log ‖c k‖ : ℂ)), ?_, ?_⟩` and prove the remaining obligations.

Introduce `j w hw`. Establish `hzV : (R.A.chart j).symm w ∈ R.U x ∩ R.U x'` using `hw.2.1`. Establish `hzk` using `fun k => Set.mem_iInter.mp hw.2.2 k`. Establish `ha : ∀ p, AnalyticAt ℂ (fun w => R.lift x ((R.A.chart j).symm w) p) w` using `fun p => R.holo x p j w ⟨hw.1, hzV.1⟩`. Establish `ha' : ∀ p, AnalyticAt ℂ (fun w => R.lift x' ((R.A.chart j).symm w) p) w` using `fun p => R.holo x' p j w ⟨hw.1, hzV.2⟩`.

Establish `hrk : ∀ k, AnalyticAt ℂ (fun w => r k ((R.A.chart j).symm w)) w` using `fun k => ((ha _).div (ha' _) (hzk k).1.2).div analyticAt_const (hc k)`. Use `show AnalyticAt ℂ (fun w => ∑ k, (L.a k : ℂ) * (Complex.log (r k ((R.A.chart j).symm w)) + (Real.log ‖c k‖ : ℂ))) w`. Use `Finset.analyticAt_fun_sum (𝕜 := ℂ) Finset.univ fun k _ => ?_` and prove the remaining obligations. Conclude with `analyticAt_const.mul (((hrk k).clog (hzk k).2).add analyticAt_const)`. Introduce and unpack `z ⟨⟨hzW, hzx⟩, hzx'⟩`.

Take `⟨c', hc', hz⟩` from `R.compat x x' z ⟨hzx, hzx'⟩`. Establish `hzk` using `fun k => Set.mem_iInter.mp hzW.2 k`. Establish `h2` using `L.pos _ (R.mem x' z hzx').1`. Establish `hsm` using `L.smul c' (R.lift x' z) hc'`. Rewrite `hsm` using `[← hz]`.

Establish `hrz : ∀ k, r k z = c' k / c k`. Introduce `k`. Establish `hne : R.lift x' z ⟨k, i k⟩ ≠ 0` using `(hzk k).1.2`. Simplify using `only [r, congrFun hz ⟨k, i k⟩]`. Clear denominators, using `[hne, hc k]` for the nonvanishing conditions.

Establish `hP : ∀ k ∈ Finset.univ, ‖c' k‖ ^ L.a k ≠ 0` using `fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc' k))`. Simplify using `only [potOf]`. Rewrite using `[hsm, Real.log_mul (Finset.prod_ne_zero_iff.mpr hP) h2.ne', add_sub_cancel_right, Real.log_prod hP, Complex.re_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hrz k, Real.log_zpow]`.

Simplify using `only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_re, Complex.log_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, zero_mul, sub_zero, norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc' k)) (norm_ne_zero_iff.mpr (hc k))]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_holo_re_eq_potOf_sub_on_overlap (R : AnLogRes P J e) (L : HermLine ι) (x x' y : R.X)
    (hy : y ∈ R.U x ∩ R.U x') : ∃ W : Set R.X, IsOpen W ∧ y ∈ W ∧ ∃ G : R.X → ℂ,
      R.A.HoloOn W G ∧ ∀ z ∈ W ∩ R.U x ∩ R.U x',
        (potOf R L).φ x z - (potOf R L).φ x' z = (G z).re := by
  classical
  obtain ⟨c, hc, hxy⟩ := R.compat x x' y hy
  choose i hi using (R.mem x' y hy.2).1
  have hVo : IsOpen (R.U x ∩ R.U x') := (R.isOpen_U x).inter (R.isOpen_U x')
  have hcx : ∀ p, ContinuousOn (fun z => R.lift x z p) (R.U x ∩ R.U x') := fun p =>
    (continuousOn_lift R x p).mono Set.inter_subset_left
  have hcx' : ∀ p, ContinuousOn (fun z => R.lift x' z p) (R.U x ∩ R.U x') := fun p =>
    (continuousOn_lift R x' p).mono Set.inter_subset_right
  let r : K → R.X → ℂ := fun k z => R.lift x z ⟨k, i k⟩ / R.lift x' z ⟨k, i k⟩ / c k
  let D : K → Set R.X := fun k => (R.U x ∩ R.U x') ∩ (fun z => R.lift x' z ⟨k, i k⟩) ⁻¹' {0}ᶜ
  have hD : ∀ k, IsOpen (D k) := fun k => (hcx' _).isOpen_inter_preimage hVo isOpen_compl_singleton
  have hr : ∀ k, ContinuousOn (r k) (D k) := fun k =>
    (((hcx _).mono Set.inter_subset_left).div ((hcx' _).mono Set.inter_subset_left)
      (fun z hz => hz.2)).div_const _
  let W : Set R.X := (R.U x ∩ R.U x') ∩ ⋂ k, (D k ∩ r k ⁻¹' Complex.slitPlane)
  have hW : IsOpen W :=
    hVo.inter (isOpen_iInter_of_finite fun k =>
      (hr k).isOpen_inter_preimage (hD k) Complex.isOpen_slitPlane)
  have hlk : ∀ k, R.lift x y ⟨k, i k⟩ = c k * R.lift x' y ⟨k, i k⟩ := fun k => congrFun hxy _
  have hyW : y ∈ W := by
    refine ⟨hy, Set.mem_iInter.mpr fun k => ⟨⟨hy, hi k⟩, ?_⟩⟩
    have : r k y = 1 := by
      simp only [r, hlk k]
      field_simp [hi k, hc k]
    simp only [Set.mem_preimage, this]
    exact Complex.one_mem_slitPlane
  refine ⟨W, hW, hyW, fun z => ∑ k, (L.a k : ℂ) * (Complex.log (r k z) + (Real.log ‖c k‖ : ℂ)),
    ?_, ?_⟩
  · intro j w hw
    have hzV : (R.A.chart j).symm w ∈ R.U x ∩ R.U x' := hw.2.1
    have hzk := fun k => Set.mem_iInter.mp hw.2.2 k
    have ha : ∀ p, AnalyticAt ℂ (fun w => R.lift x ((R.A.chart j).symm w) p) w := fun p =>
      R.holo x p j w ⟨hw.1, hzV.1⟩
    have ha' : ∀ p, AnalyticAt ℂ (fun w => R.lift x' ((R.A.chart j).symm w) p) w := fun p =>
      R.holo x' p j w ⟨hw.1, hzV.2⟩
    have hrk : ∀ k, AnalyticAt ℂ (fun w => r k ((R.A.chart j).symm w)) w := fun k =>
      ((ha _).div (ha' _) (hzk k).1.2).div analyticAt_const (hc k)
    show AnalyticAt ℂ (fun w => ∑ k, (L.a k : ℂ) *
      (Complex.log (r k ((R.A.chart j).symm w)) + (Real.log ‖c k‖ : ℂ))) w
    refine Finset.analyticAt_fun_sum (𝕜 := ℂ) Finset.univ fun k _ => ?_
    exact analyticAt_const.mul (((hrk k).clog (hzk k).2).add analyticAt_const)
  · rintro z ⟨⟨hzW, hzx⟩, hzx'⟩
    obtain ⟨c', hc', hz⟩ := R.compat x x' z ⟨hzx, hzx'⟩
    have hzk := fun k => Set.mem_iInter.mp hzW.2 k
    have h2 := L.pos _ (R.mem x' z hzx').1
    have hsm := L.smul c' (R.lift x' z) hc'
    rw [← hz] at hsm
    have hrz : ∀ k, r k z = c' k / c k := by
      intro k
      have hne : R.lift x' z ⟨k, i k⟩ ≠ 0 := (hzk k).1.2
      simp only [r, congrFun hz ⟨k, i k⟩]
      field_simp [hne, hc k]
    have hP : ∀ k ∈ Finset.univ, ‖c' k‖ ^ L.a k ≠ 0 := fun k _ =>
      zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc' k))
    simp only [potOf]
    rw [hsm, Real.log_mul (Finset.prod_ne_zero_iff.mpr hP) h2.ne', add_sub_cancel_right,
      Real.log_prod hP, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hrz k, Real.log_zpow]
    simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_re,
      Complex.log_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, zero_mul, sub_zero,
      norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc' k)) (norm_ne_zero_iff.mpr (hc k))]
    ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨smoothOn_potOf_of_isSmoothHerm R hL, fun x x' y hy => exists_holo_re_eq_potOf_sub_on_overlap R L x x' y hy⟩`.
-/
theorem isPotential_potOf (R : AnLogRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) :
    IsPotential R.A (potOf R L) :=
  ⟨smoothOn_potOf_of_isSmoothHerm R hL, fun x x' y hy => exists_holo_re_eq_potOf_sub_on_overlap R L x x' y hy⟩

/- English proof (translation)
Introduce `K _ ι _ P J e R L hL`. Conclude with `isPotential_potOf R hL`.
-/
theorem potOfPotential : PotOfPotentialStatement := by
  intro K _ ι _ P J e R L hL
  exact isPotential_potOf R hL

end ReciprocityTheory.ChartRestriction.G.Geo
