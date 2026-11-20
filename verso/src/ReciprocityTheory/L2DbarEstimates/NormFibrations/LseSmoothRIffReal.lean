import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology
open scoped ContDiff

/- English proof (translation)
Use `first`. Consider the case `exact WithTop.coe_le_coe.mpr le_top`. Consider the case `exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)`. Consider the case `simp`. Consider the case `decide`.
-/
theorem lse_two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
  first
  | exact WithTop.coe_le_coe.mpr le_top
  | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
  | simp
  | decide

/- English proof (translation)
Unfold `SmoothR Smooth`. Use `forall_congr' fun e => imp_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Establish `h1` using `Complex.reCLM.contDiff.comp_contDiffOn h`. Simplify `h1` using `[Function.comp_def, Complex.reCLM_apply]`. Conclude with `Complex.ofRealCLM.contDiff.comp_contDiffOn h`.
-/
theorem lse_smoothR_iff_real {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℝ) :
    SmoothR n z f ↔ ∀ e : OpenPartialHomeomorph M (V n), IsChart n z e →
      ContDiffOn ℝ ∞ (f ∘ e.symm) e.target := by
  unfold SmoothR Smooth
  refine forall_congr' fun e => imp_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · have h1 := Complex.reCLM.contDiff.comp_contDiffOn h
    simpa [Function.comp_def, Complex.reCLM_apply] using h1
  · exact Complex.ofRealCLM.contDiff.comp_contDiffOn h

/- English proof (translation)
Take `⟨f, hxf, hzf⟩` from `hz x`. Establish `hzx : z x = e x` using `he hx`. Establish `hzx' : z x = e' x` using `he' hx'`. Establish `h1 : ∀ᶠ w in 𝓝 (z x), e.symm w ∈ f.source`. Rewrite using `[hzx]`.

Conclude with `(e.continuousAt_symm (e.map_source hx)).preimage_mem_nhds (by rw [e.left_inv hx]; exact f.open_source.mem_nhds hxf)`. Establish `h2 : ∀ᶠ w in 𝓝 (z x), e'.symm w ∈ f.source`. Rewrite using `[hzx']`. Conclude with `(e'.continuousAt_symm (e'.map_source hx')).preimage_mem_nhds (by rw [e'.left_inv hx']; exact f.open_source.mem_nhds hxf)`. Establish `h3 : ∀ᶠ w in 𝓝 (z x), w ∈ e.target`.

Rewrite using `[hzx]`. Conclude with `e.open_target.mem_nhds (e.map_source hx)`. Establish `h4 : ∀ᶠ w in 𝓝 (z x), w ∈ e'.target`. Rewrite using `[hzx']`. Conclude with `e'.open_target.mem_nhds (e'.map_source hx')`.

Use `filter_upwards [h1, h2, h3, h4] with w hw1 hw2 hw3 hw4`. Establish `k1 : f (e.symm w) = w` using `by rw [← hzf, he (e.map_target hw3), e.right_inv hw3]`. Establish `k2 : f (e'.symm w) = w` using `by rw [← hzf, he' (e'.map_target hw4), e'.right_inv hw4]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem chart_symm_apply_eventually_eq {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n}
    (hz : IsLocalHomeomorph z) {e e' : OpenPartialHomeomorph M (V n)} (he : IsChart n z e)
    (he' : IsChart n z e') {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    ∀ᶠ w in 𝓝 (z x), e.symm w = e'.symm w := by
  obtain ⟨f, hxf, hzf⟩ := hz x
  have hzx : z x = e x := he hx
  have hzx' : z x = e' x := he' hx'
  have h1 : ∀ᶠ w in 𝓝 (z x), e.symm w ∈ f.source := by
    rw [hzx]
    exact (e.continuousAt_symm (e.map_source hx)).preimage_mem_nhds
      (by rw [e.left_inv hx]; exact f.open_source.mem_nhds hxf)
  have h2 : ∀ᶠ w in 𝓝 (z x), e'.symm w ∈ f.source := by
    rw [hzx']
    exact (e'.continuousAt_symm (e'.map_source hx')).preimage_mem_nhds
      (by rw [e'.left_inv hx']; exact f.open_source.mem_nhds hxf)
  have h3 : ∀ᶠ w in 𝓝 (z x), w ∈ e.target := by
    rw [hzx]
    exact e.open_target.mem_nhds (e.map_source hx)
  have h4 : ∀ᶠ w in 𝓝 (z x), w ∈ e'.target := by
    rw [hzx']
    exact e'.open_target.mem_nhds (e'.map_source hx')
  filter_upwards [h1, h2, h3, h4] with w hw1 hw2 hw3 hw4
  have k1 : f (e.symm w) = w := by rw [← hzf, he (e.map_target hw3), e.right_inv hw3]
  have k2 : f (e'.symm w) = w := by rw [← hzf, he' (e'.map_target hw4), e'.right_inv hw4]
  calc e.symm w = f.symm (f (e.symm w)) := (f.left_inv hw1).symm
    _ = f.symm (f (e'.symm w)) := by rw [k1, k2]
    _ = e'.symm w := f.left_inv hw2

/- English proof (translation)
Establish `h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source` using `⟨e, he, hx⟩`. Unfold `d`. Rewrite using `[dif_pos h]`. Apply `wd_congr` to reduce the goal to its premises. Use `filter_upwards [chart_symm_apply_eventually_eq hz (Classical.choose_spec h).1 he (Classical.choose_spec h).2 hx] with w hw`.

Simplify using `only [Function.comp_apply, hw]`.
-/
private theorem d_eq_wd_of_isLocalHomeomorph_chart {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n}
    (hz : IsLocalHomeomorph z) {e : OpenPartialHomeomorph M (V n)} (he : IsChart n z e)
    {x : M} (hx : x ∈ e.source) (j : Fin n) (g : M → ℂ) :
    d n z j g x = wd n j (g ∘ e.symm) (z x) := by
  have h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := ⟨e, he, hx⟩
  unfold d
  rw [dif_pos h]
  apply wd_congr
  filter_upwards [chart_symm_apply_eventually_eq hz (Classical.choose_spec h).1 he (Classical.choose_spec h).2 hx]
    with w hw
  simp only [Function.comp_apply, hw]

/- English proof (translation)
Establish `h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source` using `⟨e, he, hx⟩`. Unfold `db`. Rewrite using `[dif_pos h]`. Apply `wdb_congr` to reduce the goal to its premises. Use `filter_upwards [chart_symm_apply_eventually_eq hz (Classical.choose_spec h).1 he (Classical.choose_spec h).2 hx] with w hw`.

Simplify using `only [Function.comp_apply, hw]`.
-/
private theorem db_eq_wdb_of_isLocalHomeomorph_chart {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n}
    (hz : IsLocalHomeomorph z) {e : OpenPartialHomeomorph M (V n)} (he : IsChart n z e)
    {x : M} (hx : x ∈ e.source) (j : Fin n) (g : M → ℂ) :
    db n z j g x = wdb n j (g ∘ e.symm) (z x) := by
  have h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := ⟨e, he, hx⟩
  unfold db
  rw [dif_pos h]
  apply wdb_congr
  filter_upwards [chart_symm_apply_eventually_eq hz (Classical.choose_spec h).1 he (Classical.choose_spec h).2 hx]
    with w hw
  simp only [Function.comp_apply, hw]

/- English proof (translation)
Unfold `Levi leviV`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `hzx : z x = e x` using `he hx`. Establish `hnh : ∀ᶠ w in 𝓝 (z x), w ∈ e.target`. Rewrite using `[hzx]`.

Conclude with `e.open_target.mem_nhds (e.map_source hx)`. Establish `hev : (db n z k fun y => (ph y : ℂ)) ∘ e.symm =ᶠ[𝓝 (z x)] wdb n k (fun y => ((ph (e.symm y) : ℝ) : ℂ))` using `by filter_upwards [hnh] with w hw`. Rewrite using `[Function.comp_apply, db_eq_wdb_of_isLocalHomeomorph_chart hz he (e.map_target hw) k, he (e.map_target hw), e.right_inv hw]`. Apply the tactic sequence `try rfl`. Rewrite using `[d_eq_wd_of_isLocalHomeomorph_chart hz he hx, wd_congr hev]`.
-/
private theorem levi_eq_leviV_comp_chart_symm {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n}
    (hz : IsLocalHomeomorph z) {e : OpenPartialHomeomorph M (V n)} (he : IsChart n z e)
    {x : M} (hx : x ∈ e.source) (ph : M → ℝ) (ξ : Fin n → ℂ) :
    Levi n z ph x ξ = leviV n (fun y => ((ph (e.symm y) : ℝ) : ℂ)) (z x) ξ := by
  unfold Levi leviV
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have hzx : z x = e x := he hx
  have hnh : ∀ᶠ w in 𝓝 (z x), w ∈ e.target := by
    rw [hzx]
    exact e.open_target.mem_nhds (e.map_source hx)
  have hev : (db n z k fun y => (ph y : ℂ)) ∘ e.symm =ᶠ[𝓝 (z x)]
      wdb n k (fun y => ((ph (e.symm y) : ℝ) : ℂ)) := by
    filter_upwards [hnh] with w hw
    rw [Function.comp_apply, db_eq_wdb_of_isLocalHomeomorph_chart hz he (e.map_target hw) k, he (e.map_target hw),
      e.right_inv hw]
    try rfl
  rw [d_eq_wd_of_isLocalHomeomorph_chart hz he hx, wd_congr hev]

/- English proof (translation)
Introduce `z hz p q ph g hph hL hg hpos`. Establish `hchart : ∀ x : M, ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source`. Introduce `x`. Take `⟨f, hxf, hzf⟩` from `hz x`. Conclude with `⟨f, fun y _ => by rw [hzf], hxf⟩`.

Establish `hsm : ∀ e : OpenPartialHomeomorph M (V n), IsChart n z e → ContDiffOn ℝ ∞ (fun v => Real.log (∑ i, Real.exp (ph i (e.symm v)) + ∑ j, ‖g j (e.symm v)‖ ^ 2)) e.target`. Introduce `e he`. Establish `h1 : ∀ i, ContDiffOn ℝ ∞ (fun v => ph i (e.symm v)) e.target` using `fun i => (lse_smoothR_iff_real n z (ph i)).mp (hph i) e he`. Establish `h2 : ∀ j, ContDiffOn ℝ ∞ (fun v => g j (e.symm v)) e.target` using `fun j => by`. Establish `hgd : DifferentiableOn ℂ (fun v => g j (e.symm v)) e.target` using `hg j e he`.

Establish `hgc : ContDiffOn ℂ ∞ (fun v => g j (e.symm v)) e.target`. Conclude with `C.holo_contDiffOn_complex e.open_target hgd`. Conclude with `hgc.restrict_scalars ℝ`. Use `ContDiffOn.log ?_ fun v _ => (hpos (e.symm v)).ne'` and prove the remaining obligations. Conclude with `(ContDiffOn.sum fun i _ => (h1 i).exp).add (ContDiffOn.sum fun j _ => (h2 j).norm_sq ℝ)`.

Use `⟨(lse_smoothR_iff_real n z _).mpr fun e he => hsm e he, fun x ξ => ?_⟩` and prove the remaining obligations. Take `⟨e, he, hx⟩` from `hchart x`. Rewrite using `[levi_eq_leviV_comp_chart_symm hz he hx]`. Use `set u : Fin (p + q) → V n → ℝ := fun i => Fin.addCases (fun i y => Real.exp (ph i (e.symm y))) (fun j y => ‖g j (e.symm y)‖ ^ 2) i with hu`. Establish `hsum : ∀ y, ∑ i, u i y = ∑ i, Real.exp (ph i (e.symm y)) + ∑ j, ‖g j (e.symm y)‖ ^ 2`.

Introduce `y`. Rewrite using `[Fin.sum_univ_add]`. Simplify using `[hu]`. Establish `hzx : z x = e x` using `he hx`. Establish `hmem : z x ∈ e.target`.

Rewrite using `[hzx]`. Conclude with `e.map_source hx`. Establish `hA : ∀ i, (∃ φ : V n → ℝ, ContDiffOn ℝ 2 φ e.target ∧ LeviNonnegOn n φ e.target ∧ ∀ y ∈ e.target, u i y = Real.exp (φ y)) ∨ (∃ g' : V n → ℂ, ContDiffOn ℂ 2 g' e.target ∧ ∀ y ∈ e.target, u i y = Complex.normSq (g' y))`. Introduce `i`. Proceed by induction on `i using Fin.addCases with`.

Consider the case `left i => left`. Use `⟨fun y => ph i (e.symm y), ((lse_smoothR_iff_real n z (ph i)).mp (hph i) e he).of_le lse_two_le_infty, ?_, fun y _ => by simp [hu]⟩` and prove the remaining obligations. Introduce `y hy ζ`. Establish `h` using `hL i (e.symm y) ζ`. Rewrite `h` using `[levi_eq_leviV_comp_chart_symm hz he (e.map_target hy), he (e.map_target hy), e.right_inv hy]`.

Conclude with `h`. Consider the case `right j => right`. Establish `hgd : DifferentiableOn ℂ (fun v => g j (e.symm v)) e.target` using `hg j e he`. Establish `hgc : ContDiffOn ℂ 2 (fun v => g j (e.symm v)) e.target` using `(C.holo_contDiffOn_complex e.open_target hgd).of_le (by first`. Consider the case `exact WithTop.coe_le_coe.mpr le_top`.

Consider the case `exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)`. Consider the case `simp)`. Use `⟨fun y => g j (e.symm y), hgc, fun y _ => ?_⟩` and prove the remaining obligations. Simplify using `[hu, Complex.normSq_eq_norm_sq]`. Establish `hB : ∀ y ∈ e.target, 0 < ∑ i, u i y`.

Introduce `y _`. Rewrite using `[hsum]`. Conclude with `hpos (e.symm y)`. Establish `key` using `lseV n (p + q) e.target u e.open_target hA hB (z x) hmem ξ`. Establish `e1 : leviV n (fun y => ((Real.log (∑ i, u i y) : ℝ) : ℂ)) (z x) ξ = leviV n (fun y => ((Real.log (∑ i, Real.exp (ph i (e.symm y)) + ∑ j, ‖g j (e.symm y)‖ ^ 2) : ℝ) : ℂ)) (z x) ξ`.

Use `congr 1`. Use function extensionality and compare the values at `y`. Rewrite using `[hsum]`. Rewrite `key` using `[e1]`. Conclude with `key`.
-/
theorem lse (n : ℕ) (M : Type*) [TopologicalSpace M] : LSEStatement n M := by
  intro z hz p q ph g hph hL hg hpos
  have hchart : ∀ x : M, ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := by
    intro x
    obtain ⟨f, hxf, hzf⟩ := hz x
    exact ⟨f, fun y _ => by rw [hzf], hxf⟩
  have hsm : ∀ e : OpenPartialHomeomorph M (V n), IsChart n z e →
      ContDiffOn ℝ ∞ (fun v => Real.log (∑ i, Real.exp (ph i (e.symm v)) +
        ∑ j, ‖g j (e.symm v)‖ ^ 2)) e.target := by
    intro e he
    have h1 : ∀ i, ContDiffOn ℝ ∞ (fun v => ph i (e.symm v)) e.target :=
      fun i => (lse_smoothR_iff_real n z (ph i)).mp (hph i) e he
    have h2 : ∀ j, ContDiffOn ℝ ∞ (fun v => g j (e.symm v)) e.target :=
      fun j => by
        have hgd : DifferentiableOn ℂ (fun v => g j (e.symm v)) e.target := hg j e he
        have hgc : ContDiffOn ℂ ∞ (fun v => g j (e.symm v)) e.target := by
          exact C.holo_contDiffOn_complex e.open_target hgd
        exact hgc.restrict_scalars ℝ
    refine ContDiffOn.log ?_ fun v _ => (hpos (e.symm v)).ne'
    exact (ContDiffOn.sum fun i _ => (h1 i).exp).add (ContDiffOn.sum fun j _ => (h2 j).norm_sq ℝ)
  refine ⟨(lse_smoothR_iff_real n z _).mpr fun e he => hsm e he, fun x ξ => ?_⟩
  obtain ⟨e, he, hx⟩ := hchart x
  rw [levi_eq_leviV_comp_chart_symm hz he hx]
  set u : Fin (p + q) → V n → ℝ := fun i => Fin.addCases (fun i y => Real.exp (ph i (e.symm y)))
      (fun j y => ‖g j (e.symm y)‖ ^ 2) i with hu
  have hsum : ∀ y, ∑ i, u i y = ∑ i, Real.exp (ph i (e.symm y)) + ∑ j, ‖g j (e.symm y)‖ ^ 2 := by
    intro y
    rw [Fin.sum_univ_add]
    simp [hu]
  have hzx : z x = e x := he hx
  have hmem : z x ∈ e.target := by
    rw [hzx]
    exact e.map_source hx
  have hA : ∀ i, (∃ φ : V n → ℝ, ContDiffOn ℝ 2 φ e.target ∧ LeviNonnegOn n φ e.target ∧
        ∀ y ∈ e.target, u i y = Real.exp (φ y)) ∨
      (∃ g' : V n → ℂ, ContDiffOn ℂ 2 g' e.target ∧
        ∀ y ∈ e.target, u i y = Complex.normSq (g' y)) := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      left
      refine ⟨fun y => ph i (e.symm y),
        ((lse_smoothR_iff_real n z (ph i)).mp (hph i) e he).of_le lse_two_le_infty, ?_,
        fun y _ => by simp [hu]⟩
      intro y hy ζ
      have h := hL i (e.symm y) ζ
      rw [levi_eq_leviV_comp_chart_symm hz he (e.map_target hy), he (e.map_target hy), e.right_inv hy] at h
      exact h
    | right j =>
      right
      have hgd : DifferentiableOn ℂ (fun v => g j (e.symm v)) e.target := hg j e he
      have hgc : ContDiffOn ℂ 2 (fun v => g j (e.symm v)) e.target :=
        (C.holo_contDiffOn_complex e.open_target hgd).of_le (by
          first
          | exact WithTop.coe_le_coe.mpr le_top
          | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
          | simp)
      refine ⟨fun y => g j (e.symm y), hgc, fun y _ => ?_⟩
      simp [hu, Complex.normSq_eq_norm_sq]
  have hB : ∀ y ∈ e.target, 0 < ∑ i, u i y := by
    intro y _
    rw [hsum]
    exact hpos (e.symm y)
  have key := lseV n (p + q) e.target u e.open_target hA hB (z x) hmem ξ
  have e1 : leviV n (fun y => ((Real.log (∑ i, u i y) : ℝ) : ℂ)) (z x) ξ =
      leviV n (fun y => ((Real.log (∑ i, Real.exp (ph i (e.symm y)) +
        ∑ j, ‖g j (e.symm y)‖ ^ 2) : ℝ) : ℂ)) (z x) ξ := by
    congr 1
    funext y
    rw [hsum]
  rw [e1] at key
  exact key

end ReciprocityTheory.L2DbarEstimates
