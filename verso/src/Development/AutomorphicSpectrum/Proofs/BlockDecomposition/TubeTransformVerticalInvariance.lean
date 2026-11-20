import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContourShiftGaussianDecayStatement

noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

/- English proof (translation)
Establish `h : (fun y : ℝ => (⟨x, y⟩ : ℂ)) = fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I`. Use extensionality with `y`. Apply the tactic sequence `apply Complex.ext <;> simp`. Rewrite using `[h]`. Use `fun_prop`.
-/
theorem continuous_mk_im_shiftSnd (x : ℝ) : Continuous fun y : ℝ => (⟨x, y⟩ : ℂ) := by
  have h : (fun y : ℝ => (⟨x, y⟩ : ℂ)) = fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
    ext y
    apply Complex.ext <;> simp
  rw [h]
  fun_prop

/- English proof (translation)
Unfold `pt`. Conclude with `((continuous_mk_im_shiftSnd x.1).comp continuous_fst).prodMk ((continuous_mk_im_shiftSnd x.2).comp continuous_snd)`.
-/
theorem continuous_pt_shiftSnd (x : ℝ × ℝ) : Continuous fun y : ℝ × ℝ => pt x y := by
  unfold pt
  exact ((continuous_mk_im_shiftSnd x.1).comp continuous_fst).prodMk ((continuous_mk_im_shiftSnd x.2).comp continuous_snd)

/- English proof (translation)
Establish `h1 : Integrable fun x : ℝ => Real.exp (-1 * x ^ 2)` using `integrable_exp_neg_mul_sq one_pos`. Establish `h2` using `(h1.mul_prod h1).const_mul K`. Rewrite using `[Measure.volume_eq_prod]`. Use `h2.congr (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[← Real.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integrable_gauss_prod_shiftSnd (K : ℝ) :
    Integrable fun y : ℝ × ℝ => K * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)) := by
  have h1 : Integrable fun x : ℝ => Real.exp (-1 * x ^ 2) := integrable_exp_neg_mul_sq one_pos
  have h2 := (h1.mul_prod h1).const_mul K
  rw [Measure.volume_eq_prod]
  refine h2.congr (Eventually.of_forall fun y => ?_)
  simp only
  rw [← Real.exp_add]
  congr 2
  ring

/- English proof (translation)
Use `set C : Set (ℝ × ℝ) := (fun s : ℝ => (c, s)) '' Set.Icc a b with hC`. Establish `hCc : IsCompact C` using `isCompact_Icc.image (by fun_prop)`. Establish `hCΩ : C ⊆ Ω`. Introduce and unpack `_ ⟨s, hs', rfl⟩`. Conclude with `hs s hs'`.

Take `⟨M, hM⟩` from `hG.decay C hCΩ hCc`. Take `⟨B, hB⟩` from `(hCc.image (f := fun x : ℝ × ℝ => Real.exp (-(x.1 * t.1 + x.2 * t.2))) (by fun_prop)).bddAbove`. Set `H : ℂ × ℂ → X` to `fun l => Complex.exp (-dot l t) • G l`. Establish `hexp : Continuous fun l : ℂ × ℂ => Complex.exp (-dot l t)`. Unfold `dot`.

Use `fun_prop`. Establish `hbound : ∀ l ∈ tube C, ‖H l‖ ≤ (|B| * |M|) * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2))`. Introduce `l hl`. Establish `h1 : ‖Complex.exp (-dot l t)‖ ≤ |B|`. Rewrite using `[Complex.norm_exp]`.

Establish `h : (-dot l t).re = -(l.1.re * t.1 + l.2.re * t.2)` using `by simp [dot]`. Rewrite using `[h]`. Conclude with `(hB ⟨(l.1.re, l.2.re), hl, rfl⟩).trans (le_abs_self B)`. Establish `h2 : ‖G l‖ ≤ |M| * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2))` using `(hM l hl).trans (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hcont : ContinuousOn H (tube Ω)` using `hexp.continuousOn.smul hG.cont`. Establish `hmem : ∀ s ∈ Set.Icc a b, ∀ y : ℝ × ℝ, pt (c, s) y ∈ tube C` using `fun s hs' y => ⟨s, hs', rfl⟩`. Establish `hint : ∀ s ∈ Set.Icc a b, Integrable fun y : ℝ × ℝ => H (pt (c, s) y)`. Introduce `s hs'`. Establish `hc : Continuous fun y : ℝ × ℝ => H (pt (c, s) y)` using `hcont.comp_continuous (continuous_pt_shiftSnd _) fun y => hs s hs'`.

Use `(integrable_gauss_prod_shiftSnd (|B| * |M|)).mono' hc.aestronglyMeasurable (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Conclude with `hbound _ (hmem s hs' y)`. Establish `hphi : ∀ s ∈ Set.Icc a b, phi G (c, s) t = ∫ y₁ : ℝ, ∫ y₂ : ℝ, H (⟨c, y₁⟩, ⟨s, y₂⟩)`. Introduce `s hs'`. Establish `h` using `hint s hs'`.

Rewrite `h` using `[Measure.volume_eq_prod]`. Establish `h'` using `integral_prod _ h`. Rewrite `h'` using `[← Measure.volume_eq_prod]`. Conclude with `h'`. Rewrite using `[hphi a (Set.left_mem_Icc.2 hab), hphi b (Set.right_mem_Icc.2 hab)]`.

Use `integral_congr_ae (Eventually.of_forall fun y₁ => ?_)` and prove the remaining obligations. Simplify using `only`. Use `GlobalTheory.T.contour_shift_gaussian_decay X (fun z => H (⟨c, y₁⟩, z)) a b (|B| * |M|) hab ?_ ?_` and prove the remaining obligations. Set `p : ℂ × ℂ` to `(⟨c, y₁⟩, 0)`. Set `v : ℂ × ℂ` to `(0, 1)`.

Establish `e : ∀ τ : ℂ, p + τ • v = (⟨c, y₁⟩, τ)`. Introduce `τ`. Simplify using `[p, v]`. Establish `h1 : DifferentiableOn ℂ (fun τ : ℂ => G (⟨c, y₁⟩, τ)) {z : ℂ | z.re ∈ Set.Icc a b}`. Establish `h` using `hG.hol p v`.

Simplify using `only [e] at h`. Conclude with `h.mono fun z hz => hs _ hz`. Establish `h2 : Differentiable ℂ fun τ : ℂ => Complex.exp (-dot ((⟨c, y₁⟩, τ) : ℂ × ℂ) t)`. Unfold `dot`. Use `fun_prop`.

Conclude with `h2.differentiableOn.smul h1`. Introduce `z hz`. Establish `h` using `hbound (⟨c, y₁⟩, z) ⟨z.re, hz, rfl⟩`. Use `h.trans ?_` and prove the remaining obligations. Establish `hK : 0 ≤ |B| * |M|` using `by positivity`.

Use `mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK` and prove the remaining obligations. Establish `: 0 ≤ y₁ ^ 2` using `sq_nonneg _`. Simplify using `only`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem phi_shift_snd (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ))
    (G : ℂ × ℂ → X) (hG : GaussTube G Ω) (a b c : ℝ) (hab : a ≤ b) (hs : ∀ s ∈ Set.Icc a b, (c, s) ∈ Ω)
    (t : ℝ × ℝ) : phi G (c, a) t = phi G (c, b) t := by
  set C : Set (ℝ × ℝ) := (fun s : ℝ => (c, s)) '' Set.Icc a b with hC
  have hCc : IsCompact C := isCompact_Icc.image (by fun_prop)
  have hCΩ : C ⊆ Ω := by
    rintro _ ⟨s, hs', rfl⟩
    exact hs s hs'
  obtain ⟨M, hM⟩ := hG.decay C hCΩ hCc
  obtain ⟨B, hB⟩ := (hCc.image (f := fun x : ℝ × ℝ => Real.exp (-(x.1 * t.1 + x.2 * t.2)))
    (by fun_prop)).bddAbove
  let H : ℂ × ℂ → X := fun l => Complex.exp (-dot l t) • G l
  have hexp : Continuous fun l : ℂ × ℂ => Complex.exp (-dot l t) := by
    unfold dot
    fun_prop
  have hbound : ∀ l ∈ tube C, ‖H l‖ ≤ (|B| * |M|) * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by
    intro l hl
    have h1 : ‖Complex.exp (-dot l t)‖ ≤ |B| := by
      rw [Complex.norm_exp]
      have h : (-dot l t).re = -(l.1.re * t.1 + l.2.re * t.2) := by simp [dot]
      rw [h]
      exact (hB ⟨(l.1.re, l.2.re), hl, rfl⟩).trans (le_abs_self B)
    have h2 : ‖G l‖ ≤ |M| * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) :=
      (hM l hl).trans (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le)
    calc ‖H l‖ = ‖Complex.exp (-dot l t)‖ * ‖G l‖ := norm_smul _ _
      _ ≤ |B| * (|M| * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2))) := by gcongr
      _ = _ := by ring
  have hcont : ContinuousOn H (tube Ω) := hexp.continuousOn.smul hG.cont
  have hmem : ∀ s ∈ Set.Icc a b, ∀ y : ℝ × ℝ, pt (c, s) y ∈ tube C := fun s hs' y => ⟨s, hs', rfl⟩
  have hint : ∀ s ∈ Set.Icc a b, Integrable fun y : ℝ × ℝ => H (pt (c, s) y) := by
    intro s hs'
    have hc : Continuous fun y : ℝ × ℝ => H (pt (c, s) y) :=
      hcont.comp_continuous (continuous_pt_shiftSnd _) fun y => hs s hs'
    refine (integrable_gauss_prod_shiftSnd (|B| * |M|)).mono' hc.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    exact hbound _ (hmem s hs' y)
  have hphi : ∀ s ∈ Set.Icc a b, phi G (c, s) t = ∫ y₁ : ℝ, ∫ y₂ : ℝ, H (⟨c, y₁⟩, ⟨s, y₂⟩) := by
    intro s hs'
    have h := hint s hs'
    rw [Measure.volume_eq_prod] at h
    have h' := integral_prod _ h
    rw [← Measure.volume_eq_prod] at h'
    exact h'
  rw [hphi a (Set.left_mem_Icc.2 hab), hphi b (Set.right_mem_Icc.2 hab)]
  refine integral_congr_ae (Eventually.of_forall fun y₁ => ?_)
  simp only
  refine GlobalTheory.T.contour_shift_gaussian_decay X (fun z => H (⟨c, y₁⟩, z)) a b (|B| * |M|) hab ?_ ?_
  · let p : ℂ × ℂ := (⟨c, y₁⟩, 0)
    let v : ℂ × ℂ := (0, 1)
    have e : ∀ τ : ℂ, p + τ • v = (⟨c, y₁⟩, τ) := by
      intro τ
      simp [p, v]
    have h1 : DifferentiableOn ℂ (fun τ : ℂ => G (⟨c, y₁⟩, τ)) {z : ℂ | z.re ∈ Set.Icc a b} := by
      have h := hG.hol p v
      simp only [e] at h
      exact h.mono fun z hz => hs _ hz
    have h2 : Differentiable ℂ fun τ : ℂ => Complex.exp (-dot ((⟨c, y₁⟩, τ) : ℂ × ℂ) t) := by
      unfold dot
      fun_prop
    exact h2.differentiableOn.smul h1
  · intro z hz
    have h := hbound (⟨c, y₁⟩, z) ⟨z.re, hz, rfl⟩
    refine h.trans ?_
    have hK : 0 ≤ |B| * |M| := by positivity
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK
    have : 0 ≤ y₁ ^ 2 := sq_nonneg _
    simp only
    linarith

end GlobalTheory.CompanionTheory.TubeFourier
